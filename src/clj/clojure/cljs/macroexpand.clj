;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Macroexpansion across the two worlds.

  A ClojureScript macro is an ordinary Clojure macro: a Var in a real JVM
  namespace, whose function runs at compile time and returns ClojureScript. So
  expansion asks two different worlds two different questions - which macro does
  this symbol name here (the macro-side view of the current ClojureScript
  namespace) and, once found, just call it (the JVM).

  Follows cljs.analyzer/macroexpand-1* (analyzer.cljc:4273) and get-expander*
  (:4203), which is the contract the M2 AST-diff oracle will be checked against.
  Two deliberate departures, both noted at their site below: no *ns* rebinding
  and no js* :js-op tagging.

  See doc/cljs-compiler.md M1."}
  clojure.cljs.macroexpand
  (:refer-clojure :exclude [macroexpand macroexpand-1])
  (:require [clojure.cljs.env :as env]
            [clojure.edn :as edn]
            [clojure.java.io :as io])
  (:import [clojure.lang Namespace NamespaceWorld Symbol Var]
           [java.io File]))

(def specials
  "cljs.analyzer/specials. A special form is never a macro call, whatever the
  symbol happens to name."
  '#{if def fn* do let* loop* letfn* throw try recur new set! ns deftype*
     defrecord* . js* & quote case* var ns*})

;; --- finding the macro -----------------------------------------------------

(defn- rewrite-ns
  [cenv sym]
  (get (:macro-ns-rewrites cenv) sym sym))

(defn- macro-namespace
  "The JVM namespace named by the namespace part of a qualified symbol, as seen
  from the current ClojureScript namespace. cljs.analyzer/get-expander-ns."
  ^Namespace [cenv nsym]
  (let [^Namespace view (env/macro-view cenv)
        ^Namespace cns  (.find ^NamespaceWorld (:world cenv) env/*current-ns*)]
    (or
     ;; (:require-macros [foo.macros :as m]) - the alias already names a JVM ns.
     ;;
     ;; REWRITTEN LIKE ANY OTHER NAME, which is the whole reason this branch takes
     ;; the alias apart again instead of returning it. get-expander-ns resolves an
     ;; alias to a NAME first and rewrites that, so (:require-macros [clojure.core
     ;; :as lang]) makes lang/for the cljs.core macro even though the alias itself
     ;; points at the JVM clojure.core - and cljs/ns_test.cljs writes exactly that
     ;; and expects (lang/for [x (range 5)] x) to be a seq. Without it clojure.core's
     ;; own `for` expands, and its expansion calls .nth on a cljs collection.
     ;;
     ;; A :REFER OFF THE SAME SPEC IS NOT REWRITTEN, which is not an oversight but
     ;; the same rule read the other way: only the namespace PART of a qualified
     ;; symbol goes through this, so :refer [when] off clojure.core refers the JVM
     ;; clojure.core/when, as it does in ClojureScript (get-expander* reaches
     ;; :rename-macros and :use-macros without consulting get-expander-ns).
     (some-> (.lookupAlias view nsym) .getName (->> (rewrite-ns cenv)) find-ns)
     ;; a runtime alias, whose target namespace may also carry macros of the same
     ;; name: (:require [foo :as f]) then (f/some-macro ...)
     (some-> cns (.lookupAlias nsym) .getName (->> (rewrite-ns cenv)) find-ns)
     ;; written out in full
     (find-ns (rewrite-ns cenv nsym)))))

(defn macro-var
  "The Var to expand `sym` with in `env`, or nil if it names no macro here.

  Locals hide macros, so this consults `env`, not only the worlds. So does
  (:refer-clojure :exclude [...]), which the ns form records and which suppresses
  the core fallback below for the names it lists - the only thing it can affect
  until cljs.core is vendored and core vars exist to be hidden as well."
  ^Var [cenv env sym]
  (when-not (contains? (:locals env) sym)
    (let [v (if-let [nsym (some-> (namespace sym) symbol)]
              (when-let [^Namespace mns (macro-namespace cenv nsym)]
                (.findInternedVar mns (symbol (name sym))))
              (or
               ;; (:refer-macros [...]) / :use-macros / :rename-macros
               (let [m (.getMapping (env/macro-view cenv) sym)]
                 (when (instance? Var m) m))
               ;; anything else unqualified falls through to the core macros,
               ;; unless this namespace excluded the name
               (when-not (env/excluded? cenv env/*current-ns* sym)
                 (when-let [^Namespace cns (some-> (:core-macros cenv) find-ns)]
                   (.findInternedVar cns sym)))))]
      (when (and v (.isMacro ^Var v))
        v))))

;; --- expanding -------------------------------------------------------------

(defn- host-sugar
  "(.foo x a) => (. x foo a), (Foo. a) => (new Foo a). Not macroexpansion, but
  cljs.analyzer does it here and the shapes have to match for the M2 oracle."
  [form op]
  (let [s (str op)]
    (cond
      (.startsWith s ".")
      (let [[target & args] (next form)]
        (with-meta (list* '. target (symbol (subs s 1)) args) (meta form)))

      ;; The type symbol remembers where `Foo.` was written, less the dot, under
      ;; ::written and NOT as :line. Without it the symbol reads as one a macro made
      ;; up, and clojure.cljs.analysis records a use of Foo only where the source
      ;; wrote one. As :line it would be a position like any other, and
      ;; clojure.cljs.source-info would move the constructor's source-map column
      ;; from the paren to the name - which repl-test pins, and which is a change
      ;; to what a stack frame says rather than to what analysis sees.
      (and (.endsWith s ".") (> (count s) 1))
      (let [m (meta op)]
        (with-meta (list* 'new
                          (cond-> (symbol (subs s 0 (dec (count s))))
                            (:line m)
                            (with-meta {::written
                                        (cond-> (select-keys m [:line :column :end-line :end-column])
                                          (:end-column m) (update :end-column dec))}))
                          (next form))
          (meta form)))

      :else form)))

(def ^:private upstream-compiler-var
  "ClojureScript's own `cljs.env/*compiler*`, if the ClojureScript jar is on this
  classpath, and nil if it is not.

  RESOLVED RATHER THAN REQUIRED, because org.clojure/clojurescript is a TEST
  dependency here (pom.xml) - the vendored suite is the oracle, and nothing in
  src/clj may depend on it. Resolving also says the right thing: the var is bound
  for the benefit of somebody else's macro that calls upstream's analyzer, and no
  such macro can be on a classpath that has no upstream analyzer on it either."
  (delay (try (require 'cljs.env)
              (resolve 'cljs.env/*compiler*)
              (catch Throwable _ nil))))

;; --- the other build tool's module map ---------------------------------------

;; shadow-cljs splits one source tree into several output modules and loads them
;; on demand, and shadow.lazy/loadable is the macro a program writes to say `this
;; component comes later`. It expands by asking the compiler-state atom which
;; module a namespace is part of:
;;
;;     (defn module-for-ns [compiler-env ns]
;;       (get-in compiler-env [:shadow.build/ns->mod ns]))
;;
;;     (defn module-for-ns! [env ns]
;;       (let [mod (module-for-ns @env/*compiler* ns)]
;;         (when-not mod
;;           (throw (ana/error env (str "Could not find module for ns: " ns))))
;;         mod))
;;
;; and with nothing under that key the throw is unconditional. It is not a failure
;; of analysis - the form is fine and we understand it - it is a question about a
;; build, asked of a compiler that is not running one.
;;
;; THE ANSWER IS WRITTEN DOWN ALREADY, and that is why this is small. A module is
;; named by its ENTRY namespaces in shadow-cljs.edn:
;;
;;     :modules {:editor {:entries [nosco.richtext.editor] :depends-on #{:main}}}
;;
;; and an entry is exactly the kind of namespace loadable is given, because naming
;; a module by its entry point is what code-splitting is. So the map shadow would
;; have computed is not needed; the part of it anyone asks for is stated in the
;; configuration, and reading it is not a guess.
;;
;; WHERE IT STOPS is a namespace that is not an entry. Which module shadow puts one
;; of those in is decided by walking the dependency graph against the module tree,
;; and that is a build's work and a build's alone. Such a namespace is absent here,
;; module-for-ns! throws exactly what it threw before, and the refusal sits where
;; the knowledge actually runs out rather than one step past it.
;;
;; AND WHO STILL ASKS, which is worth saying now that the answer has changed for
;; the caller this was written for. shadow.lazy's own macro cannot load under this
;; compiler at all - it requires cljs.compiler as well as cljs.analyzer - so a
;; project running here supplies its own, and a lazy loader written against THIS
;; runtime has no modules to ask about: every namespace is already its own ES
;; module and $CLJS.require fetches one by name (5.67). So this answers a question
;; that a macro of shadow's would ask and the one macro anybody replaced it with
;; does not. It stays because it is the right answer for any OTHER macro reading
;; that key, and because being wrong about which macros exist is exactly the kind
;; of guess the section above declines to make.
;;
;; See doc/cljs-compiler.md 5.58 and 5.67.

(def ^:dynamic *shadow-cljs-edn*
  "shadow-cljs's configuration file.

  RELATIVE, AND THAT IS SHADOW'S OWN RULE RATHER THAN A CHOICE OF OURS.
  shadow.cljs.devtools.config/load-cljs-edn is literally (io/file
  \"shadow-cljs.edn\"): the project directory is whichever directory the JVM was
  started in, which is why the shadow-cljs command line insists on being run from
  the project root. A java.io.File holding a relative path resolves it when it is
  read and not when it is made, so this stays a question and does not become an
  answer at load time.

  A REPL started somewhere else finds no file and this answers nothing, which is
  the truth about that REPL and not a fallback worth inventing around.

  Dynamic so a test can point it at a fixture."
  (io/file "shadow-cljs.edn"))

(def shadow-build
  "Which build's :modules are read.

  THE ONE THING THAT CANNOT BE DERIVED, so it is written down instead. A
  shadow-cljs.edn holds several builds; each splits the same source tree its own
  way, and one namespace can be an entry of differently named modules in two of
  them - nosco-gamma's richtext editor is :editor in the :main build and :trial in
  the :trial build. A shadow build knows which one it is because it was started as
  one. This compiler was not started as any, and there is no fact anywhere in the
  world it holds that would settle it, so guessing would be picking one build's
  answer and presenting it as the truth about all of them."
  :main)

(defn- shadow-modules
  "[:builds <shadow-build> :modules] out of the configuration file, or nil.

  EVERY TAG IS DROPPED, its value kept. shadow reads this file with readers for
  #shadow/env and #env, which look up environment variables - nosco-gamma spells
  an :asset-path that way. We read one vector of symbols out of the whole file and
  a symbol carries no tag, so the tags we meet are always somebody else's
  configuration on the way past, and the cheapest correct thing to do with a value
  we will never look at is to stop it from throwing."
  []
  (let [^File f *shadow-cljs-edn*]
    (when (and f (.exists f))
      (-> (edn/read-string {:default (fn [_tag value] value)} (slurp f))
          (get-in [:builds shadow-build :modules])))))

(defn shadow-ns->mod
  "What upstream's atom answers under :shadow.build/ns->mod.

  A VIEW, for the reason clojure.cljs.env/upstream-namespaces is one: the file is
  read when a lookup happens rather than when this is made. A REPL outlives an
  edit to shadow-cljs.edn - adding a module is how you make a component lazy - and
  a map built once would go on answering what the file used to say. The cost is a
  slurp of a few kilobytes per loadable in a compilation unit, and there are six
  in the whole of nosco-gamma.

  ILookup AND NOTHING ELSE, because one get-in is the whole of what reads it.
  5.57 grew its view twice at runtime by guessing at the shape first; this one
  waits to be asked."
  []
  (reify
    clojure.lang.ILookup
    (valAt [this k] (.valAt this k nil))
    (valAt [_ k nf]
      (or (some (fn [[mod-id {:keys [entries]}]]
                  (when (some #(= k %) entries) mod-id))
                (shadow-modules))
          nf))))

(def ^:private upstream-compiler-state
  "What `cljs.env/*compiler*` derefs to while a macro of ours runs.

  A CONSTANT, and that is the whole point. The three things upstream's macro
  lookup reads through that atom on the JVM path are

    ::namespaces <ns> :excludes    - excluded?  (analyzer.cljc:4176)
    ::namespaces <ns> :use-macros  - used?      (analyzer.cljc:4182)
    :options :spec-skip-macros     - do-macroexpand-check

  and the first two are asked of the ANALYSIS ENV FIRST, with this only as the
  fallback:

      (defn excluded? [env sym]
        (or (some? (gets env :ns :excludes sym))                      ; <- ours
            (some? (gets @env/*compiler* ::namespaces ... :excludes sym))))

  So the facts go where upstream asks for them first - env/analysis-env - and what
  is left here is a constant. That is the ORDER of the design and not a detail of
  it. The other way round is the trap: binding an atom and stopping there makes
  `go` compile without giving &env anything, and then `excluded?` answers `nothing
  is excluded` for every namespace, so a core MACRO an ns form excluded goes on
  expanding over the top of the var the program defined instead. Run end to end
  that prints `Elapsed time: 0.027292 msecs` where the program said `mine:3` -
  the same shape of bug as the one 5.55 exists to fix, and not a trade worth
  making.

  :spec-skip-macros is a DECISION rather than a default: clojure.spec's macro
  instrumentation is not something this compiler runs, so it is skipped by saying
  so rather than by happening not to be configured.

  STILL A CONSTANT AFTER 5.57, which added the entry that is not one. `::namespaces`
  answers for whichever compile environment is bound when it is asked, so there is
  one of these for the whole compiler rather than one per macroexpansion - see
  clojure.cljs.env/upstream-namespaces. The reason it had to be added at all is the
  reason 5.55 gave for leaving it empty, read backwards: excluded? and used? ask
  &env first, but cljs.analyzer.api does not ask &env at all. It is a facade over
  this atom, and a macro that calls it - sci's protocol-vars, asking whether
  cljs.core/ICloneable is a protocol - has no other road in.

  AND STILL A CONSTANT AFTER 5.58, which added a second entry that is not one,
  and not even upstream's: :shadow.build/ns->mod, which shadow-cljs's own macros
  read through upstream's var. The two views differ in what they read - one the
  compile environment bound around this call, the other a file on disk - and
  agree in why they are views: neither fact can be frozen at the moment this atom
  is made without a REPL going on to answer from the past."
  (atom {:options    {:spec-skip-macros true}
         ;; spelled out rather than ::-resolved: this is cljs.analyzer's keyword,
         ;; and cljs.analyzer is not required here (see upstream-compiler-var)
         :cljs.analyzer/namespaces (env/upstream-namespaces)
         ;; not cljs.analyzer's key at all but shadow-cljs's, and here for the
         ;; same reason: a macro reads it through this atom and has no other road
         ;; in. See shadow-ns->mod above.
         :shadow.build/ns->mod (shadow-ns->mod)}))

(def ^:dynamic *on-expand*
  "nil, or a function of the macro Var, the symbol that named it and the form,
  called just before each macro this namespace expands. clojure.cljs.analysis binds
  it: every expansion is a compile-time dependency of the form being compiled on the
  macro, a call whose symbol the source wrote is a use of it, and the form of a
  (comment ...) is the only sight anything gets of its body.

  A hook here and not a node in the AST, because the AST has nothing left to hold
  it by: the call is replaced by its expansion before any node is built."
  nil)

(def ^:dynamic *on-destructured-keyword*
  "nil, or a function of a keyword and the symbol a :keys destructuring wrote it
  as - {:keys [id]} names :id by the local id - called from cljs.core/destructure
  as it builds the keyword. clojure.cljs.analysis binds it: that is a use of the
  keyword, where the local is written, and the expansion keeps no trace of which
  symbol it was built from. *on-protocol-impl*'s reason, for a keyword."
  nil)

(def ^:dynamic *on-protocol-impl*
  "nil, or a function of the protocol's qualified name and the symbol that named
  it, called for each protocol a `deftype', `defrecord', `reify', `specify!' or
  `extend-type' implements - from cljs.core/update-protocol-var, which is where
  every one of those forms resolves the protocol it was given.
  clojure.cljs.analysis binds it: naming a protocol in an implementation is a use
  of it, and that is how where-is-this-protocol-implemented is answered.

  A hook here and not a node in the AST, for *on-expand*'s reason in its sharpest
  form. A ClojureScript protocol is not a var at run time but a munged property
  name, so implementing one compiles to

      (set! (.. Square -prototype -up$cutil$Shape) true)

  and the protocol's name is not in that form at all - it has become four
  characters of a property. Nothing the analyzer is handed remembers that the
  source wrote `Shape' there, and nothing could: the only moment the written
  symbol and the var it resolves to are both in hand is the moment the macro
  resolves it, which is this one.

  The written symbol is passed rather than a position because a protocol a MACRO
  names carries no reader position - `defrecord' extends fourteen of cljs.core's
  own - and what has no position was not written anywhere a person can be taken
  to. The analysis side drops those, the same way it drops a macro call nobody
  wrote."
  nil)

(defn macroexpand-1
  "Expand `form` once in `env`. Returns the form unchanged when there is nothing
  to expand - identical?, so callers can test for a fixed point.

  The macro is invoked exactly as Clojure invokes one: (apply @v form env args),
  so it receives &form and &env.

  One departure from cljs.analyzer remains: it tags a js* expansion with :js-op /
  ::numeric metadata for the emitter's operator inference, which has nothing to
  consume it yet.

  *NS* IS BOUND, AND TO THE MACRO VIEW. cljs.analyzer binds it to
  (create-ns *cljs-ns*), minting a JVM namespace named after a ClojureScript one,
  which is the collision NamespaceWorld exists to avoid - so this used to bind
  nothing, and a macro that asked (ns-name *ns*) got whoever happened to be
  compiling. The macro view answers the question that macro is really asking: it is
  a clojure.lang.Namespace, it is named after the ClojureScript namespace, and it
  already exists in a world of its own (doc/cljs-compiler.md 5.57). goog-define in
  our own core.cljc is the local reader - it munges the name of *ns* into the
  define it emits - and kitchen-async's fixup-alias is the one that made it
  necessary."
  [cenv env form]
  (if-not (seq? form)
    form
    (let [op (first form)]
      (cond
        (contains? specials op) form

        (symbol? op)
        (if-let [v (macro-var cenv env op)]
          (do
            (when-let [f *on-expand*] (f v op form))
            ;; the one place *cenv* is bound. A macro's parameters are &form and
            ;; &env, so a macro that has to resolve a ClojureScript symbol -
            ;; defprotocol and its family, which turn one into a property name -
            ;; has no way to be handed the compile environment explicitly.
            ;; and cljs.env/*compiler*, for a macro that calls UPSTREAM's analyzer
            ;; rather than being expanded by ours. core.async's go is the case: it
            ;; walks its own body to build a state machine, and walking means
            ;; macroexpanding, so ioc_macros.clj:728 calls cljs.analyzer/macroexpand-1
            ;; - which derefs that var and, unbound, throws a NullPointerException
            ;; out of deref-future. See upstream-compiler-state, and
            ;; doc/cljs-compiler.md 5.55.
            (with-bindings (cond-> {#'env/*cenv* cenv
                                    #'*ns* (env/macro-view cenv env/*current-ns*)}
                             @upstream-compiler-var
                             (assoc @upstream-compiler-var upstream-compiler-state))
              (apply @v form env (rest form))))
          (host-sugar form op))

        :else form))))

(defn macroexpand
  "Expand `form` until it stops changing at the top level, as clojure.core's
  macroexpand does. `limit` guards a macro that expands to itself."
  ([cenv env form] (macroexpand cenv env form 100))
  ([cenv env form limit]
   (loop [form form n 0]
     (when (> n limit)
       (throw (ex-info (str "macroexpand did not reach a fixed point after " limit
                            " expansions")
                       {:form form})))
     (let [form' (macroexpand-1 cenv env form)]
       (if (identical? form form')
         form
         (recur form' (inc n)))))))
