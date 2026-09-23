(ns ^{:doc "cljs.analyzer.api, as much of it as anything here asks for.

  ClojureScript keeps two front doors onto its symbol table: cljs.analyzer, which
  is internal, and cljs.analyzer.api, which is the documented one. cljs/test.cljc
  goes through the second, and uses six of it - resolve, get-options, all-ns,
  find-ns, ns-resolve and ns-interns - so those six are the whole of what a
  vendored cljs.test needs that clojure.cljs.analyzer does not already give it.

  `current-file' is the seventh and `ns-publics' the eighth, and both are here for
  somebody else: src/compat publishes this namespace under ClojureScript's own
  name, and what comes through that door is a macro namespace asking where it is
  being expanded, or a sandbox asking what a namespace holds. `current-file' could
  not have come through the other one - a dynamic var cannot be forwarded, and a
  function that READS one can (see src/compat/cljs/analyzer/api.clj).

  A NAMESPACE OF ITS OWN because five of the eight are clojure.core names. Putting
  them beside resolve-var would shadow resolve, find-ns, ns-resolve, ns-interns and
  ns-publics inside the analyzer itself, which is a trap for a file that is 1,700
  lines of ordinary Clojure.

  ClojureScript's versions take an optional compiler-state first argument. Ours do
  not: the state is clojure.cljs.env/*cenv*, for the reason that namespace's
  docstring gives."}
  clojure.cljs.analyzer-api
  (:refer-clojure :exclude [all-ns find-ns ns-interns ns-publics ns-resolve resolve])
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.env :as env])
  (:import [clojure.lang Namespace Var]))

(defn current-file
  "The file being analysed, as a var's :file records it, or nil outside a file.

  clojure.cljs.analyzer/*source-file*, and A PATH UNDER A SOURCE DIRECTORY -
  my_lib/core.cljs - rather than one on this machine, which is that var's own
  rule and the one an editor can resolve. ClojureScript's answer here is
  whatever its driver was handed, which is an absolute path, so a caller that
  prints it will see a shorter string than it used to. NIL AT A REPL, where
  ClojureScript says \"NO_SOURCE_PATH\"."
  []
  ana/*source-file*)

(defn get-options
  "The compiler options in force. ClojureScript's build options map; ours is empty,
  because a CompileEnv holds no build options - the driver takes them per call.
  cljs.test reads :output-dir out of it and defaults to \"out\" when it is absent,
  which is the answer we want anyway."
  []
  {})

(defn all-ns
  "Every ClojureScript namespace that exists, as symbols."
  []
  (map #(.getName ^Namespace %) (env/all-cljs-ns env/*cenv*)))

(defn find-ns
  "The namespace `ns-sym` as a map, or nil. cljs.test only tests it for truth."
  [ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns env/*cenv* ns-sym)]
    {:name (.getName n)}))

(defn- var-info
  "A Var as the map cljs.analyzer.api answers with: its metadata, plus the three
  keys every caller reads first.

  THE METADATA IS THERE TWICE, flattened and again under :meta, and that is
  ClojureScript's shape rather than an accident of this one. Its parse-def merges
  `sym-meta` into the var map and then puts the same map under :meta beside it
  (analyzer.cljc:2050), so both spellings work upstream and a caller picks one.
  Both have a reader here: cljs.test reads :test and :line off the FLAT map, and
  sci.core/copy-ns reads (:meta var) and silently DROPS every entry that has none -
  its exclude-when-meta is an if-let over that key, so a var map without it is not
  copied rather than copied wrong. Copying nothing is what a sandbox got before
  this key was here, and the compile that produced it reported no error.

  THE NESTED COPY HAS TO BE READABLE, because copy-ns quotes it into the code it
  emits - (list 'quote m) - so anything in it that is not a constant is a constant
  the emitter is asked to build and cannot. Two keys are made safe, and only two,
  because a var's metadata is otherwise whatever the program wrote there and
  upstream carries that as-is:

    :test   dissoc'd, as upstream dissocs it. There the reason is an analysis
            cache that has to be valid EDN; here nothing is cached and the reason
            is the quote. The FLAT :test stays - it is the one cljs.test reads.
    :ns     a SYMBOL rather than the clojure.lang.Namespace that (meta v) holds.
            That object is ours rather than ClojureScript's: upstream's :meta is a
            symbol's metadata and never had one, ours is a real Var's and always
            does. The flat map already spells it as a symbol; this makes the two
            agree instead of one of them being unprintable."
  [^Var v]
  (when v
    (let [m  (meta v)
          ns (.getName (.ns v))]
      (assoc m
             :name (symbol (str ns) (str (.sym v)))
             :ns   ns
             ;; cljs.test asks :fn-var to tell a function from a macro before it
             ;; builds an assertion around a call to it
             :fn-var (boolean (:fn-var m))
             :meta (-> m (dissoc :test) (assoc :ns ns))))))

(defn ns-resolve
  "The var `sym` names in `ns-sym`, as a map, or nil. Interned only - what another
  namespace merely refers is not reachable through this one's name."
  [ns-sym sym]
  (some-> ^Namespace (env/find-cljs-ns env/*cenv* ns-sym)
          (.findInternedVar (symbol (name sym)))
          var-info))

(defn ns-interns
  "Every var interned in `ns-sym`, as {simple-symbol var-map}.

  THIS IS HOW cljs.test FINDS THE TESTS: test-all-vars-block asks for the interns,
  keeps the ones whose map has :test, and sorts them by :line - so both of those
  keys have to survive from the def that made the var to here, and both do,
  because a var map is its metadata."
  [ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns env/*cenv* ns-sym)]
    (into {} (keep (fn [[sym v]] (when (instance? Var v) [sym (var-info v)])))
          (.getMappings n))))

(defn ns-publics
  "The vars of `ns-sym` that another namespace may name, as {simple-symbol
  var-map}: `ns-interns` without the private ones.

  THE EIGHTH, and sci is what asked. sci.core/copy-ns lifts a namespace into a
  sandbox wholesale - nosco-gamma writes (sci/copy-ns cljs.math (create-ns
  'clojure.math)) so that surface code can call clojure.math/round - and the branch
  of that macro which runs inside the ClojureScript compiler reads its list through
  this name. The other seven are what cljs/test.cljc asks for; this one is for
  somebody else's library, as `current-file` is.

  THE DEFS AND NOT THE MACROS, which is where it parts company with
  ClojureScript's. Upstream merges a namespace's :macros over its :defs, because
  both are entries in one map there. Here they are not in the same world at all: a
  ClojureScript namespace is a clojure.lang.Namespace of ClojureScript vars, and
  its macros live in a JVM namespace reached through the macro view (see
  `macro-var` below), which is per-namespace-being-compiled rather than something
  this can be handed a name and asked about. Nor would a caller want one back:
  copy-ns builds a reference `(symbol ns-sym var-name)` for every entry, and a
  macro is a name with no JavaScript behind it.

  Private is read off the var's own metadata, which `var-info` carries whole - the
  same place (:private m) would be read from upstream's var map."
  [ns-sym]
  (into {} (remove (fn [[_ m]] (:private m))) (ns-interns ns-sym)))

(defn- macro-info
  [^Var v]
  {:name (symbol (str (.getName (.ns v))) (str (.sym v)))
   :ns   (.getName (.ns v))
   :macro true})

(defn- macro-var
  "The macro `sym` names in the macro view of the namespace being compiled, or nil.

  ALIAS THEN NAME for a qualified symbol, which is how every other qualified name
  in this compiler resolves and is what s/coll-of needs: cljs.spec-test writes
  (:require [cljs.spec.alpha :as s]) and then s/coll-of, so the prefix is an alias
  on the macro view rather than a namespace name. cljs.core/fn arrives as the name
  itself and is found by the second half."
  ^Var [sym]
  (when-let [cenv env/*cenv*]
    (let [^Namespace view (env/macro-view cenv)
          nm   (symbol (name sym))
          ;; clojure.core/find-ns, spelled out: find-ns and ns-interns above are
          ;; the CLOJURESCRIPT-world ones this namespace redefines, and a macro
          ;; namespace is a JVM one.
          m    (if-let [nsp (namespace sym)]
                 (let [nsp (symbol (if (= "clojure.core" nsp) "cljs.core" nsp))]
                   (some-> ^Namespace (or (.lookupAlias view nsp)
                                          (clojure.core/find-ns nsp))
                           (.findInternedVar nm)))
                 (.getMapping view nm))]
      (when (and (instance? Var m) (.isMacro ^Var m)) m))))

(defn resolve
  "The var `sym` names here, as a map, or NIL when there is none.

  Not clojure.cljs.analyzer/resolve-var, and the difference is the whole reason
  this one exists: that one synthesises a name for a var that is not there, on
  purpose (its docstring says why). cljs.analyzer.api's resolve asks with
  confirm-var-exists-throw and answers nil instead, and cljs.test depends on the
  nil - `(when (ana-api/resolve &env 'cljs-test-once-fixtures) ...)` is how it
  decides whether a namespace HAS fixtures, and a synthesised answer makes every
  namespace look as though it does.

  A MACRO RESOLVES TOO, after the var and never instead of one. cljs.analyzer.api
  falls back to resolve-macro-var for the same reason (api.cljc:211), and
  cljs.spec.alpha is what needs it: (s/form (s/coll-of int?)) records the resolved
  head of every predicate form, and `coll-of` is a macro - so without this the spec
  remembered a bare `coll-of` and (s/form ...) printed a name that resolves to
  nothing. The same goes for `fn` and `or` inside a (fn [%] ...) predicate.

  The macro VIEW is where a namespace's macros are visible (env/macro-view), and
  what is interned there is a JVM var whose namespace is the macro namespace.

  `env` is accepted and ignored, as it is throughout."
  [env sym]
  (or (ana/resolve-existing-var env sym)
      (some-> (macro-var sym) macro-info)))

