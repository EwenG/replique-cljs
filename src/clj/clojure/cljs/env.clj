;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The ClojureScript compilation environment: two worlds and a cursor.

  ClojureScript is compiled by two languages at once. Its vars are ClojureScript
  and exist only as a symbol table; its macros are Clojure functions that run, on
  the JVM, at compile time. A namespace therefore has two sets of requires, and a
  symbol means different things depending on which side is asking.

  So a compile environment is:

    :world        a NamespaceWorld of ClojureScript namespaces holding
                  root-unbound Vars - the target's symbol table
    :macro-world  a NamespaceWorld of per-ClojureScript-namespace *views* onto
                  the JVM: aliases point at real loaded clojure.lang.Namespace
                  objects (:require-macros) and mappings hold real macro Vars
                  (:refer-macros / :use-macros / :rename-macros)

  A world and nothing else. WHERE THE COMPILER IS STANDING is *current-ns*, a
  dynamic var rather than a field, so that one world can be shared by two REPLs
  that are in different namespaces - see that var.

  The macro world holds views, not namespaces of its own: nothing is ever interned
  into it, and every alias and mapping in it points into NamespaceWorld/DEFAULT,
  where macros actually live. That is the whole of the two-world arrangement -
  cljs.analyzer keeps the same information in nested maps under [::namespaces ns
  :require-macros], and resolves it against clojure.lang.Namespace at the end
  anyway (analyzer.cljc:4203, .findInternedVar on a JVM namespace).

  Populated here by hand. The (ns ...) special form owns this in the real front
  end, along with the rules that do not belong at this level - :refer-clojure
  :exclude, and the implicit \"a .cljs file may have a same-named .clj macro
  file\" self-require. See doc/cljs-compiler.md M3."}
  clojure.cljs.env
  (:import [clojure.lang Namespace NamespaceWorld Symbol Var]))

(def default-macro-ns-rewrites
  "Macro namespaces ClojureScript renames on the way through: clojure.core macros
  are cljs.core macros. Applied to the namespace part of a qualified symbol and to
  an alias's target, matching cljs.analyzer/get-expander-ns."
  '{clojure.core cljs.core
    clojure.repl cljs.repl})

(def ^:dynamic *current-ns*
  "The namespace being compiled, as a symbol - the cursor.

  A DYNAMIC VAR AND NOT A FIELD OF THE COMPILE ENVIRONMENT, which is
  cljs.analyzer/*cljs-ns* and is the one place this compiler does not thread its
  state explicitly. The reason is that a cursor is not a property of a symbol
  table: two REPLs attached to one program must agree about what is defined and
  must NOT agree about where the user is standing, and a world held by reference
  with a cursor held per scope is exactly that arrangement. cljs.env/*compiler*
  and cljs.analyzer/*cljs-ns* split the same way and for the same reason.

  Moved by set-current-ns!, which is a set! - so a scope that means to move it
  must first give itself a binding to move (with-current-ns). Every entry point
  that compiles anything does: the driver, so that compiling a file's (ns ...)
  does not move the caller; and the REPL loop, so that an (ns ...) typed at it
  does."
  'cljs.user)

(defmacro with-current-ns
  "Body with a cursor of its own, starting at `sym`. A set-current-ns! inside moves
  this binding and nothing outside it - which is both how a compilation borrows the
  cursor without stealing it, and how a REPL gets one it may keep."
  [sym & body]
  `(binding [*current-ns* ~sym] ~@body))

(defn set-current-ns!
  "Move the cursor. A driver calls this as it processes each (ns ...) form; the
  reader's resolver and macro lookup both read it per form.

  Throws if there is no binding to move - see *current-ns*."
  [sym]
  (set! *current-ns* sym)
  sym)

(defrecord CompileEnv [^NamespaceWorld world
                       ^NamespaceWorld macro-world
                       core-macros
                       macro-ns-rewrites])

(defn compile-env
  "A fresh compile environment.

    :ns                 namespace to start in, default 'cljs.user. Positioning is
                        set-current-ns!, not a field: the environment is the world
                        and the cursor is a binding (*current-ns*), so this needs
                        an enclosing with-current-ns and throws without one.
    :core-macros        namespace consulted for any unqualified macro not referred
                        in - ClojureScript's is cljs.core, and so is this default.
                        Loaded here, so a name that does not exist fails now rather
                        than as a silent non-expansion later. It defaulted to nil
                        while cljs.core was not vendored; since §5.12 every
                        namespace requires cljs.core, so every compilation compiles
                        it, and compiling it needs its own macros. Pass nil to opt
                        out - the analyzer's own tests do, to keep a form from
                        expanding out from under them.
    :macro-ns-rewrites  see default-macro-ns-rewrites"
  (^CompileEnv [] (compile-env nil))
  (^CompileEnv [{:keys [ns core-macros macro-ns-rewrites]
                 :or   {ns 'cljs.user
                        core-macros 'cljs.core
                        macro-ns-rewrites default-macro-ns-rewrites}}]
   (when core-macros
     (require core-macros))
   (set-current-ns! ns)
   (->CompileEnv (NamespaceWorld.) (NamespaceWorld.) core-macros macro-ns-rewrites)))

(defn cljs-ns
  "The ClojureScript namespace `sym`, created if absent. Its vars are
  root-unbound: a symbol table, never invoked."
  (^Namespace [^CompileEnv cenv] (cljs-ns cenv *current-ns*))
  (^Namespace [^CompileEnv cenv sym] (.findOrCreate ^NamespaceWorld (:world cenv) sym)))

(defn macro-view
  "The macro-side view of ClojureScript namespace `sym`, created if absent - what
  that namespace can see of the JVM."
  (^Namespace [^CompileEnv cenv] (macro-view cenv *current-ns*))
  (^Namespace [^CompileEnv cenv sym] (.findOrCreate ^NamespaceWorld (:macro-world cenv) sym)))

(defn macro-ns
  "The JVM namespace `jvm-ns`, loaded, with every name in `refers` checked to be a
  macro interned there. Throws otherwise, naming which name and why: a refer that
  does not resolve would otherwise fail silently, as a call that never expands.

  Separate from require-macros! below so that the ns form can VALIDATE a reference
  before it applies any of them - the two calls are the same work, and the work is
  idempotent, which is what makes checking twice cheaper than unwinding once."
  ^Namespace [jvm-ns refers]
  (require jvm-ns)
  (let [^Namespace jns (or (find-ns jvm-ns)
                           (throw (ex-info (str "No such macro namespace: " jvm-ns)
                                           {:ns jvm-ns})))]
    (doseq [sym refers]
      (let [v (.findInternedVar jns sym)]
        (when-not (and v (.isMacro ^Var v))
          (throw (ex-info (str jvm-ns "/" sym
                               (if v " is not a macro" " does not exist"))
                          {:ns jvm-ns :sym sym})))))
    jns))

(defn require-macros!
  "Make the JVM namespace `jvm-ns` visible as macros to ClojureScript namespace
  `ns-sym`, loading it first. `:as` adds an alias, `:refer` a collection of macro
  names to map directly, `:rename` a map of {from to} for a macro this namespace
  calls something else. What (:require-macros ...) and (:refer-macros ...) do -
  and what a :rename that turned out to name a macro does (see the analyzer's
  check-renames!)."
  [^CompileEnv cenv ns-sym jvm-ns & {:keys [as refer rename]}]
  (let [^Namespace view (macro-view cenv ns-sym)
        ^Namespace jns  (macro-ns jvm-ns (into (vec refer) (vals rename)))]
    (when as
      (.addAlias view (symbol (name as)) jns))
    (doseq [sym refer]
      (.refer view sym (.findInternedVar jns sym)))
    ;; the same mapping with the two names apart
    (doseq [[to from] rename]
      (.refer view to (.findInternedVar jns from)))
    ;; recorded for the same reason declared-requires is: a LATER namespace asks
    ;; what this one said about itself. See declared-macro-requires.
    (alter-meta! (cljs-ns cenv ns-sym) update ::macro-requires (fnil conj #{}) jvm-ns)
    view))

(defn refer-globals!
  "Record that `ns-sym` refers the JavaScript globals in `m`, a map from the name
  it uses to the js/ name it stands for.

  On the namespace rather than in the analysis env, because an env is built fresh
  per form (driver/compile-source!) and this has to outlive the ns form that
  declared it. cljs.analyzer keeps its :js-globals in the env and its
  :refer-global names in the namespace's :uses, which is the same split."
  [^CompileEnv cenv ns-sym m]
  (alter-meta! (cljs-ns cenv ns-sym) update ::global-refers merge m)
  m)

(defn global-refers
  "What `ns-sym` may write as a bare name and mean a JavaScript global."
  [^CompileEnv cenv ns-sym]
  (::global-refers (meta (cljs-ns cenv ns-sym)) {}))

(defn declared-macro-requires
  "The JVM namespaces `ns-sym`'s ns form reached for macros - what
  :require-macros, :use-macros, :refer-macros and :include-macros named.

  Read for one question, and it is worth naming: whether a namespace says its
  macros live in the JVM namespace OF ITS OWN NAME. A .cljc that is both a runtime
  namespace and a macro namespace declares that by requiring itself, as cljs.test
  does - and a namespace that requires cljs.test may then :refer a macro from it
  without saying :refer-macros (doc/cljs-compiler.md 5.17).

  cljs.analyzer answers the same question with macro-autoload-ns?, which falls back
  to reading the ns form off disk when the namespace has not been analysed. There
  is no fallback here and none is needed: the driver compiles what a namespace
  requires before the namespace itself, so a required namespace has always been
  analysed by the time this is asked."
  [^CompileEnv cenv ns-sym]
  (::macro-requires (meta (cljs-ns cenv ns-sym)) #{}))

(defn find-cljs-ns
  "The ClojureScript namespace `sym`, or nil - cljs-ns without the creation."
  ^Namespace [^CompileEnv cenv sym]
  (.find ^NamespaceWorld (:world cenv) sym))

;; --- what the ns form records ------------------------------------------------
;;
;; On the namespace object's own metadata, not in a field of CompileEnv. A
;; NamespaceWorld is this compiler's answer to cljs.analyzer's one big
;; [::namespaces ns ...] map, and these are two more entries of it: they are
;; per-namespace, they are per-world for free, and a REPL can look at them with
;; (meta (env/cljs-ns cenv)). A field would be a fourth piece of state to move in
;; step with the world it describes.

(defn add-imports!
  "Record that `ns-sym` (:import ...)ed the classes in `m`, a map from the bare
  class name to the qualified Closure name it stands for.

  An :import is applied as a require plus an alias, and the alias is all the rest
  of the compiler needs - StringBuffer resolves through it like any other. This
  keeps the pair anyway, because ns-imports asks a question an alias cannot
  answer: WHICH of a namespace's aliases came from an :import. cljs.analyzer keeps
  the same map under [::ana/namespaces ns :imports], separately from :requires,
  and cljs.core/ns-imports reads it there.

  Beside ::global-refers on the namespace's metadata, and for the same reason: an
  analysis env is built fresh per form, and this has to outlive the ns form."
  [^CompileEnv cenv ns-sym m]
  (alter-meta! (cljs-ns cenv ns-sym) update ::imports merge m)
  m)

(defn imports
  "What `ns-sym` imported: {StringBuffer goog.string.StringBuffer}."
  [^CompileEnv cenv ns-sym]
  (or (::imports (meta (some-> (find-cljs-ns cenv ns-sym)))) {}))

(defn declared-requires
  "The ClojureScript namespaces `ns-sym`'s ns form actually wrote down. Names, not
  aliases: an alias is an alias on the Namespace itself, and a :require with no :as
  adds none.

  PROVENANCE, where `requires` below is EFFECT. The two differ by cljs.core, which
  every namespace requires whether or not it said so, and the difference matters in
  one direction only: a caller asking what the source declared wants this, and a
  caller about to emit an import or resolve a name wants the other. `requires` is
  the one to reach for by default, because forgetting cljs.core there means a module
  that silently omits its import."
  [^CompileEnv cenv ns-sym]
  (::requires (meta (cljs-ns cenv ns-sym)) #{}))

(defn requires
  "Every ClojureScript namespace `ns-sym` requires, declared or not.

  Read by qualified-symbol resolution, which refuses a namespace that is not in
  here, and by the emitter, which binds one namespace object per entry.

  CLJS.CORE IS IN EVERY SET, said or not, which is the LOAD half of the implicit
  require (doc/cljs-compiler.md §5.12) - resolve-ns has the naming half. Here
  rather than in parse-ns, where ClojureScript writes it, for the reason given
  there: a namespace with no ns form at all is the REPL's starting one, and it
  needs cljs.core as much as any other.

  Everything downstream then follows with no case of its own. A module gets an
  import (driver/module-text), a script gets an await $CLJS.require
  (emitter/script-prologue), and the driver compiles it first because it compiles
  what a namespace requires before the namespace itself.

  Not for cljs.core, which would then require itself: an import cycle the module
  system tolerates and a compile cycle the driver refuses by name."
  [^CompileEnv cenv ns-sym]
  (let [required (declared-requires cenv ns-sym)]
    (if (= 'cljs.core ns-sym)
      required
      (conj required 'cljs.core))))

(defn add-require!
  "Record that `ns-sym` requires `required`, and create the required namespace so
  that a var can be referred out of it.

  Creating it is all this does. Compiling a required namespace that has not been
  analysed yet needs source resolution and a compilation driver, which is M3's
  second half - so until then the namespaces of a program are analysed in
  dependency order by whoever drives the compiler, exactly as require-macros! was
  called by hand before this form existed."
  [^CompileEnv cenv ns-sym required]
  (cljs-ns cenv required)
  (alter-meta! (cljs-ns cenv ns-sym) update ::requires (fnil conj #{}) required)
  required)

;; --- what a STRING require records -------------------------------------------
;;
;; Three entries, on the same metadata and for the same reason as ::imports above.
;; They are kept apart from ::requires, and that separation is the whole of the
;; model: a JavaScript module is not a namespace. It has no Namespace object, no
;; vars, no source to compile and no place in the dependency graph the driver
;; walks - so a specifier in the requires set would send that driver looking for
;; react.cljs, and would make resolve-ns answer for a name that has nothing to
;; answer with.
;;
;; What they hold, all keyed by the namespace that wrote the ns form:
;;
;;   ::js-requires  the specifiers, which is what a module imports and what a
;;                  script awaits - one import per specifier, however many names
;;                  the ns form drew out of it
;;   ::js-aliases   {alias [specifier path]}, for (:require ["react" :as React])
;;                  and the React/createElement that follows - the path being the
;;                  $ sugar, nil whenever the alias names the module itself
;;   ::js-refers    {name [specifier export]}, for :refer and :default, which
;;                  bring a BARE name into scope the way a :refer of a var does -
;;                  the export being a dotted path when the $ sugar named one
;;
;; And one more of the same kind for the other world of JavaScript this compiler
;; knows, which lives here for the same reason - a Closure name is not a Var
;; either, so a refer of one has nowhere in a Namespace to go:
;;
;;   ::goog-refers  {name goog.string/format}, for (:require [goog.string :refer
;;                  [format]]) - the value being the QUALIFIED name the bare one
;;                  stands for, which is all the resolver needs because the
;;                  qualified spelling already resolves (analyzer's
;;                  analyze-qualified-symbol)

(defn add-js-require!
  "Record that `ns-sym` requires the JavaScript module `specifier`.

  Nothing is created and nothing is checked: there is no module to make and no way
  to ask a JavaScript file what it exports. The specifier's SHAPE was checked when
  the ns form was read (clojure.cljs.output/js->path), and whether the file is
  there is answered by the bundler that builds npm/ - a question this compiler
  reports on rather than settles."
  [^CompileEnv cenv ns-sym specifier]
  (alter-meta! (cljs-ns cenv ns-sym) update ::js-requires (fnil conj #{}) specifier)
  specifier)

(defn js-requires
  "Every JavaScript module `ns-sym` requires, sorted.

  SORTED, where `requires` is not: every caller of that one sorts at the point of
  use (driver/module-text does), and this has one shape of caller - a list of
  import lines, or of awaits - so the order belongs here rather than at each of
  them. Alphabetical rather than as-written, because a set does not remember how it
  was written: an import list that moved when a line of the ns form moved would be
  a changed file to whatever is watching the output directory."
  [^CompileEnv cenv ns-sym]
  (sort (::js-requires (meta (cljs-ns cenv ns-sym)) #{})))

(defn add-js-alias!
  "Record that `ns-sym` named `alias` for the module `specifier`, or - when `path`
  is not nil - for what sits at that property path inside it."
  [^CompileEnv cenv ns-sym alias specifier path]
  (alter-meta! (cljs-ns cenv ns-sym) update ::js-aliases assoc alias [specifier path])
  alias)

(defn js-aliases
  "What `ns-sym` called the JavaScript modules it required: {React [\"react\" nil]}.

  [specifier path], where the path is nil for a plain (:require [\"react\" :as
  React]) and a dotted string for the $ sugar - [\"date-fns/sub$default\" :as sub]
  gives {sub [\"date-fns/sub\" \"default\"]}. Both halves of a $ specifier are one
  import of the module, so what is recorded here is the module and a way into it,
  which is also the shape js-refers has."
  [^CompileEnv cenv ns-sym]
  (::js-aliases (meta (some-> (find-cljs-ns cenv ns-sym))) {}))

(defn add-js-refers!
  "Record the bare names `ns-sym` drew out of JavaScript modules: `m` is
  {name [specifier export]}."
  [^CompileEnv cenv ns-sym m]
  (alter-meta! (cljs-ns cenv ns-sym) update ::js-refers merge m)
  m)

(defn js-refers
  "The bare names `ns-sym` drew out of JavaScript modules: {useState [\"react\"
  \"useState\"]}.

  :refer and :default are one thing here, differing only in the export named -
  which is what they are in JavaScript too, where `default` is an export like any
  other with a name that happens to be a keyword."
  [^CompileEnv cenv ns-sym]
  (::js-refers (meta (some-> (find-cljs-ns cenv ns-sym))) {}))

(defn add-goog-refers!
  "Record the bare names `ns-sym` drew out of Closure namespaces: `m` is
  {name qualified-name}."
  [^CompileEnv cenv ns-sym m]
  (alter-meta! (cljs-ns cenv ns-sym) update ::goog-refers merge m)
  m)

(defn goog-refers
  "The bare names `ns-sym` drew out of Closure namespaces: {format
  goog.string/format}.

  The value is the QUALIFIED symbol and nothing else, because the qualified
  spelling is already a complete answer: goog.string/format resolves to the
  provide goog.string.format, gobject/get to a property of the goog.object
  namespace object, and a name in a namespace this fork REDUCED is refused by
  name. A refer therefore has nothing of its own to decide - it says which
  qualified name a bare one stands for, and hands the question on."
  [^CompileEnv cenv ns-sym]
  (::goog-refers (meta (some-> (find-cljs-ns cenv ns-sym))) {}))

(defn all-cljs-ns
  "Every ClojureScript namespace in this environment."
  [^CompileEnv cenv]
  (seq (.all ^NamespaceWorld (:world cenv))))

(defn remove-var!
  "Undefine `qsym` - the JVM half of clojure.cljs.repl's remove-var.

  Not only from the namespace that defined it. A var referred into another
  namespace is a mapping there holding the same Var object, and leaving those
  behind would let the deleted name go on resolving from wherever it was referred -
  so every namespace in the world is checked and any mapping to this Var is
  removed. Replique does the same thing by scanning each namespace's :uses and
  :renames; holding real Var objects makes it an identity test instead.

  Throws if there is no such var, because the alternative is a REPL command that
  silently does nothing when the name is misspelled. Returns the namespaces it
  unmapped from, the defining one first."
  [^CompileEnv cenv qsym]
  (when-not (qualified-symbol? qsym)
    (throw (ex-info (str "remove-var needs a qualified symbol, got " (pr-str qsym))
                    {:sym qsym})))
  (let [ns-sym     (symbol (namespace qsym))
        name-sym   (symbol (name qsym))
        ^Namespace home (or (find-cljs-ns cenv ns-sym)
                            (throw (ex-info (str "No such namespace: " ns-sym)
                                            {:sym qsym})))
        ^Var v     (or (.findInternedVar home name-sym)
                       (throw (ex-info (str "No such var: " qsym) {:sym qsym})))]
    (.unmap home name-sym)
    (into [ns-sym]
          (for [^Namespace n (all-cljs-ns cenv)
                :when (not (identical? n home))
                [sym mapping] (.getMappings n)
                :when (identical? v mapping)]
            (do (.unmap n sym) (.getName n))))))

(defn declared?
  "Has an ns form for `ns-sym` been analysed in this environment?

  Not the same question as whether the namespace exists: add-require! creates one
  on being named, so existence says only that something mentioned it. A compilation
  driver needs the stronger fact - a namespace that is declared but has no source
  file was defined at the REPL, and demanding a file for it would be wrong.

  find-cljs-ns rather than cljs-ns, so ASKING CREATES NOTHING. It used to, and the
  cost was a wrong answer somewhere else: the analyzer asks this about the prefix
  of every qualified symbol it cannot otherwise place, and Math/floor left a
  ClojureScript namespace called Math behind - which the next branch along then
  found in the world and refused, instead of letting Math/floor be the JavaScript
  global it is (doc/cljs-compiler.md 5.8)."
  [^CompileEnv cenv ns-sym]
  (boolean (some-> (find-cljs-ns cenv ns-sym) meta ::declared)))

(defn declare-ns!
  [^CompileEnv cenv ns-sym]
  (alter-meta! (cljs-ns cenv ns-sym) assoc ::declared true)
  ns-sym)

(defn clear-ns-declaration!
  "Everything a previous ns form for `ns-sym` established, removed: its requires,
  its aliases, its refers, its excludes, and the same on the macro side.

  An ns form DECLARES a namespace's dependencies rather than adding to them, so
  re-analysing one - which is what recompiling an edited file is - has to replace
  what the last one left. Without this, deleting a :require from a file left the
  require in the compile environment, and the module went on emitting an import for
  a namespace its source no longer mentions; deleting an :as left the alias
  resolving; deleting a :refer left the name in scope. cljs.analyzer replaces the
  same way, by building a fresh namespace map rather than updating one.

  A REFER is told from a DEF by whose namespace the var belongs to, which is
  exactly what the two mean: a def interns here, a refer maps something from
  elsewhere. So nothing has to be tracked for this to be exact. On the macro side
  every mapping is a refer, since nothing is ever interned into a view.

  Called at the point an ns form starts being applied, never while it is being
  checked, so a form that throws still leaves the namespace as it was."
  [^CompileEnv cenv ns-sym]
  (let [^Namespace ns   (cljs-ns cenv ns-sym)
        ^Namespace view (macro-view cenv ns-sym)]
    (doseq [[alias _] (.getAliases ns)]
      (.removeAlias ns alias))
    (doseq [[sym v] (.getMappings ns)
            :when   (and (instance? Var v) (not (identical? ns (.ns ^Var v))))]
      (.unmap ns sym))
    (doseq [[alias _] (.getAliases view)]
      (.removeAlias view alias))
    (doseq [[sym _] (.getMappings view)]
      (.unmap view sym))
    (alter-meta! ns dissoc ::requires ::excludes ::global-refers ::imports
                 ::js-requires ::js-aliases ::js-refers ::goog-refers)
    ns-sym))

(defn excluded?
  "Is `sym` excluded from the core namespace in `ns-sym`? (:refer-clojure :exclude).

  Macro lookup consults this before falling back to :core-macros, which is the only
  thing it can affect until cljs.core is vendored and core vars exist to be hidden
  as well (M5)."
  [^CompileEnv cenv ns-sym sym]
  (contains? (::excludes (meta (cljs-ns cenv ns-sym)) #{}) sym))

(defn add-excludes!
  [^CompileEnv cenv ns-sym syms]
  (alter-meta! (cljs-ns cenv ns-sym) update ::excludes (fnil into #{}) syms))

(defn core-name?
  "Does cljs.core already have `sym` - as a var, or as a macro?

  Asked by parse-def, which excludes the name it is about to intern when the
  answer is yes: a def of a name cljs.core has takes that name over, and TAKING IT
  OVER HAS TO INCLUDE THE MACRO. Var resolution needs no help - resolve-var asks
  this namespace's own mappings first - but macro expansion happens before
  resolution is consulted at all, so without this a namespace could define `/`,
  have it resolve correctly, and still see every (/ x) in the file expand to
  division by cljs.core's `/` macro. cljs/extend_to_native_test.cljs is the case:
  (defprotocol Slashy (/ [_])).

  cljs.analyzer's core-name? (analyzer.cljc:2079), asked at the same point and
  answered from the same two places: cljs.core's :defs and its :macros.

  The macro half is asked of :core-macros rather than of cljs.core by name, so an
  environment that opted out of the core macros - the analyzer's own tests do -
  gets the answer that is true for it."
  [^CompileEnv cenv sym]
  (boolean
   (or (some-> ^Namespace (find-cljs-ns cenv 'cljs.core) (.findInternedVar sym))
       (when-let [^clojure.lang.Namespace mns (some-> (:core-macros cenv) find-ns)]
         (when-let [^Var v (.findInternedVar mns sym)]
           (.isMacro v))))))

;; --- the analysis environment handed to macros as &env ---------------------

(defn- ns-requires-map
  "{alias full-name, full-name full-name} for `ns-sym` - every name by which this
  namespace can call something it requires, mapped to that thing's real name.

  ClojureScript's `:requires`. A namespace's OWN names are in it as well as its
  aliases, because both are things a program may write and both have to resolve to
  the same target.

  JAVASCRIPT MODULES ARE NOT IN IT, and that is our model rather than an omission:
  a module is not a namespace here - it has no Namespace, no vars and no place in
  the dependency graph - which is exactly why env/js-aliases is a map of its own
  (doc/cljs-compiler.md §5.51). Upstream lists them under :requires because it has
  nowhere else to put them."
  [^CompileEnv cenv ns-sym]
  (let [^Namespace ns (cljs-ns cenv ns-sym)]
    (persistent!
     (reduce (fn [m [alias ^Namespace target]] (assoc! m alias (.getName target)))
             (reduce (fn [m r] (assoc! m r r))
                     (transient {})
                     (::requires (meta ns) #{}))
             (.getAliases ns)))))

(defn- ns-use-macros-map
  "{macro-name macro-namespace} for `ns-sym` - ClojureScript's `:use-macros`.

  Read off the MACRO VIEW, which is where a :refer-macros / :use-macros mapping
  actually lives here (require-macros!): a Var in the view that was interned
  somewhere else is a macro this namespace calls by a bare name, and the namespace
  it came from is the answer."
  [^CompileEnv cenv ns-sym]
  (let [^Namespace view (macro-view cenv ns-sym)]
    (persistent!
     (reduce (fn [m [sym v]]
               (if (and (instance? Var v) (not (identical? view (.ns ^Var v))))
                 (assoc! m sym (.getName (.ns ^Var v)))
                 m))
             (transient {})
             (.getMappings view)))))

(defn analysis-env
  "A fresh &env for the namespace `cenv` is currently in.

  ClojureScript's shape, minus what does not exist yet. :ns is a map so the usual
  (:name (:ns &env)) reads correctly; cljs.core's macros reach for (:locals &env),
  (:def-emits-var &env), (:async &env) and, at one site, (-> &env :ns :defs).
  Since we own the vendored core.cljc (doc/cljs-compiler.md §4.4), that last one is
  adaptable rather than binding.

  THREE KEYS THAT USED TO BE PART OF `minus what does not exist yet` AND NOW DO
  EXIST - :requires, :excludes and :use-macros (doc/cljs-compiler.md §5.55). A
  macro of somebody else's may read any of them, and core.async's `go` reads the
  first: it looks its parking operations up by fully-qualified name, so a body
  written with an alias - (a/<! c), which is how everybody writes it - resolves
  through `:requires` or not at all. Without it `go` COMPILED and produced code
  that threw `>! used not in (go ...) block` at run time, which is the worst
  failure this compiler can have (doc/cljs-compiler.md §8, M5).

  :line AND :column ARE A FOURTH SUCH KEY AND ARE NOT HERE, deliberately:
  clojure.cljs.analyzer/analyze-seq merges them into the env it hands to
  macroexpand-1, as ClojureScript's analyze-seq does, because a position belongs to
  the form being analysed and a FRESH env has none - so a macro reads them off
  `&env` and nothing reads them off this. Standing alone, this env describes a
  namespace rather than a form and has no position to give
  (doc/cljs-compiler.md §5.66).

  They are also what upstream's `excluded?` and `used?` ask for FIRST, before the
  compiler-state atom they fall back to - which is what keeps that atom a constant
  rather than a second copy of our symbol table. See
  clojure.cljs.macroexpand/with-upstream-state!."
  [^CompileEnv cenv]
  {:ns      {:name       *current-ns*
             :requires   (ns-requires-map cenv *current-ns*)
             :excludes   (::excludes (meta (cljs-ns cenv *current-ns*)) #{})
             :use-macros (ns-use-macros-map cenv *current-ns*)}
   :locals  {}
   :context :statement})

(defn with-locals
  "Add locals to an &env. A local hides a macro of the same name, so this is not
  cosmetic. The value shape is minimal until the analyzer defines it."
  [env syms]
  (update env :locals into (map (fn [s] [s {:name s :op :local}])) syms))

;; --- resolution --------------------------------------------------------------

(defn resolve-ns
  "The ClojureScript namespace the namespace part of a qualified symbol names from
  `ns-sym`: an alias, that namespace's own name, or one it requires.

  Requiring is not optional, and that is deliberate: a namespace reachable merely
  by having been compiled would make a typo in a name resolve to whatever else the
  session happens to hold. ClojureScript is strict here too.

  ONE name is rewritten: clojure.core is cljs.core. That is not a convenience -
  every syntax-quote in a macro resolves its symbols against the JVM, so
  `(if (not ~test) ...)` in cljs/core.cljc arrives here as clojure.core/not and
  nothing else could make it resolve. cljs.analyzer/resolve-var rewrites in the
  same place and rewrites the same single name, AFTER an alias has had its chance
  - so a namespace that aliases clojure.core to something of its own still wins."
  ^Namespace [^CompileEnv cenv nsym]
  (let [here *current-ns*]
    (or (.lookupAlias ^Namespace (cljs-ns cenv) nsym)
        (let [nsym (if (= 'clojure.core nsym) 'cljs.core nsym)]
          (cond
            ;; CLJS.CORE IS REQUIRED BY EVERY NAMESPACE, said or not, which is the
            ;; naming half of the implicit require (doc/cljs-compiler.md §5.9).
            ;; ClojureScript's parse-ns writes it into every :requires map; ours is
            ;; here rather than there so that a namespace with no ns form at all -
            ;; the REPL's starting one - gets it too.
            ;;
            ;; cljs-ns rather than find-cljs-ns, so it exists after being named:
            ;; the emitter already binds $ns("cljs.core") in every module
            ;; (nameable-namespaces), and a JVM-side namespace that did not exist
            ;; to match would make `first` resolvable in the emitted code and not
            ;; in the compiler.
            (= 'cljs.core nsym) (cljs-ns cenv 'cljs.core)

            (or (= nsym here) (contains? (requires cenv here) nsym))
            (find-cljs-ns cenv nsym))))))

(defn resolve-var
  "The ClojureScript Var `sym` names in cenv's current namespace, or nil.

  The same three rules analyze-symbol follows, and it is the analyzer that owns
  the error messages: getMapping unqualified, so a referred var resolves;
  findInternedVar qualified, so what another namespace merely refers is not
  reachable through its name; and cljs.core last, which is the REFER half of the
  implicit require (doc/cljs-compiler.md §5.12) - resolve-ns above has the naming
  half.

  THE THIRD RULE LIVES HERE RATHER THAN IN THE ANALYZER, and that is the whole
  point of this function existing. A macro resolves names too, and it resolves
  exactly the names this rule is about: extend-type turns ICloneable into a
  property, defrecord extends fourteen cljs.core protocols in its expansion, and
  satisfies? asks the same question at a call site. Answered only in
  analyze-symbol, the rule would leave every one of those resolving a core
  protocol to a var in the CURRENT namespace instead - which is not an error but a
  wrong property name, so a record would quietly fail to satisfy IMap. Both
  callers ask here, so neither can drift from the other.

  Public because a MACRO needs it. defprotocol, deftype, extend-type and
  satisfies? all have to turn a protocol symbol into a JavaScript property name
  (clojure.cljs.names/protocol-name), and a macro sees only &form and &env - so it
  reaches the compile environment through *cenv* and the symbol table through
  here. cljs.core's macros do the same thing with cljs.analyzer/resolve-var and
  cljs.env/*compiler*."
  ^Var [^CompileEnv cenv sym]
  (let [v (if-let [nsym (some-> (namespace sym) symbol)]
            (when-let [^Namespace target (resolve-ns cenv nsym)]
              (.findInternedVar target (symbol (name sym))))
            (let [here *current-ns*
                  m    (.getMapping ^Namespace (cljs-ns cenv) sym)]
              (if (instance? Var m)
                ;; a mapping of this namespace's own wins, because it was asked
                ;; first: (def reduce ...) here shadows the core one, as it does in
                ;; Clojure. :refer-clojure :exclude is the other way to say it.
                m
                ;; asked only when nothing nearer answered, so the common case pays
                ;; one nil test rather than a lookup in another namespace
                (when-not (or (= 'cljs.core here) (excluded? cenv here sym))
                  (some-> ^Namespace (find-cljs-ns cenv 'cljs.core)
                          (.findInternedVar sym))))))]
    (when (instance? Var v) v)))

(defn dotted-var-sym
  "The fully-qualified name of the var a SIMPLE symbol with dots names here -
  cljs.core.first is cljs.core/first - or nil.

  The analyzer's rule and it has to be the same one: the longest prefix that names
  a namespace splits from the name, which is analyze-dotted-symbol's second
  reading. Its first reading - the head names a value, so the rest are properties -
  is not a var and is not asked about here.

  Here because a MACRO asks the same question. cljs.core/exists? is handed a name
  and has to say whether it is a var or a namespace, and the two are different
  code; cljs/core_test.cljs writes (exists? cljs.core.first) and expects true.
  ClojureScript needs no such function because a var there IS a global path, so
  the dotted name is already the JavaScript it wants."
  [^CompileEnv cenv sym]
  (when (and (simple-symbol? sym) (.contains (str sym) "."))
    (let [^String s (str sym)]
      ;; from the LAST dot leftwards, so the longest namespace prefix wins
      (loop [i (.lastIndexOf s ".")]
        (when (pos? i)
          (let [q (symbol (subs s 0 i) (subs s (inc i)))]
            (if (some? (resolve-var cenv q))
              q
              (recur (.lastIndexOf s "." (dec i))))))))))

(defn var-sym
  "The fully-qualified name of the var `sym` names here - app.core/IShape - or nil.
  What a macro wants out of resolve-var nine times in ten."
  [^CompileEnv cenv sym]
  (when-let [^Var v (resolve-var cenv sym)]
    (symbol (str (.getName (.ns v))) (str (.sym v)))))

(def ^:dynamic *cenv*
  "The compile environment the macro now running was expanded in, or nil outside
  one. Bound by clojure.cljs.macroexpand around the call, and nowhere else.

  A dynamic var, in a compiler whose whole posture is to thread its environment
  explicitly (doc/compiler-rewrite.md §3). The exception is not a slip: a macro's
  parameters are &form and &env and nothing else, so an explicit argument is not
  available to it at all. cljs.env/*compiler* is the same admission, and vendoring
  core.cljc at M5 means meeting it anyway.

  Scoped to the macro call rather than to the compilation, so nothing that is not
  a macro can read it by accident, and a macro that starts a nested compilation
  gets that compilation's environment rather than this one's."
  nil)

;; --- the other compiler's symbol table ---------------------------------------
;;
;; cljs.analyzer keeps every namespace it knows about in one map under
;; [::ana/namespaces], and cljs.analyzer.api is a reading facade over it: resolve,
;; find-ns, ns-publics, all-ns. A library macro that wants to know something about
;; the program it is expanding inside asks THAT, because that is the compiler it
;; was written for. sci's protocol-vars asks whether cljs.core/ICloneable is a
;; protocol; kitchen-async's fixup-alias asks what a namespace's aliases point at.
;; So the map has to answer.
;;
;; §5.55 could leave the compiler-state atom a constant because the two things
;; upstream's MACRO LOOKUP reads through it are asked of &env first. Nothing asks
;; &env first here: cljs.analyzer.api goes straight to the atom, and there is no
;; other road into it.
;;
;; ANSWERED RATHER THAN BUILT. Copying the world into upstream's shape once per
;; macroexpansion would cost more than the macroexpansions do - cljs.core alone is
;; thousands of vars - and copying it once and caching it would go stale exactly
;; when it matters, because the world grows as compilation proceeds and a macro
;; asks about the namespace being compiled. What upstream does with the map is
;; `gets`, which is plain nested `get` (doc/cljs-compiler.md §5.54), so a LOOKUP is
;; all of it that is ever used - and a lookup can be computed when it is asked.
;;
;; The boundary is stated rather than hidden: these answer ILookup and Seqable,
;; which is get, get-in and keys. Anything else - assoc, contains?, a swap! into
;; the map - fails loudly instead of silently returning a half-truth about a
;; symbol table that is not really a map.

(defn- interned-defs
  "[::namespaces <ns> :defs] - what a def carried, per symbol.

  cljs.analyzer stores a map it built while analysing the def; we have the Var,
  and its metadata IS what the def carried. clojure.cljs.analyzer/resolve-var
  already answers this same question for cljs.core's own macros, in the same words
  (:protocol-symbol, :protocol-info, :const, :deprecated), which is the point:
  this is not new knowledge, only the other compiler's spelling of it.

  INTERNED, not mapped. A :refer puts another namespace's Var in this one's
  mappings, and upstream keeps those under :uses and :renames - see
  ns-refers-and-renames. Seqable as well as ILookup because
  cljs.analyzer.api/ns-publics walks it, which is how sci asks a namespace what it
  has in it."
  [^Namespace ns]
  (let [info (fn [^Var v]
               (assoc (meta v)
                      :name (symbol (str (.getName ns)) (str (.sym v)))
                      :ns   (.getName ns)))]
    (reify
      clojure.lang.ILookup
      (valAt [this k] (.valAt this k nil))
      (valAt [_ k nf]
        (if-let [^Var v (when (symbol? k) (.findInternedVar ns ^Symbol k))]
          (info v)
          nf))
      clojure.lang.Seqable
      (seq [_]
        (seq (into [] (keep (fn [[sym v]]
                              (when (and (instance? Var v)
                                         (identical? ns (.ns ^Var v)))
                                (clojure.lang.MapEntry/create sym (info v)))))
                   (.getMappings ns)))))))

(defn- ns-refers-and-renames
  "{:uses {name namespace} :renames {here there-qualified}} for `ns-sym`.

  One pass, because in this world a :refer and a :rename are the same act - the
  analyzer .refer's the other namespace's Var in under some name - and what tells
  them apart is whether that name is the Var's own. Upstream keeps them in two
  maps because it never has the Var to ask."
  [^CompileEnv cenv ns-sym]
  (let [^Namespace ns (cljs-ns cenv ns-sym)]
    (reduce (fn [m [sym v]]
              (if (or (not (instance? Var v)) (identical? ns (.ns ^Var v)))
                m
                (let [there (.getName (.ns ^Var v))]
                  (if (= sym (.sym ^Var v))
                    (assoc-in m [:uses sym] there)
                    (assoc-in m [:renames sym] (symbol (str there) (str (.sym ^Var v))))))))
            {:uses {} :renames {}}
            (.getMappings ns))))

(defn- ns-require-macros-map
  "{alias macro-namespace} for `ns-sym` - ClojureScript's :require-macros.

  An alias in the macro view already points at a real loaded JVM namespace, which
  is the whole of what the macro world is for (see the namespace docstring)."
  [^CompileEnv cenv ns-sym]
  (persistent!
   (reduce (fn [m [alias ^Namespace target]] (assoc! m alias (.getName target)))
           (transient {})
           (.getAliases ^Namespace (macro-view cenv ns-sym)))))

(defn- upstream-ns-entry
  "[::namespaces <ns>] for one namespace, or nil if there is no such namespace.

  Nil rather than an empty map on purpose: upstream's loaded-js-ns? reads absence
  here as `this name is a JavaScript namespace rather than a ClojureScript one`,
  and an empty map would answer that question the wrong way round."
  [^CompileEnv cenv ns-sym]
  (when-let [^Namespace ns (find-cljs-ns cenv ns-sym)]
    (merge {:name           ns-sym
            :defs           (interned-defs ns)
            :requires       (ns-requires-map cenv ns-sym)
            :require-macros (ns-require-macros-map cenv ns-sym)
            :use-macros     (ns-use-macros-map cenv ns-sym)
            :excludes       (::excludes (meta ns) #{})
            :imports        (imports cenv ns-sym)}
           (ns-refers-and-renames cenv ns-sym))))

(defn upstream-namespaces
  "cljs.analyzer's [::namespaces] map, answered from the world instead of copied
  into it. See the section note above for why it is a lookup and not a map.

  With no argument it reads whatever *cenv* is bound to when the lookup happens,
  which is what lets clojure.cljs.macroexpand hold ONE of these in a constant atom
  for the whole compiler rather than allocating a compile environment's worth of
  them per macroexpansion."
  ([] (upstream-namespaces nil))
  ([cenv]
   (let [world  (fn [] (or cenv *cenv*))
         entry  (fn [c k] (when (symbol? k) (upstream-ns-entry c k)))
         allsq  (fn [^CompileEnv c]
                  (seq (mapv (fn [^Namespace n]
                               (clojure.lang.MapEntry/create
                                (.getName n) (upstream-ns-entry c (.getName n))))
                             (all-cljs-ns c))))]
     (reify
       clojure.lang.ILookup
       (valAt [this k] (.valAt this k nil))
       (valAt [_ k nf] (or (when-let [c (world)] (entry c k)) nf))

       clojure.lang.Seqable
       (seq [_] (when-let [c (world)] (allsq c)))

       clojure.lang.IPersistentCollection
       (count [_] (if-let [c (world)] (count (all-cljs-ns c)) 0))
       (empty [_] {})
       (equiv [this o] (identical? this o))
       ;; A WRITE IS DROPPED, and this is the one place that needs saying out loud.
       ;; cljs.analyzer swaps bookkeeping into [::namespaces <ns> :externs] while
       ;; resolving a js/ name, for an externs-inference pass it runs later. We
       ;; have no such pass, and nothing here is written through the atom anyway -
       ;; a def reaches the symbol table by being analysed, which interns a Var.
       ;; So the write has nothing to change and nothing to tell, and returning
       ;; the view unchanged leaves the atom holding exactly what it held before.
       ;; Refusing instead would break the macro that triggered it over
       ;; bookkeeping neither compiler would ever read.
       (cons [this _] this)

       clojure.lang.Associative
       (containsKey [_ k] (boolean (when-let [c (world)] (entry c k))))
       (entryAt [_ k] (when-let [c (world)]
                        (when-let [e (entry c k)]
                          (clojure.lang.MapEntry/create k e))))
       (assoc [this _ _] this)))))
