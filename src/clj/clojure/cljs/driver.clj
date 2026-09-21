;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The compilation driver: source files in, ES modules out.

  Named driver rather than compiler because cljs.compiler is ClojureScript's
  emitter, cited throughout these docs as the emission oracle, and one of the two
  should not have to be qualified every time it is mentioned.

  What it adds to the pieces that were already here is the only thing none of them
  could do alone: an ORDER. clojure.cljs.analyzer needs a namespace's requires
  analysed before it can resolve a symbol into them, and finding out which they are
  cannot wait for parse-ns, which is what needs them. So the driver reads a file's
  ns form, compiles what it names, and only then analyses the file - depth first,
  post-order, which is the order the module system will evaluate the output in
  anyway.

  Two paths reach the runtime, and this builds the first one:

    a MODULE on disk, imported. Its static imports carry the load order, so a cold
    start needs no manifest and no ordering computation at load time - one
    <script type=\"module\"> entry point pulls the whole graph (doc/cljs-repl.md
    §7.1).

    a SCRIPT, evaluated. What the REPL ships. Same body, different prologue.

  SOURCE PATHS ARE DIRECTORIES, and munged, because a source file is not ours to
  name: my-lib.core has always been my_lib/core.cljs, and that is what people have
  on disk. The OUTPUT path is unmunged (clojure.cljs.output), because that one is
  ours. The two differing is the honest answer rather than an inconsistency - one
  follows a convention we inherited, the other follows a rule we chose, and each
  says which in its own docstring.

  A macro namespace is NOT resolved here. (:require-macros [foo.macros]) names a
  real JVM namespace, and the classpath finds it, exactly as it does for any other
  Clojure code - so a .clj macro file beside a .cljs source has to be on the
  classpath rather than merely on the source path.

  NOT INCREMENTAL, and the reason is worth stating rather than fixing here: a
  CompileEnv lives only as long as the JVM, so every namespace in the graph has to
  be analysed on every run whatever its file's mtime says. Skipping the write would
  save an emit and a spit and nothing else. What it would save is a needless mtime
  change, so the write is skipped when the text is identical - enough to leave
  editors and watchers alone. Real incremental compilation is the analysis
  subsystem's stale-files, which persists a model across restarts; wiring to it is
  its own piece of work.

  That skip rests on emission being deterministic, and it is with ONE exception,
  worth knowing before it is discovered: a macro that calls gensym mints a new name
  on every expansion, so a file using one compiles to different text every time and
  is rewritten every time. An auto-gensym does not - v# is minted once when the
  macro is READ, and clojure.cljs.names drops its decoration anyway - and nothing
  else in the output is allocated from outside the forms. No absolute path appears
  in it either, so the same source compiles identically in another output directory
  and on another machine - the source map included, which names its source by the
  path it would be found at rather than by where it was found (source-label).

  See doc/cljs-compiler.md M3."}
  clojure.cljs.driver
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.goog :as cgoog]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.cljs.names :as names]
            [clojure.cljs.output :as output]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.source-info :as si]
            [clojure.cljs.source-map :as sm]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io File]))

;; --- finding a source file --------------------------------------------------

(def source-extensions
  "In the order ClojureScript looks: a .cljs beats a .cljc of the same name."
  [".cljs" ".cljc"])

(defn ns->source-path
  "The source file for a namespace, relative to a source directory: my-lib.core is
  my_lib/core.cljs.

  MUNGED, unlike the output path, and clojure.core/munge is the same function
  cljs.util/ns->relpath uses. The two agree on every name a namespace segment may
  hold - our precondition allows no character that the two maps spell differently -
  so this is a hyphen-to-underscore rule with a wider one behind it for safety."
  [ns-sym ext]
  (str (str/replace (munge (str ns-sym)) \. \/) ext))

(defn default-source-paths
  "The directory entries of the classpath.

  A jar entry is skipped: a namespace inside a jar has no mtime to speak of and no
  ClojureScript library ships as one yet, so the day one does is the day to decide
  what that means rather than now."
  []
  (into [] (comp (map io/file) (filter #(.isDirectory ^File %)))
        (str/split (System/getProperty "java.class.path")
                   (re-pattern (java.util.regex.Pattern/quote File/pathSeparator)))))

(defn find-source
  "What `ns-sym` is compiled from, or nil. A File from the source paths, or a URL on
  the classpath when no source path holds it.

  THE CLASSPATH FALLBACK IS HOW cljs.core IS FOUND. It is not the user's source -
  it ships with this compiler, the way cljs/core.cljs ships inside the ClojureScript
  jar - so it must not depend on a caller having listed the directory it happens to
  live in today, and every namespace requires it (env/requires) so every compile
  needs it. A caller that passes :source-paths is replacing its own tree, not ours.

  It also happens to reach a library inside a jar, which default-source-paths
  deliberately skips. That skip stands: a jar entry has no mtime worth consulting,
  and this compiler is not incremental anyway, so what it costs is nothing and what
  it buys is that a jarred dependency compiles rather than being unfindable.

  Everything downstream takes a reader over it, so the two kinds are interchangeable
  - only compile-file!, which is handed a path by a user, needs a real file."
  [source-paths ns-sym]
  (or (first (for [dir  source-paths
                   ext  source-extensions
                   :let [f (io/file dir (ns->source-path ns-sym ext))]
                   :when (.isFile f)]
               f))
      (first (keep #(io/resource (ns->source-path ns-sym %)) source-extensions))))

;; --- one file ---------------------------------------------------------------

(def ^:private EOF (Object.))

(defn- module-text
  "The module for `ns-sym`: its imports, its prologue, then `body`.

  The imports are what the script path spells as await $CLJS.require, and the
  prologue is the same either way, which is the whole of doc/cljs-repl.md §4. Every
  specifier is computed by clojure.cljs.output from this module's own place in the
  tree, so a module two directories down reaches the prelude as ../../runtime.js.

  Returns a chunk rather than a string when the body lines carry positions, which
  is what compile-source! turns into the map beside it."
  [cenv ns-sym body]
  (let [required (env/requires cenv ns-sym)
        imports  (-> [(emitter/runtime-import
                       (output/specifier ns-sym output/prelude-name))]
                     (into (map #(emitter/ns-import
                                  (output/specifier ns-sym (output/ns->path %))))
                           (sort (disj (set required) ns-sym)))
                     ;; and one per JavaScript module, which is the other half of
                     ;; what a module's ns form can require. Last, so a specifier
                     ;; appearing or disappearing does not move the namespace
                     ;; imports above it - a module is rewritten when its text
                     ;; changed, and a shuffled import list is a changed text.
                     (into (map #(emitter/js-import
                                  (names/js-alias %)
                                  (output/specifier ns-sym (output/js->path %))))
                           (env/js-requires cenv ns-sym)))]
    ;; sm/join and not str/join: the body lines carry where they came from, and
    ;; joining them with clojure.string would flatten that back to a string.
    (sm/cat (sm/join "\n" (into imports
                                (-> (emitter/ns-prologue ns-sym required)
                                    (conj (emitter/fetched-mark ns-sym))
                                    (into body))))
            "\n")))

(defn- write-if-changed!
  "Write `text` - a string, or a chunk that also knows where its lines came
  from - to `f` unless that is already what it holds. Returns f when it
  wrote, nil when it did not - so a caller can report what actually moved.

  An optimisation, never a correctness measure: this namespace's docstring says
  which sources compile to different text every time, and for those this simply
  always writes."
  [^File f text]
  (let [^String text (sm/text text)]
    (.mkdirs (.getParentFile f))
    (when-not (and (.isFile f) (= text (slurp f)))
      (spit f text)
      f)))

(defn- map-name
  "The map beside a module: ns/app/core.js is mapped by core.js.map in the same
  directory.

  A BARE NAME, so the //# sourceMappingURL in the module resolves against whatever
  the module itself was loaded as - a file: URL under node, an http: one in a
  browser - without either side being told where the output root is. The same name
  works for the reload script, which carries the module's URL already
  (see body-script)."
  [ns-sym]
  (str (peek (str/split (output/ns->path ns-sym) #"/")) ".map"))

(defn- source-label
  "How a source names itself inside its map: the path it would be found at under a
  source directory, my_lib/core.cljs.

  Not where it was actually found, which is an absolute path on this machine and
  would make the output machine-dependent - the one thing this namespace's
  docstring promises it is not. The map embeds the source text anyway
  (clojure.cljs.source-map/encode), so the label is a label: it is what a sources
  panel shows and what a stack frame is reported against, and it is stable."
  [ns-sym src]
  (let [s (str src)]
    (ns->source-path ns-sym
                     (or (first (filter #(str/ends-with? s %) source-extensions))
                         (first source-extensions)))))

(defn- body-script
  "The same body as the module, as a script to evaluate: the namespace itself, the
  script prologue, the sweep, then the forms.

  This is doc/cljs-repl.md 7.1 - one namespace body, two prologues - and it is what
  makes a reload the same operation as a first load. Nothing is returned from it: a
  namespace body has no value, and the REPL prints its own.

  No sweep rides along here. A def deleted from the file stays interned and stays a
  property until something removes it, and reloading is not that something: which
  defs vanished is a question about provenance, and answering it from a diff the
  driver happens to compute in passing was a guess with no model behind it (7.3).
  Until the explicit sweep lands, clojure.cljs.repl/remove-var undefines one named
  var, which is what Replique offers and what a user actually reaches for.

  IT OPENS WITH AN EARLY RETURN, and the body below it is the second of two ways to
  get the same namespace into the same runtime:

      if (!$CLJS.fetched.has(name)) return $CLJS.fetch(name);

  If the module has never been through the module system, FETCHING it is the whole
  operation - the file and this body came from the same compile a moment ago, so
  they define the same things, and the fetch does one thing the body cannot: it
  registers the URL, so the next static import of this namespace returns the cached
  module rather than evaluating the file over whatever the REPL redefines later.
  Running the body as well would be worse than redundant, because a namespace body
  can have top-level effects and they would happen twice.

  If it HAS been fetched, the module system will never evaluate that file again, so
  running the body is the only way to change what is live - and that is the reload.

  Testing `fetched` rather than `loaded` is what makes the two cases exhaustive. A
  namespace can be loaded without having been fetched - an (ns foo) typed at the
  REPL marks it - and that is precisely the case where the body must not simply be
  run, because the URL would still be unregistered afterwards.

  The mark itself is set by the module (emitter/fetched-mark), not by whatever
  fetched it: a module body runs if and only if the file was evaluated, and it
  reaches that point through another module's static import as often as through
  $CLJS.require.

  IT CARRIES THE MODULE'S OWN URL, which is doc/cljs-output-layout.md §4 and the
  first of that section's two rules: a reloaded body is a new version of a file that
  already exists on disk and may be open in a browser's sources panel, so naming it
  after that file lets devtools replace the resource rather than add an anonymous
  one beside it. The REPL's rule is the opposite one, for the opposite reason - see
  clojure.cljs.repl/compile-form."
  [cenv ns-sym body]
  ;; text, not a chunk: a script is sent to a runtime, and the only thing that maps
  ;; it is the module's own map, which it names above.
  (sm/text
   (emitter/script
    (-> [(str "if (!$CLJS.fetched.has(\"" ns-sym "\")) return $CLJS.fetch(\""
              ns-sym "\");")]
        (into (emitter/script-prologue ns-sym (env/requires cenv ns-sym)
                                       (env/js-requires cenv ns-sym)))
        (into body))
    (output/ns->path ns-sym)
    (map-name ns-sym))))

(defn- compile-source!
  "Analyse `src` into `cenv`, write its module, and return what a REPL needs to
  make the same thing happen in a running runtime.

  The forms are read ONE AT A TIME and analysed as they are read, because reading
  is not independent of what has been analysed: ::kw and syntax-quote resolve
  against the namespace the reader is currently in, which the ns form moves. Every
  form of the file shares ONE name scope, because every form of a module lands in
  one JavaScript scope.

  Two files are written, not one: the module, and the source map beside it
  (doc/cljs-compiler.md §5.43). The map is returned as :mapped, separately from
  :written, because a map can be unchanged while its module is not - a gensym moves
  a NAME and not the line it sits on, which is exactly cljs.core on every compile.

  Nothing is removed here: see body-script for why a reload sweeps nothing."
  [cenv opts src ns-sym]
  (let [^File out (io/file (:out-dir opts) (output/ns->path ns-sym))
        label     (source-label ns-sym src)
        ;; READ AS A STRING rather than streamed, because the map embeds the source
        ;; and the only way to be sure the embedded text is the one that was
        ;; compiled is for them to be the same string.
        text      (slurp src)
        rdr       (reader/push-back-reader text)]
    (names/with-name-scope
      (let [body (loop [acc []]
                   (let [form (reader/read-one cenv rdr EOF)]
                     (if (identical? form EOF)
                       acc
                       ;; The &env PER FORM, not once for the file. It carries
                       ;; {:ns {:name ...}} as a VALUE, read as (-> &env :ns :name)
                       ;; by defprotocol, defmulti and deftype among others - and
                       ;; the file's ns form moves the cursor, so one built before
                       ;; the loop names whatever namespace the driver happened to
                       ;; be in when it opened the file. That is cljs.user for the
                       ;; first file of a run and the PREVIOUS file for every one
                       ;; after it, which is how a protocol in one namespace got
                       ;; method names qualified with another.
                       ;;
                       ;; LINES, not one string per form, and source-info before
                       ;; emitting: a line is what a source map maps, emit-top
                       ;; would join the lines into text whose interior boundaries
                       ;; nothing can find again, and the emitter attributes a line
                       ;; to a node from the position that pass writes (§5.43).
                       (recur (into acc
                                    (emitter/emit-top-lines
                                     (si/source-info
                                      (ana/analyze-top
                                       cenv (env/analysis-env cenv) form)
                                      (assoc (meta form) :file label))))))))
            module (sm/cat (module-text cenv ns-sym body)
                           "//# sourceMappingURL=" (map-name ns-sym) "\n")
            ^File out-map (io/file (str out ".map"))]
        {:written (write-if-changed! out module)
         :mapped  (write-if-changed!
                   out-map
                   (sm/encode {:file      (.getName out)
                               :positions (sm/line-positions module)
                               :content   {label text}}))
         :script  (body-script cenv ns-sym body)}))))

(defn- read-ns-form
  "The first form of `src`, which has to be the ns form it declares.

  ClojureScript requires this and so do we, for a reason of our own: the driver has
  to know a file's dependencies before it can analyse the file, and the ns form is
  where they are written. A file whose ns form came second would have half of it
  analysed against the wrong namespace before anyone found out."
  [cenv src ns-sym]
  (with-open [r (io/reader src)]
    (let [form (reader/read-one cenv (reader/push-back-reader r) EOF)]
      (when (identical? form EOF)
        (throw (ex-info (str src " is empty: a source file begins with its ns form.")
                        {:file (str src)})))
      (when-not (and (seq? form) (= 'ns (first form)))
        (throw (ex-info (str src " must begin with an ns form, not "
                             (pr-str (if (seq? form) (first form) form)) ".")
                        {:file (str src) :form form})))
      ;; ns-sym is nil when the file was named rather than looked up - load-file
      ;; learns the namespace from the form instead of checking it against a path
      (when (and ns-sym (not= ns-sym (second form)))
        (throw (ex-info (str src " declares " (pr-str (second form))
                             " but was required as " ns-sym
                             " - the file's name and its ns form have to agree.")
                        {:file (str src) :declared (second form) :required ns-sym})))
      form)))

;; --- the graph --------------------------------------------------------------

(declare ensure!)

(defn- compile-one!
  "Compile the file `src`, which declares `ns-sym`, after everything its ns form
  requires. The post-order step shared by looking a namespace up and being handed a
  file."
  [cenv opts state src ns-sym]
  (let [ns-form (read-ns-form cenv src ns-sym)
        ns-sym  (or ns-sym (second ns-form))
        ;; cljs.core FIRST and whether or not the ns form says so, because every
        ;; namespace requires it (env/requires) and so every module imports it.
        ;; Compiling it is what makes that import resolve to a file. Excluded for
        ;; cljs.core itself, which would otherwise be its own dependency and be
        ;; reported as a cycle.
        deps    (cond->> (ana/ns-form-deps ns-form)
                  (not= 'cljs.core ns-sym) (cons 'cljs.core))
        state   (reduce #(ensure! cenv opts %1 %2)
                        (update state :visiting conj ns-sym)
                        deps)
        {:keys [written mapped script]} (compile-source! cenv opts src ns-sym)]
    (-> state
        (update :visiting pop)
        (update :done conj ns-sym)
        (update :compiled conj ns-sym)
        (update :scripts conj [ns-sym script])
        (cond-> written (update :written conj written)
                mapped  (update :written conj mapped)))))

(defn- ensure!
  "Compile `ns-sym` if it has not been compiled in this run, its dependencies
  first. `state` carries what is done, what is being visited, and what was written."
  [cenv opts state ns-sym]
  (cond
    (contains? (:done state) ns-sym) state

    ;; a cycle. Depth first with no cycle check would recur until the stack ran
    ;; out, and the message for that names nothing at all
    (contains? (set (:visiting state)) ns-sym)
    (throw (ex-info (str "Circular dependency: "
                         (str/join " -> " (conj (vec (:visiting state)) ns-sym)))
                    {:cycle (conj (vec (:visiting state)) ns-sym)}))

    :else
    (if-let [src (find-source (:source-paths opts) ns-sym)]
      (compile-one! cenv opts state src ns-sym)

      ;; No file. Fine if the namespace was declared some other way - the REPL is
      ;; the other way - and an error otherwise, because the alternative is an
      ;; empty namespace and a reference to it that fails somewhere else later.
      (if (env/declared? cenv ns-sym)
        (update state :done conj ns-sym)

        ;; A CLOSURE-STYLE JAVASCRIPT FILE ON THE CLASSPATH is the other way there
        ;; is to be a namespace without a .cljs: com.cognitect.transit is
        ;; com/cognitect/transit.js in transit-js's jar, with a goog.provide at the
        ;; top of it. Nothing to compile - clojure.cljs.goog converts it, and
        ;; clojure.cljs.output/ensure-goog! writes it out with everything it
        ;; requires, at the end of the run and for the same reason the goog subset
        ;; is written then: what has to be on disk is decided by what was required.
        ;;
        ;; ASKED AFTER THE SOURCE PATH, which is the whole of how a .cljs wins over
        ;; a .js of the same name. The analyzer reaches the same conclusion from the
        ;; other side a moment later (analyzer/closure-ns?, which asks env/declared?
        ;; first) and can only do so because this marked the namespace done rather
        ;; than compiling something into it.
        (if (ana/closure-ns? cenv ns-sym)
          (update state :done conj ns-sym)

          ;; A JAVASCRIPT MODULE REQUIRED BY ITS BARE NAME - shadow-cljs's
          ;; spelling, (:require [react :as React]). Nothing to compile and
          ;; nothing to write: npm/ is built by a bundler out of node_modules,
          ;; and all this run owes it is the specifier, which the ns form's
          ;; analysis records a moment later (analyzer/js-module-ns?, which asks
          ;; the same question and can only answer because this got here).
          ;;
          ;; AFTER the source path and after the classpath, which is what makes
          ;; a name with a file behind it mean the file. It can never be confused
          ;; with the clojure.test fallback below: that one is about a DOTTED
          ;; name, and a dot is exactly what output/symbol-specifier refuses.
          (if (ana/js-module-ns? cenv ns-sym)
            (update state :done conj ns-sym)

            ;; clojure.test WITH NO FILE OF ITS OWN MEANS cljs.test, and it means it
            ;; here rather than at the ns form because this is where the evidence is:
            ;; the source paths are the driver's, and "there is no clojure.test" is a
            ;; statement about them. The analyzer reaches the same conclusion from what
            ;; it has analysed a moment later (analyzer/aliased-clj-ns), which it can
            ;; only do because this compiled the target first.
            ;;
            ;; Asked LAST, after the file and after declared?: a clojure.* namespace
            ;; that does exist is itself and nothing else, which is what keeps
            ;; clojure.string out of this.
            (let [alt (ana/clj-ns->cljs-ns ns-sym)]
              (if-let [src (and (not= alt ns-sym) (find-source (:source-paths opts) alt))]
                (-> (compile-one! cenv opts (update state :done conj ns-sym) src alt)
                    (update :compiled conj ns-sym))
                (throw (ex-info (str "Could not locate " (ns->source-path ns-sym ".cljs")
                                     (when (not= alt ns-sym)
                                       (str " or " (ns->source-path alt ".cljs")))
                                     " on the source path: "
                                     (str/join ", " (map str (:source-paths opts))))
                                {:ns ns-sym
                                 :source-paths (mapv str (:source-paths opts))}))))))))))

(def ^:private empty-state
  {:done #{} :visiting [] :compiled [] :written [] :scripts []})

(defn- data-reader-nss
  "The ClojureScript namespaces every data_readers.cljc on the classpath names, as
  far as this run can find sources for them.

  A DATA READER IS A DEPENDENCY OF THE PROGRAM, not of the namespace that uses the
  tag. cljs.reader's tag table holds a call to each registered reader, so those
  namespaces have to be loaded before cljs.reader's module body runs - and here a
  var is a property of a namespace object bound by an import (doc/cljs-compiler.md
  5.2), so `loaded` means an import in that module, which means compiled. Nothing
  in cljs/reader.cljs can say so: which namespaces they are is whatever the
  classpath registered. So the run compiles them, exactly as it compiles cljs.core
  whether or not an ns form says so.

  ClojureScript reaches the same place from the other end - cljs.closure's
  load-data-readers! is a build-level step too - and gets away with naming the
  functions as globals, because there a var IS a global path.

  A namespace with no ClojureScript source is skipped rather than refused. The
  reader that registered it may be a JVM one used only while compiling, which is
  what ClojureScript's own data_readers_test fixture is outside its test tree; the
  tag still reads at compile time, and a reference to it from the tag table gets
  the ordinary undeclared-ns warning."
  [opts]
  (into []
        (comp (map (comp symbol namespace))
              (distinct)
              (filter #(or (find-source (:source-paths opts) %)
                           (find-source (:source-paths opts) (ana/clj-ns->cljs-ns %)))))
        (map #(:sym (meta %)) (vals (reader/user-data-readers)))))

(defn- seed-state
  "empty-state, with every data-reader namespace already compiled into it."
  [cenv opts]
  (reduce #(ensure! cenv opts %1 %2) empty-state (data-reader-nss opts)))

(defn- run!*
  "Every entry point goes through here: normalise the options, make sure the output
  root exists, and put the namespace cursor back where it was.

  Restoring the cursor is not tidiness. Analysing a file runs its ns form, which
  moves the cursor by design - so without this, a REPL user typing (require 'foo)
  was silently moved into foo, and the next form they typed was compiled in the
  wrong namespace. Clojure's own load binds *ns* for the same reason.

  :static-dispatch is the one compilation option there is, and it is off unless a
  caller asks: a call site that names an arity is faster and does not survive the
  var being redefined without that arity, which is a trade a whole-program build
  can make and a reloadable file cannot (emitter/*static-dispatch*, §5.44)."
  [cenv opts f]
  (let [opts (assoc opts
                    :out-dir (io/file (:out-dir opts))
                    :source-paths (or (seq (:source-paths opts))
                                      (default-source-paths)))]
    (output/write-prelude! (:out-dir opts))
    ;; A CURSOR OF ITS OWN, borrowed from the caller's. Compiling a file runs its
    ;; (ns ...), which moves the cursor by design; binding rather than saving and
    ;; restoring means the move is discarded by the scope ending, so a require
    ;; typed at a REPL cannot silently move the user (repl-test).
    (env/with-current-ns env/*current-ns*
      (binding [emitter/*static-dispatch* (boolean (:static-dispatch opts))
                cgoog/*closure-library* (cgoog/library-option opts)]
        (let [result (select-keys (f opts) [:compiled :written :scripts])
              ;; THE BUNDLER'S INPUT, and the reason this is reported rather than
              ;; acted on. Everything else under the output root is written here;
              ;; npm/ is built by a bundler from node_modules, and
              ;; doc/cljs-advanced.md §3 says not to vendor one or make one
              ;; mandatory. So what crosses the line is this list and the mapping
              ;; beside it (clojure.cljs.output/js->path) - which is a better input
              ;; than scanning sources for string requires, because it is what the
              ;; compiler actually resolved rather than what a regex found.
              ;;
              ;; EVERY NAMESPACE IN THE ENVIRONMENT, for ensure-goog!'s reason
              ;; below: a compile env outlives an output directory, and a run that
              ;; compiled nothing still has to say what the program needs.
              js-req (into (sorted-set)
                           (mapcat #(env/js-requires
                                     cenv (.getName ^clojure.lang.Namespace %)))
                           (env/all-cljs-ns cenv))]
          ;; AFTER, not before: which Closure files have to be on disk is decided by
          ;; what was compiled, and the prelude runs before anything is. Every module
          ;; this run wrote imports its goog requires by path, so this is what makes
          ;; those paths resolve. See clojure.cljs.output/ensure-goog!.
          ;;
          ;; EVERY NAMESPACE IN THE ENVIRONMENT, not the ones this run compiled. A
          ;; compile env outlives an output directory - the same session compiles
          ;; into a fresh one every time a runtime is started - so a run that
          ;; compiled nothing because everything was already analysed still has to
          ;; fill a directory that has none of it. The set is small and the writes
          ;; are skipped when the files are already there.
          (output/ensure-goog! cenv (:out-dir opts)
                               (mapcat #(env/requires cenv (.getName ^clojure.lang.Namespace %))
                                       (env/all-cljs-ns cenv)))
          ;; and the one thing that can be said about npm/ from here: which of
          ;; those the bundler has not built yet. A warning rather than a failure,
          ;; because on a first build into a fresh directory every one of them is
          ;; missing - this run is what produced the list.
          (assoc result
                 :js-requires (vec js-req)
                 :js-missing  (output/report-missing-js! (:out-dir opts) js-req)))))))

(defn compile-namespace!
  "Compile `ns-sym` and everything it requires into an output directory.

    :out-dir          where the modules go; the prelude is written there too
    :source-paths     directories to look in, default default-source-paths
    :static-dispatch  compile a call to a var of known shape as a call to the arity
                      that answers it. Faster, and it does not survive a
                      redefinition that drops that arity - see run!*. Default off.

  Returns, for everything compiled and in the order it was compiled:

    :compiled  the namespaces
    :written   the files that actually changed on disk
    :scripts   [ns script] pairs - each namespace's body as the REPL would ship it,
               which is the same body the module holds under the other prologue

  And one thing that is about the whole environment rather than this run:

    :js-requires  every specifier a string require named, sorted - what a bundler
                  has to build npm/ out of. See run!*.
    :js-missing   those of them that are not under npm/ yet, which is a 404 waiting
                  to happen and is warned about besides"
  [cenv ns-sym opts]
  (run!* cenv opts #(ensure! cenv % (seed-state cenv %) ns-sym)))

(defn compile-file!
  "compile-namespace! for a file named rather than looked up - what load-file
  needs. The namespace comes from the file's own ns form, and its dependencies are
  still resolved by name on the source path."
  [cenv path opts]
  (let [^File src (io/file path)]
    (when-not (.isFile src)
      (throw (ex-info (str "No such file: " src) {:path (str src)})))
    (run!* cenv opts #(compile-one! cenv % (seed-state cenv %) src nil))))
