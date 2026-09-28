;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "In-memory semantic model of the ClojureScript this compiler compiled:
  var usages and definitions, local bindings and their uses, keyword
  occurrences, macro calls, references to the host (JavaScript globals, JS
  modules, Closure namespaces), and the compile-time dependency of a form on every
  macro it expanded - with precise source spans, across files. And the lints those
  add up to, read against the namespace state the ns forms left in the compile
  environment: unused aliases, refers, imports and macro requires.

  THE SAME MODEL AS replique-clj's clojure.analysis, and a separate one. Same
  shape - a log of top-level forms, each carrying the facts it produced, filed
  under the file it came from; query indexes derived from the log on demand and
  cached - and the same rules: a file commits all at once when it compiles to the
  end, and a file that throws keeps whatever it had before. Separate because the
  two cannot share keys: a .cljc file is both a Clojure load and a ClojureScript
  compile under one path, and cljs.core/+ is both a JVM macro and a ClojureScript
  function under one name.

  FED BY AN AST WALK, not by taps in the analyzer. The analyzer already builds a
  tree whose every node declares its children (clojure.cljs.ast), and the reader
  already hangs a position on every symbol it reads (clojure.cljs.reader binds
  Compiler/RECORD_POSITIONS) - so what Clojure had to patch into its compiler is
  here a walk over what analyze-top returns. The driver brackets files and forms
  through clojure.cljs.driver/*sink*, which run-analysis binds.

  THE CAPTURE RULE is clojure.analysis's: a usage is recorded where the name is
  written. A symbol the reader read carries a :line; one a macro made up does not.
  A keyword carries nothing - it cannot hold metadata - so keywords are the one
  fact taken from the READER rather than the AST: the driver binds a sink around
  each form's read (clojure.cljs.reader/*analysis-sink*), and the reader reports
  every keyword it reads, auto-resolved ones (::x, ::alias/x) fully qualified in
  the ClojureScript namespace being compiled. Macro expansions are the other fact
  the AST cannot hold - a call is gone before a node is built - and come from a
  hook in clojure.cljs.macroexpand (*on-expand*), which run-analysis binds.

  DISK ONLY. Nothing typed at a REPL reaches the model - the REPL does not go
  through the driver's file loop - so it stays in step with what is on disk.

  cljs.core IS NOT ANALYSED, as clojure.core is not analysed on the JVM (it loads
  AOT and never passes the sink). Uses of its vars from analysed files are
  recorded like any other; its own definitions are not, so `definition` of a core
  var is nil, and the var's own :file / :line metadata is where to look instead.

  The reload unit is the FILE, keyed by the label the driver gives it - the path
  under its source directory, my_lib/core.cljs, which is also what a var's :file
  records. Each form keeps the namespace it was compiled in as :ns.

  STALENESS, as clojure.analysis has it and for the same reason: a file changed on
  disk since it was compiled is stale, and so is a file that expanded a macro
  whose Clojure file changed since - the one kind of compile-time dependency a
  ClojureScript file has. stale-reload! recompiles them, reloading the macro files
  on the JVM first, and hands back the scripts a runtime needs.

  Drivers: run-analysis, load-file!, retract-file!, reset-model!, stale-reload!,
  prune-file!. Queries: find-usages, definition, find-keyword-usages,
  find-macro-usages, find-host-usages, macro-deps, ns-referenced-namespaces,
  unused-locals, unused-aliases, unused-refers, unused-imports,
  unused-macro-aliases, unused-macro-refers, changed-files, stale-macro-files,
  stale-files, meta-stale-files, deleted-files, file-def-vars,
  file-def-var-snapshot, file-forms, file-namespaces, ns-forms, snapshot."
      :author "replique-cljs"}
    clojure.cljs.analysis
  (:require [clojure.analysis :as clj-analysis]
            [clojure.cljs.ast :as ast]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.cljs.macroexpand :as mx]
            [clojure.java.io :as io])
  (:import [clojure.lang IAnalysisSink Keyword Namespace RT Var]
           [java.io File]
           [java.net URL]
           [java.util ArrayList]))

;; stored (write model - mutated only by commit-frame! and retraction):
;;   :forms          {fid {:ns :source :line :column + one key per non-empty fact
;;                         category: :usages :defs :locals :local-uses
;;                         :keyword-usages :macro-usages :macro-deps
;;                         :host-usages :var-meta-deps}}
;;                   :var-meta-deps is [qsym key value]: a var's metadata the
;;                   compile of the form read (see record-meta-deps!)
;;   :source->forms  {source #{fid}}
;;   :locations      {source File-or-URL}  where each file was last found
;;   :file-mtime     {source long-or-nil}  its mtime when it was last compiled; nil
;;                                         for one that is not a file (a jar entry)
;;   :macro-files    {source {resource long}}  the Clojure files of the macros it
;;                                         expanded, and the mtime of the version
;;                                         the JVM had loaded then (:macro-loaded)
;;   :macro-loaded   {resource long}       the mtime of the version of a macro file
;;                                         the JVM has loaded, as far as this model
;;                                         knows: taken the first time a file
;;                                         expands one of its macros, advanced only
;;                                         when stale-reload! loads it again
;;   :pending-macro-files #{resource}     macro files a stale-reload! set out to
;;                                         load and has not loaded yet
;;   :pending-sources #{source}           files a stale-reload! set out to
;;                                         recompile and has not committed yet -
;;                                         so a reload that throws half way loses
;;                                         no staleness the cascade had found
;;   :next-fid       long
;; derived (build-index, cached by :forms identity):
;;   :usages         {qsym #{span}}
;;   :defs           {qsym {:span span}}   only vars a live form defines
;;   :locals         {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages {kw #{span}}
;;   :macro-usages   {macro-qsym #{span}}   a macro is a JVM var: its qsym names a
;;                                          Clojure namespace, so this is kept apart
;;                                          from :usages, whose keys are
;;                                          ClojureScript vars - cljs.core/str is both
;;   :macro-deps     {ns-sym {macro-qsym #{fid}}}
;;   :host-usages    {host-ref #{span}}   host-ref is a map - see host-ref
(def ^:private empty-model
  {:forms {} :source->forms {} :locations {} :file-mtime {} :macro-files {}
   :macro-loaded {} :pending-macro-files #{} :pending-sources #{} :next-fid 0})

(defonce ^:private model (atom empty-model))

;; A usage/def span, as clojure.analysis has it: primitive coordinates, an absent
;; end stored as -1, and `entity` - the var key the span is about - carried on the
;; span so a fact is one object. from-ns is a namespace SYMBOL here (a
;; ClojureScript namespace is not something to hold on to); nil for a def.
(defrecord Span [entity source ^int line ^int column ^int end-line ^int end-column from-ns])

(defn- norm-pos [x] (if (nat-int? x) (int x) -1))

(defn- span [entity source line column el ec from-ns]
  (->Span entity source (norm-pos line) (norm-pos column) (norm-pos el) (norm-pos ec)
          from-ns))

(defn- span->map [s]
  (cond-> {:source (:source s) :line (:line s) :column (:column s)}
    (nat-int? (:end-line s))   (assoc :end-line (:end-line s))
    (nat-int? (:end-column s)) (assoc :end-column (:end-column s))
    (:from-ns s)               (assoc :from-ns (:from-ns s))))

(defn- spans->maps [spans]
  (when spans (into #{} (map span->map) spans)))

(defrecord LocalSpan [binding source ^int line ^int column ^int end-line ^int end-column lns lname])

(defn- local->map
  "A LocalSpan as the plain map the :locals index holds - clojure.analysis's
  shape, :name omitted for a use."
  [l]
  (cond-> {:source (:source l) :line (:line l) :column (:column l) :ns (:lns l)}
    (nat-int? (:end-line l))   (assoc :end-line (:end-line l))
    (nat-int? (:end-column l)) (assoc :end-column (:end-column l))
    (:lname l)                 (assoc :name (:lname l))))

(defn- jvm-var-key
  "A macro's model key: the fully-qualified name of the JVM var it is."
  [^Var v]
  (symbol (str (.getName (.ns v))) (str (.sym v))))

(defn- var-key
  "A ClojureScript var's model key: its fully-qualified name symbol. nil for a var
  in no namespace, so a lookup misses rather than throws."
  [^Var v]
  (when-let [ns (.ns v)]
    (symbol (str (.getName ns)) (str (.sym v)))))

;; --- frames -------------------------------------------------------------------

(def ^:private ^:const CAT-USAGES   0)
(def ^:private ^:const CAT-DEFS     1)
(def ^:private ^:const CAT-LOCALS   2)
(def ^:private ^:const CAT-LOCALUSE 3)
(def ^:private ^:const CAT-KEYWORDS 4)
(def ^:private ^:const CAT-MACROUSE 5)
(def ^:private ^:const CAT-MACRODEP 6)
(def ^:private ^:const CAT-HOST     7)
(def ^:private ^:const CAT-METADEP  8)
(def ^:private ^:const N-CATS       9)

(def ^:private cat-keys
  [:usages :defs :locals :local-uses :keyword-usages :macro-usages :macro-deps
   :host-usages :var-meta-deps])

;; A form being compiled. `pos` is [line column], corrected by form-start once the
;; form has been read; `cats` holds one ArrayList per fact category, made on first use.
(deftype OpenForm [^long seq ^longs pos ^objects cats])

;; A file being compiled. `ignored` is cljs.core's frame, which is pushed like any
;; other - so a form's facts always land in the frame of the file it belongs to -
;; and whose facts go nowhere. `forms` is the stack of open forms, `buffer` the
;; finished ones, `counter` the next begin-order rank.
(deftype FileFrame [source location mtime ignored ^ArrayList forms ^ArrayList buffer
                    ^longs counter])

;; --- where a file is, and when it changed ------------------------------------

(defn- url->file
  "The File a file: URL points at - through toURI, which decodes %20, and falling
  back to the raw path for a URL a classloader built with a literal space in it,
  which toURI refuses (clojure.analysis/resource->file)."
  ^File [^URL u]
  (try (File. (.toURI u))
       (catch java.net.URISyntaxException _ (File. (.getPath u)))))

(defn- location-file
  "The File behind a location - a File, a URL or a classpath resource path - or nil
  when it is not a file on disk (a jar entry, nothing at all)."
  ^File [loc]
  (let [loc (if (string? loc) (io/resource loc) loc)]
    (cond (instance? File loc) loc
          (and (instance? URL loc) (= "file" (.getProtocol ^URL loc))) (url->file loc))))

(defn- mtime
  "The modification time of the file behind `loc`, or nil when there is none."
  [loc]
  (when-let [f (location-file loc)]
    (when (.isFile f) (.lastModified f))))

(defn- peek-list [^ArrayList l]
  (when-not (.isEmpty l) (.get l (dec (.size l)))))

(defn- pop-list! [^ArrayList l]
  (.remove l (int (dec (.size l)))))

(defn- open-form
  "The form facts go to: the innermost open form of the innermost file, or nil when
  there is none, or when that file is one whose facts are not kept."
  ^OpenForm [^ArrayList files]
  (when-let [^FileFrame fr (peek-list files)]
    (when-not (.ignored fr)
      (peek-list (.forms fr)))))

(defn- add-fact! [^OpenForm of ^long cat fact]
  (let [^objects cats (.cats of)]
    (if-let [^ArrayList l (aget cats cat)]
      (.add l fact)
      (aset cats cat (doto (ArrayList.) (.add fact))))))

;; --- facts, from the AST ------------------------------------------------------

(defn- written-at
  "The reader's position for `form`, or nil when the reader did not read it - which
  is the capture rule: a macro's own symbols carry no :line.

  Or the position it was rebuilt from: the Foo of (Foo. x) is made by
  macroexpand's host sugar, which records where Foo. was written under a key of
  its own (see host-sugar for why not as :line)."
  [form]
  (let [m (meta form)]
    (if (:line m) m (:clojure.cljs.macroexpand/written m))))

(defn- record-def! [^OpenForm of source var-node]
  (let [^longs pos (.pos of)
        m (or (written-at (:form var-node))
              {:line (aget pos 0) :column (aget pos 1)})]
    (add-fact! of CAT-DEFS (span (:name var-node) source (:line m) (:column m)
                                 (:end-line m) (:end-column m) nil))))

(defn- record-usage! [^OpenForm of source from-ns node]
  (when-let [m (written-at (:form node))]
    (add-fact! of CAT-USAGES (span (:name node) source (:line m) (:column m)
                                   (:end-line m) (:end-column m) from-ns))))

(defn- record-meta-deps!
  "The var's metadata the emitted code was built from - a compile-time dependency
  on the file that defines the var, which a run-time lookup does not undo.

    :tag      (def ^boolean x ...): an if on x skips the truth_ check
    :ret-tag  (defn ^boolean f ...): an if on (f ...) does too
    :top-fn   the arities; a call site dispatches straight to one - only when
              emitter/*static-dispatch* is on, which is the only time it is read

  Every :var node, written or not: a macro's expansion is compiled against the
  same metadata. Only what is there: a tag or arity ADDED later leaves the code
  correct, merely unoptimised; one changed or removed does not."
  [^OpenForm of node]
  (let [q (:name node)]
    (when-some [t (:tag node)] (add-fact! of CAT-METADEP [q :tag t]))
    (when-some [t (:ret-tag node)] (add-fact! of CAT-METADEP [q :ret-tag t]))
    (when (and emitter/*static-dispatch* (:top-fn node))
      (add-fact! of CAT-METADEP [q :top-fn (:top-fn node)]))))

;; A local's identity is its JavaScript name within its file: clojure.cljs.names
;; numbers every binding of a file from one counter (the driver compiles a file
;; inside one name scope), so [source js-name] names exactly one binding, and a
;; use carries the js-name of the binding it resolved to.

(defn- record-local! [^OpenForm of source ns node]
  (let [sym (:form node)]
    ;; a symbol the source wrote - not a macro's gensym, and not the try form a
    ;; catch's own binding hangs off
    (when-let [m (and (symbol? sym) (written-at sym))]
      (add-fact! of CAT-LOCALS
                 (->LocalSpan [source (:js-name node)] source
                              (norm-pos (:line m)) (norm-pos (:column m))
                              (norm-pos (:end-line m)) (norm-pos (:end-column m))
                              ns (:name node))))))

(defn- record-local-use! [^OpenForm of source ns js-name m]
  (when m
    (add-fact! of CAT-LOCALUSE
               (->LocalSpan [source js-name] source
                            (norm-pos (:line m)) (norm-pos (:column m))
                            (norm-pos (:end-line m)) (norm-pos (:end-column m))
                            ns nil))))

(defn- host-ref
  "What a reference to the host names, as a map, or nil for a node that is not one.

    {:kind :global    :name Foo}                     js/Foo, or a :refer-global
    {:kind :goog-var  :name goog.string/trim}        a var in a Closure namespace
    {:kind :goog-ns   :name goog.math.Long}          a Closure namespace as a value
    {:kind :js-module :specifier \"react\"}           a JS module object
    {:kind :js-module :specifier \"react\" :export \"useState\"}   one of its exports

  plus :written, the symbol the source wrote, without its metadata. That is what
  tells an alias from a refer when both reach the same export - React/useState and
  a :referred useState are one export and two names - which is the question the
  unused-* lints ask."
  [n]
  (when-let [r (case (:op n)
                 :js-var        {:kind :global :name (:name n)}
                 :goog-var      {:kind :goog-var :name (:name n)}
                 :goog-ns       {:kind :goog-ns :name (:name n)}
                 :js-module     {:kind :js-module :specifier (:specifier n)}
                 :js-module-var {:kind :js-module :specifier (:specifier n)
                                 :export (:export n)}
                 nil)]
    (cond-> r (symbol? (:form n)) (assoc :written (with-meta (:form n) nil)))))

(defn- record-host! [^OpenForm of source ns node]
  (when-let [m (written-at (:form node))]
    (add-fact! of CAT-HOST (span (host-ref node) source (:line m) (:column m)
                                 (:end-line m) (:end-column m) ns))))

(defn- record-facts!
  "Walk one top-level form's AST into the open form.

  A :def and a :deftype each hold the var they define as a :var CHILD, which is a
  definition and not a use of it - so that child is recorded as the def and not
  walked.

  (def f (fn* ...)) gives the fn a :binding named f that is no local at all - it
  names the emitted JavaScript function and is in nobody's scope (analyzer's
  name-defd-fn) - and it is built from the def's own name symbol, position and
  all. Such a binding is skipped by that identity.

  A deftype field is read through a rewrite, (. self -x) (analyzer's
  analyze-symbol), whose form remembers the field under ::field-of."
  [^OpenForm of source ns node]
  (let [def-names (java.util.IdentityHashMap.)]
    (letfn [(visit [n]
              (case (:op n)
                (:def :deftype)
                (let [v (:var n)]
                  (record-def! of source v)
                  (.put def-names (:form v) true)
                  (doseq [c (ast/children n) :when (not (identical? c v))]
                    (visit c)))

                :var (do (record-usage! of source ns n)
                         (record-meta-deps! of n))

                :binding
                (do (when-not (.containsKey def-names (:form n))
                      (record-local! of source ns n))
                    (run! visit (ast/children n)))

                :local (record-local-use! of source ns (:js-name n) (written-at (:form n)))

                :host-field
                (let [m (meta (:form n))]
                  (when-let [js (:clojure.cljs.analyzer/field-of m)]
                    (record-local-use! of source ns js (written-at (:form n))))
                  (run! visit (ast/children n)))

                (:js-var :goog-var :goog-ns :js-module :js-module-var)
                (record-host! of source ns n)

                (run! visit (ast/children n))))]
      (visit node))))

;; --- commit -------------------------------------------------------------------

(defn- drop-empty [m idx k]
  (if (empty? (get-in m [idx k])) (update m idx dissoc k) m))

(defn- retract-form [m fid]
  (if-let [fe (get-in m [:forms fid])]
    (let [m (update m :forms dissoc fid)]
      (if-let [src (:source fe)]
        (-> m (update-in [:source->forms src] disj fid) (drop-empty :source->forms src))
        m))
    m))

(defn- macro-files
  "The Clojure files the macros a file's forms expanded were loaded from, each with
  the mtime of the version the JVM has loaded (`loaded`, :macro-loaded) - not the
  one on disk now, which the JVM may not have loaded: a macro file edited, or
  changed by a branch switch, and not loaded since, still expands its old macros.
  A file this model has not seen before is taken to be loaded as it is on disk.
  A macro whose var has no :file on the classpath (one defined at a REPL) has no
  file to go stale."
  [loaded buffer]
  (into {} (for [fe buffer
                 [_ _ file] (:macro-deps fe)
                 :when file
                 :let [t (or (get loaded file) (mtime file))]
                 :when t]
             [file t])))

(defn- commit-frame!
  "Install a whole file's forms in one swap!, replacing that file's prior forms -
  clojure.analysis/commit-frame!, whose docstring has the argument."
  [^FileFrame fr]
  (let [source      (.source fr)
        ^ArrayList buffer (.buffer fr)
        begin-count (aget ^longs (.counter fr) 0)]
    ;; nothing to add and nothing to replace leaves :forms identical, and with it
    ;; the derived-index cache
    (when (or (pos? (.size buffer))
              (seq (get-in @model [:source->forms source])))
      (swap! model
             (fn [m]
               (let [m     (reduce retract-form m (get-in m [:source->forms source]))
                     base  (long (:next-fid m))
                     fid   #(+ base (long (:seq %)))
                     forms (persistent!
                            (reduce (fn [t fe] (assoc! t (fid fe) (dissoc fe :seq)))
                                    (transient (:forms m)) buffer))
                     s->f  (reduce (fn [s2f fe] (update s2f source (fnil conj #{}) (fid fe)))
                                   (:source->forms m) buffer)]
                 (assoc m :forms forms :source->forms s->f
                          :next-fid (+ base (long begin-count)))))))
    (swap! model
           (fn [m]
             (let [mfiles (macro-files (:macro-loaded m) buffer)]
               (-> m
                   (assoc-in [:locations source] (.location fr))
                   (assoc-in [:file-mtime source] (.mtime fr))
                   (assoc-in [:macro-files source] mfiles)
                   (update :pending-sources disj source)
                   ;; the files seen for the first time: merge keeps a baseline
                   ;; already there, which only a reload advances
                   (update :macro-loaded #(merge mfiles %))))))
    nil))

(defn- def-echo?
  "Is `s` a usage sitting exactly on one of `defs`? A macro that defines a name
  often writes that same symbol again in its expansion - deftype hands the type's
  name to the code that extends it - and the copy carries the reader's position,
  so it passes the capture rule. It is the definition seen twice, not a use."
  [defs ^Span s]
  (contains? defs [(.entity s) (.line s) (.column s)]))

(defn- remove-if! [^ArrayList l pred]
  (when l
    (.removeIf l (reify java.util.function.Predicate (test [_ x] (boolean (pred x)))))))

(defn- freeze-form
  "An open form as a model entry, or nil when it recorded nothing.

  Echoes are dropped first. A var usage lying on a def of the same var is the
  definition seen twice (def-echo?). A local use lying on ANY binding's position is
  too, for the same reason: a macro writes a binding's symbol again into code it
  generates - defrecord reads every field back in its lookup - and nothing a
  program writes can use a local exactly where a local is bound."
  [^OpenForm of source]
  (let [^objects cats (.cats of)
        ^longs pos    (.pos of)
        defs (into #{} (map (fn [^Span s] [(.entity s) (.line s) (.column s)]))
                   (aget cats CAT-DEFS))
        _    (when (seq defs)
               (remove-if! (aget cats CAT-USAGES) #(def-echo? defs %)))
        bound (into #{} (map (fn [^LocalSpan l] [(.line l) (.column l)]))
                    (aget cats CAT-LOCALS))
        _    (when (seq bound)
               (remove-if! (aget cats CAT-LOCALUSE)
                           (fn [^LocalSpan l] (contains? bound [(.line l) (.column l)]))))
        fe (reduce (fn [fe i]
                     (let [^ArrayList l (aget cats (long i))]
                       (if (and l (not (.isEmpty l)))
                         (assoc fe (nth cat-keys i)
                                ;; one edge per macro per form: a form expanding
                                ;; `when` a hundred times depends on it once
                                (if (or (= i CAT-MACRODEP) (= i CAT-METADEP))
                                  (vec (distinct l))
                                  (vec l)))
                         fe)))
                   nil (range N-CATS))]
    (when fe
      (assoc fe :seq (.seq of) :source source
                :line (aget pos 0) :column (aget pos 1)
                ;; after the form, so an (ns ...) files under the ns it made
                :ns env/*current-ns*))))

;; --- the sink -----------------------------------------------------------------

;; What the reader reports to while it reads a form of an analysed file. It is a
;; clojure.lang.IAnalysisSink because the reader is Clojure's and speaks only that;
;; of everything the interface carries, a ClojureScript read produces keywords and
;; syntax-quote references, and the second are dropped: LispReader resolves them
;; against the JVM's namespaces (Compiler.sinkSyntaxQuoteRef), not this world's.
;; Its source and namespace arguments are the JVM's too, so the file's label and
;; env/*current-ns* stand in for them.
(deftype ReaderSink [^ArrayList files]
  IAnalysisSink
  (beginFile [_ _])
  (endFile [_ _])
  (beginForm [_ _ _ _])
  (formStart [_ _ _])
  (endForm [_])
  (varUsage [_ _ _ _ _ _ _ _])
  (varDef [_ _ _ _ _ _ _])
  (localDef [_ _ _ _ _ _ _ _ _])
  (localUsage [_ _ _ _ _ _ _ _])
  (classUsage [_ _ _ _ _ _ _ _])
  (macroExpansion [_ _ _ _ _ _ _ _ _])
  (keywordUsage [_ kw _ _ line column el ec]
    ;; the branch of a reader conditional this platform does not take is read with
    ;; *suppress-read* on - it is another platform's code, not this program's. A #_
    ;; discard is read normally and IS recorded: it is still written in the file.
    (when-let [of (and (not (RT/suppressRead)) (open-form files))]
      (add-fact! of CAT-KEYWORDS
                 (span kw (.source ^FileFrame (peek-list files)) line column el ec
                       env/*current-ns*)))))

(defn- on-expand
  "The macroexpand hook for one run: every expansion inside an open form is an edge
  from the namespace being compiled to the macro, and a call the source wrote -
  its symbol carries the reader's position - is a use of the macro too."
  [^ArrayList files]
  (fn [^Var v op]
    (when-let [of (open-form files)]
      (let [k  (jvm-var-key v)
            ns env/*current-ns*]
        (add-fact! of CAT-MACRODEP [ns k (:file (meta v))])
        (when-let [m (written-at op)]
          (add-fact! of CAT-MACROUSE
                     (span k (.source ^FileFrame (peek-list files)) (:line m) (:column m)
                           (:end-line m) (:end-column m) ns)))))))

;; One per run-analysis. `files` is the stack of files being compiled; it is touched
;; only by the thread the compilation runs on, which is the thread that bound it.
(deftype AnalysisSink [^ArrayList files reader]
  driver/CompileSink
  (reader-sink [_] reader)
  (begin-file [_ ns-sym source location]
    (.add files (FileFrame. source location (mtime location) (= 'cljs.core ns-sym)
                            (ArrayList.) (ArrayList.) (long-array 1)))
    nil)
  (begin-form [_]
    (when-let [^FileFrame fr (peek-list files)]
      (let [^longs c (.counter fr)
            rank     (aget c 0)]
        (aset c 0 (inc rank))
        (.add ^ArrayList (.forms fr) (OpenForm. rank (long-array [-1 -1]) (object-array N-CATS)))))
    nil)
  (form-start [_ line column]
    (when-let [^FileFrame fr (peek-list files)]
      (when-let [^OpenForm of (peek-list (.forms fr))]
        (aset ^longs (.pos of) 0 (long line))
        (aset ^longs (.pos of) 1 (long (or column -1)))))
    nil)
  (analyzed [_ node]
    (when-let [of (open-form files)]
      (record-facts! of (.source ^FileFrame (peek-list files)) env/*current-ns* node))
    nil)
  (end-form [_]
    (when-let [^FileFrame fr (peek-list files)]
      (when-let [of (peek-list (.forms fr))]
        (pop-list! (.forms fr))
        (when-not (.ignored fr)
          (when-let [fe (freeze-form of (.source fr))]
            (.add ^ArrayList (.buffer fr) fe)))))
    nil)
  (end-file [_ _source]
    (when-let [^FileFrame fr (peek-list files)]
      (pop-list! files)
      (when-not (.ignored fr)
        (commit-frame! fr)))
    nil)
  (abort-file [_ _source]
    ;; its open forms go with it: they are on the frame, not beside it
    (when-not (.isEmpty files)
      (pop-list! files))
    nil))

;; --- drivers ------------------------------------------------------------------

(defn reset-model!
  "Clear the whole model."
  []
  (reset! model empty-model)
  nil)

(defn run-analysis
  "Invoke `thunk` with the analysis sink installed on this thread, so every file the
  driver compiles in it - compile-namespace!, compile-file!, a REPL's require -
  replaces its own slice of the model as it finishes. Returns the thunk's value.

  What is ALREADY COMPILED is not compiled again (clojure.cljs.driver/ensure!), and
  so is not analysed either: a namespace compiled into the environment before
  analysis was on reaches the model only when something compiles it again -
  :reload / :reload-all, or load-file!."
  [thunk]
  (let [files (ArrayList.)]
    (binding [driver/*sink*     (->AnalysisSink files (->ReaderSink files))
              mx/*on-expand* (on-expand files)]
      (thunk))))

(defn load-file!
  "Compile the file at `path` under the sink - clojure.cljs.driver/compile-file!,
  whose options these are - replacing that file's forms in the model. A file that
  fails to compile keeps its prior forms. Returns the driver's result."
  [cenv path opts]
  (run-analysis #(driver/compile-file! cenv path opts)))

(defn retract-file!
  "Remove every form of file `source` (its label, e.g. \"app/util.cljs\") from the
  model, and its staleness baselines with it. Other files' usages of its vars are
  theirs, and stay."
  [source]
  (swap! model (fn [m] (-> (reduce retract-form m (get-in m [:source->forms source]))
                           (update :locations dissoc source)
                           (update :file-mtime dissoc source)
                           (update :macro-files dissoc source)
                           (update :pending-sources disj source))))
  nil)

;; --- derived indexes ------------------------------------------------------------

(defn- cached-by-forms
  "What `build` computes from the form log, recomputed only when `forms` is not the
  log `cache` holds a value for - clojure.analysis/cached-by-forms."
  [cache forms build]
  (let [c @cache]
    (if (identical? forms (:forms c))
      (:value c)
      (let [built (build)]
        (reset! cache {:forms forms :value built})
        built))))

(defonce ^:private index-cache (atom {:forms nil :value nil}))

(defn- build-index
  "Replay the form log, in fid order, into the by-entity indexes. A later def of the
  same var overwrites the earlier one, so the highest fid wins."
  [forms]
  (let [idx (reduce
             (fn [idx fid]
               (let [fe (get forms fid)]
                 (as-> idx idx
                   (reduce (fn [idx ^Span s]
                             (let [sub (get idx :usages)
                                   e   (.entity s)]
                               (assoc! idx :usages (assoc! sub e (conj (get sub e #{}) s)))))
                           idx (:usages fe))
                   (reduce (fn [idx ^Span s]
                             (assoc! idx :defs (assoc! (get idx :defs) (.entity s) {:span s})))
                           idx (:defs fe))
                   ;; bindings before their uses: a local is scoped to its form
                   (reduce (fn [idx ^LocalSpan l]
                             (let [sub (get idx :locals)
                                   b   (.binding l)]
                               (assoc! idx :locals
                                       (assoc! sub b (assoc (local->map l)
                                                            :uses (get (get sub b) :uses #{}))))))
                           idx (:locals fe))
                   (reduce (fn [idx ^LocalSpan l]
                             (let [sub (get idx :locals)
                                   b   (.binding l)]
                               (if-let [cur (get sub b)]
                                 (assoc! idx :locals
                                         (assoc! sub b (update cur :uses conj (local->map l))))
                                 idx)))
                           idx (:local-uses fe))
                   (reduce (fn [idx ^Span s]
                             (let [sub (get idx :keyword-usages)
                                   e   (.entity s)]
                               (assoc! idx :keyword-usages
                                       (assoc! sub e (conj (get sub e #{}) s)))))
                           idx (:keyword-usages fe))
                   (reduce (fn [idx ^Span s]
                             (let [sub (get idx :macro-usages)
                                   e   (.entity s)]
                               (assoc! idx :macro-usages
                                       (assoc! sub e (conj (get sub e #{}) s)))))
                           idx (:macro-usages fe))
                   ;; the edge carries its form's fid, which is its file
                   (reduce (fn [idx [n mk]]
                             (let [sub (get idx :macro-deps)]
                               (assoc! idx :macro-deps
                                       (assoc! sub n (update (get sub n {}) mk
                                                             (fnil conj #{}) fid)))))
                           idx (:macro-deps fe))
                   (reduce (fn [idx ^Span s]
                             (let [sub (get idx :host-usages)
                                   e   (.entity s)]
                               (assoc! idx :host-usages
                                       (assoc! sub e (conj (get sub e #{}) s)))))
                           idx (:host-usages fe)))))
             (transient {:usages (transient {}) :defs (transient {}) :locals (transient {})
                         :keyword-usages (transient {}) :macro-usages (transient {})
                         :macro-deps (transient {}) :host-usages (transient {})})
             (sort (keys forms)))]
    (reduce-kv (fn [m k v] (assoc m k (persistent! v))) {} (persistent! idx))))

(defn- derived [m]
  (let [forms (:forms m)]
    (cached-by-forms index-cache forms #(build-index forms))))

;; --- queries --------------------------------------------------------------------

(defn- ->var-key [var-or-sym]
  (cond
    (instance? Var var-or-sym) (var-key var-or-sym)
    (qualified-symbol? var-or-sym) var-or-sym
    :else (throw (IllegalArgumentException.
                  (str "find-usages/definition expect a Var or fully-qualified symbol, got: "
                       (pr-str var-or-sym))))))

(defn find-usages
  "Usage sites recorded for a var - its fully-qualified name symbol, or the
  ClojureScript Var itself. A set of {:from-ns :source :line :column :end-line
  :end-column}."
  [var-or-sym]
  (spans->maps (get (:usages (derived @model)) (->var-key var-or-sym))))

(defn definition
  "Definition site recorded for a var, or nil - nil too for a var no live form
  defines (deleted from its file, or in a file never analysed, cljs.core's among
  them)."
  [var-or-sym]
  (some-> (:span (get (:defs (derived @model)) (->var-key var-or-sym))) span->map))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword `kw`. An auto-resolved keyword is recorded
  fully qualified, so ::x in app.core is found as :app.core/x."
  [^Keyword kw]
  (spans->maps (get (:keyword-usages (derived @model)) kw)))

(defn find-macro-usages
  "Where the source calls macro `macro` - the JVM Var, or its fully-qualified name
  symbol. A set of spans shaped like find-usages'.

  Only calls the source WROTE: a macro called by another macro's expansion is a
  dependency (macro-deps) and not a use. Uses of the same name as a VALUE -
  cljs.core/str passed to map rather than called - are the ClojureScript var's,
  and find-usages has them."
  [macro]
  (spans->maps (get (:macro-usages (derived @model))
                    (if (instance? Var macro) (jvm-var-key macro) macro))))

(defn macro-deps
  "The compile-time dependency of ClojureScript namespaces on macros: every macro
  expanded while compiling them, whether the source called it or another macro's
  expansion did. No argument: {ns-sym #{macro-qsym}}. With a namespace symbol: the
  set for that namespace."
  ([] (reduce-kv (fn [acc n mm] (assoc acc n (set (keys mm))))
                 {} (:macro-deps (derived @model))))
  ([ns-sym] (set (keys (get (:macro-deps (derived @model)) ns-sym)))))

(defn unused-locals
  "Local bindings the source wrote and nothing uses, optionally only those of
  namespace `ns-sym`. Each is the binding's site plus :name and :ns.

  A SITE, NOT A BINDING. A macro may bind one written symbol more than once - a
  variadic defn's parameters are bound by each function it expands to - and a
  binding the macro never reads is not the programmer's to remove while another
  one at the same place is read. So a site is unused only when every binding
  written there is."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ infos] (group-by (juxt :source :line :column)
                             (vals (:locals (derived @model))))
         :let  [info (first infos)]
         :when (every? (comp empty? :uses) infos)
         :when (or (nil? ns-sym) (= ns-sym (:ns info)))]
     (dissoc info :uses))))

(defn find-host-usages
  "Where the source refers to the host thing `ref` describes: a map in host-ref's
  shape, matched on the keys it gives. {:kind :js-module :specifier \"react\"} is
  every use of that module through any name; add :export for one export, or
  :written for one spelling of it."
  [ref]
  (into #{}
        (comp (filter (fn [[k _]] (= ref (select-keys k (keys ref)))))
              (mapcat val)
              (map span->map))
        (:host-usages (derived @model))))

;; --- namespace lints ------------------------------------------------------------
;;
;; clojure.analysis reads live namespace state for these, and so do they - but a
;; ClojureScript namespace lives in a compile environment rather than in the JVM,
;; so each takes the environment. What a namespace's ns form ESTABLISHED comes from
;; there; what its code USES comes from the model. Both are about the last compile:
;; a file edited since is answered as it was.

(defn- from-ns? [ns-sym ^Span s] (= ns-sym (.from-ns s)))

(defn- used-from
  "The keys of index `m` with at least one span from `ns-sym`."
  [m ns-sym]
  (for [[k spans] m :when (some #(from-ns? ns-sym %) spans)] k))

(defn- written-from
  "Every symbol `ns-sym` wrote to reach the host - see host-ref's :written."
  [idx ns-sym]
  (into #{} (keep :written) (used-from (:host-usages idx) ns-sym)))

(defn- written-as?
  "Did one of the `written` symbols spell `nm` - bare, or as the namespace part of
  nm/member?"
  [written nm]
  (let [s (str nm)]
    (some #(or (= % nm) (= (namespace %) s)) written)))

(defn ns-referenced-namespaces
  "The namespaces `ns-sym` refers to, per the model: the namespace of every var,
  namespaced keyword and macro its source uses, and every Closure namespace it
  reaches. A macro's namespace is a JVM one - usually the ClojureScript namespace's
  own name, which is what a .cljc library requiring itself for its macros relies on."
  [ns-sym]
  (let [idx (derived @model)
        nss (fn [ks] (keep #(some-> (namespace %) symbol) ks))]
    (into #{}
          (concat (nss (used-from (:usages idx) ns-sym))
                  (nss (used-from (:keyword-usages idx) ns-sym))
                  (nss (used-from (:macro-usages idx) ns-sym))
                  (keep (fn [r] (case (:kind r)
                                  :goog-var (symbol (namespace (:name r)))
                                  :goog-ns  (:name r)
                                  nil))
                        (used-from (:host-usages idx) ns-sym))))))

(defn unused-aliases
  "Aliases in `ns-sym` nothing uses: {alias target}. A ClojureScript or Closure
  namespace alias is unused when nothing from its target namespace is referenced
  (ns-referenced-namespaces); a JavaScript module's alias when the source never
  writes it. The target is the namespace symbol, or the module's specifier - or
  [specifier path] for one that named a path into the module.

  The aliases an :import made are unused-imports', not these."
  [cenv ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns cenv ns-sym)]
    (let [used     (ns-referenced-namespaces ns-sym)
          written  (written-from (derived @model) ns-sym)
          imported (set (keys (env/imports cenv ns-sym)))]
      (merge
       (into {} (for [[a ^Namespace target] (.getAliases n)
                      :let  [t (.getName target)]
                      :when (not (imported a))
                      :when (not (used t))]
                  [a t]))
       (into {} (for [[a [specifier path]] (env/js-aliases cenv ns-sym)
                      :when (not (written-as? written a))]
                  [a (if path [specifier path] specifier)]))))))

(defn unused-refers
  "Names `ns-sym` referred and never uses: {name target}. A ClojureScript var
  referred in counts as used when the var is used from `ns-sym` by any name, as
  clojure.analysis/unused-refers has it; a name drawn out of a JavaScript module or
  a Closure namespace only when the source writes that name. The target is the
  var's qualified name, a Closure name, or a JS module's [specifier export].
  cljs.core's implicit refers are not refers here and are never reported."
  [cenv ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns cenv ns-sym)]
    (let [idx     (derived @model)
          used    (set (used-from (:usages idx) ns-sym))
          written (written-from idx ns-sym)]
      (merge
       (into {} (for [[sym v] (.getMappings n)
                      :when (instance? Var v)
                      :let  [home (.getName (.ns ^Var v))]
                      :when (not (#{ns-sym 'cljs.core} home))
                      :let  [k (var-key v)]
                      :when (not (used k))]
                  [sym k]))
       (into {} (for [[sym target] (env/goog-refers cenv ns-sym)
                      :when (not (written sym))]
                  [sym target]))
       (into {} (for [[sym target] (env/js-refers cenv ns-sym)
                      :when (not (written sym))]
                  [sym target]))))))

(defn unused-imports
  "Classes `ns-sym` :imported and never names: {name closure-name}."
  [cenv ns-sym]
  (let [written (written-from (derived @model) ns-sym)]
    (into {} (for [[sym target] (env/imports cenv ns-sym)
                   :when (not (written-as? written sym))]
               [sym target]))))

(defn- macro-view
  "`ns-sym`'s view of the JVM, where :require-macros put its aliases and refers -
  found, never created."
  ^Namespace [cenv ns-sym]
  (.find ^clojure.lang.NamespaceWorld (:macro-world cenv) ns-sym))

(defn unused-macro-aliases
  "Macro-namespace aliases in `ns-sym` through which no macro is called:
  {alias jvm-ns}. As with unused-aliases, used means a macro of the target
  namespace is called from `ns-sym`, by whatever name."
  [cenv ns-sym]
  (when-let [view (macro-view cenv ns-sym)]
    (let [used (set (keep #(some-> (namespace %) symbol)
                          (used-from (:macro-usages (derived @model)) ns-sym)))]
      (into {} (for [[a ^Namespace target] (.getAliases view)
                     :let  [t (.getName target)]
                     :when (not (used t))]
                 [a t])))))

(defn unused-macro-refers
  "Macros `ns-sym` referred and never calls: {name macro-qsym}."
  [cenv ns-sym]
  (when-let [view (macro-view cenv ns-sym)]
    (let [used (set (used-from (:macro-usages (derived @model)) ns-sym))]
      (into {} (for [[sym v] (.getMappings view)
                     :when (instance? Var v)
                     :let  [k (jvm-var-key v)]
                     :when (not (used k))]
                 [sym k])))))

(defn file-forms
  "The fids currently attributed to file `source`."
  [source]
  (get-in @model [:source->forms source] #{}))

(defn file-namespaces
  "The namespaces file `source` defines, per the model."
  [source]
  (let [m @model]
    (into #{} (keep #(get-in m [:forms % :ns])) (file-forms source))))

(defn ns-forms
  "The fids currently attributed to namespace `ns-sym`."
  [ns-sym]
  (set (for [[fid fe] (:forms @model) :when (= ns-sym (:ns fe))] fid)))

(defn snapshot
  "The whole model, for inspection and tests: the stored log merged with the derived
  indexes, spans as plain maps."
  []
  (let [m   @model
        idx (derived m)]
    (merge m idx
           {:usages (reduce-kv (fn [a k s] (assoc a k (spans->maps s))) {} (:usages idx))
            :keyword-usages (reduce-kv (fn [a k s] (assoc a k (spans->maps s)))
                                       {} (:keyword-usages idx))
            :macro-usages (reduce-kv (fn [a k s] (assoc a k (spans->maps s)))
                                     {} (:macro-usages idx))
            :defs   (reduce-kv (fn [a k e] (assoc a k (update e :span span->map)))
                               {} (:defs idx))})))

;; --- staleness and stale reload -------------------------------------------------

(defn changed-files
  "Analysed files whose mtime differs from the one they were compiled at - edited
  since. A file with no mtime then (inside a jar) or none now (moved, deleted) is
  not reported: there is nothing to recompile it from."
  []
  (let [m @model]
    (into #{} (for [[source t] (:file-mtime m)
                    :when t
                    :let [now (mtime (get-in m [:locations source]))]
                    :when (and now (not= now t))]
                source))))

(defn- changed-macro-files*
  "{source #{resource}}: for each analysed file, the macro files it expanded a
  version of that is not the one on disk now - edited since, or already edited
  and not loaded again when it expanded them."
  [m]
  (into {} (for [[source files] (:macro-files m)
                 :let [changed (into #{} (for [[file t] files
                                               :let [now (mtime file)]
                                               :when (and now (not= now t))]
                                           file))]
                 :when (seq changed)]
             [source changed])))

(defn- macro-closure
  "`seed` - macro files to load again - and every Clojure file the Clojure model
  says expands a macro of one of them at load time, transitively
  (clojure.analysis/stale-files): a file whose code expanded the old version holds
  it until it is loaded again too. Only the files on the way to one in `tracked`,
  a macro file some analysed file expanded, are kept - the rest are the Clojure
  side's to reload. Without a Clojure model this is `seed`."
  [seed tracked]
  (into #{} (filter #(some tracked (clj-analysis/stale-files #{%})))
        (clj-analysis/stale-files seed)))

(defn stale-macro-files
  "The Clojure files (classpath resources, e.g. \"app/macros.clj\") to load again
  before anything is recompiled: the macro files some analysed file expanded that
  changed on disk since the JVM loaded them (as far as this model knows, see
  :macro-loaded); the Clojure files the Clojure model has as edited since it loaded
  them; and, through its macro graph, the files that expand their macros at load
  time - as far as they lead to a macro file an analysed file expanded. Plus any a
  stale-reload! that threw left unloaded."
  []
  (let [m       @model
        tracked (into #{} (mapcat keys) (vals (:macro-files m)))
        edited  (for [file tracked
                      :let [t   (get-in m [:macro-loaded file])
                            now (mtime file)]
                      :when (and t now (not= now t))]
                  file)]
    (into (into #{} (filter mtime) (:pending-macro-files m))
          (macro-closure (into (set edited) (clj-analysis/changed-files)) tracked))))

(defn- cljs-var
  "The ClojureScript Var `qsym` names in `cenv`, or nil."
  ^Var [cenv qsym]
  (when-let [^Namespace n (env/find-cljs-ns cenv (symbol (namespace qsym)))]
    (.findInternedVar n (symbol (name qsym)))))

(defn meta-stale-files
  "The analysed files compiled against a var's metadata that the var in `cenv` no
  longer has (see record-meta-deps!): a ^boolean dropped, an arity a static call
  site named gone, the var itself removed. What changes it is the var's file
  recompiled, or a def typed at a REPL - which never enters the model but does
  change the var - so this asks the compile environment, not the disk."
  [cenv]
  (let [m   @model
        cur (memoize (fn [q k] (some-> (cljs-var cenv q) meta (get k))))]
    (into #{} (for [[_ fe] (:forms m)
                    :when (some (fn [[q k v]] (not= v (cur q k))) (:var-meta-deps fe))]
                (:source fe)))))

(defn stale-files
  "The analysed files to recompile: those edited since they were compiled
  (changed-files); those that expanded a version of a macro file other than the
  one on disk now; those that expanded a macro from a file stale-macro-files will
  load again, which an edit to another Clojure file can put there; and any a
  stale-reload! that threw left uncompiled. Given `cenv`, also meta-stale-files.

  No cascade among ClojureScript files past that metadata: a var a file uses is
  looked up at run time, so editing the var's file leaves its users' code right."
  ([]
   (let [m      @model
         reload (stale-macro-files)]
     (-> (changed-files)
         (into (keys (changed-macro-files* m)))
         (into (for [[source files] (:macro-files m)
                     :when (some reload (keys files))]
                 source))
         ;; one deleted since has nothing to recompile it from
         (into (filter #(mtime (get-in m [:locations %]))) (:pending-sources m)))))
  ([cenv]
   (into (stale-files) (meta-stale-files cenv))))

(defn deleted-files
  "Analysed files that were compiled from a file on disk and whose file is gone -
  deleted, renamed, or left behind by a branch switch. changed-files skips them:
  there is nothing to recompile them from."
  []
  (let [m @model]
    (into #{} (for [[source t] (:file-mtime m)
                    :when (and t (nil? (mtime (get-in m [:locations source]))))]
                source))))

;; --- prune ----------------------------------------------------------------------

(defn file-def-vars
  "The fully-qualified names of the vars file `source` has a def form for, as the
  model has it now."
  [source]
  (set (for [[k e] (:defs (derived @model))
             :when (= source (:source (:span e)))]
         k)))

(defn file-def-var-snapshot
  "{qsym Var} for the vars file `source` defines, as `cenv` holds them - prune-file!'s
  `prior`, taken BEFORE the file is recompiled
  (clojure.analysis/file-def-var-snapshot)."
  [cenv source]
  (into {} (for [k (file-def-vars source)] [k (cljs-var cenv k)])))

(defn- prune-vars!
  "Remove from `cenv` each var of `prior` that no live form defines any more and
  that is still the Var `prior` saw. Warns when one is still used. Returns them."
  [cenv prior]
  (let [idx  (derived @model)
        gone (for [[k old] prior
                   :when (and old
                              (nil? (get (:defs idx) k))
                              (identical? old (cljs-var cenv k)))]
               k)]
    (doseq [k gone]
      (when-let [us (seq (get (:usages idx) k))]
        (binding [*out* *err*]
          (println "WARN: pruning" (str k) "still referenced at"
                   (vec (sort (for [u us] [(:source u) (:line u) (:column u)]))))))
      (env/remove-var! cenv k))
    (vec gone)))

(defn prune-file!
  "Remove from the compile environment the vars whose def form vanished from file
  `source` - clojure.analysis/prune-file!, on `cenv` rather than the JVM's
  namespaces. `prior` is file-def-var-snapshot taken before `source` was
  recompiled. A var is removed when it was in `prior`, no live form defines it now,
  and the same Var object is still in `cenv`; env/remove-var! also unmaps it from
  every namespace that referred it. A use of it recorded anywhere is warned about,
  and it is removed all the same. Returns the removed names.

  THE COMPILE ENVIRONMENT ONLY. The runtime keeps the property, so code already
  compiled against the var runs as before; what changes is that nothing compiled
  from now on resolves it - a file that still uses it warns when it is recompiled,
  as does a form typed at a REPL. Removing it from the runtime too is
  clojure.cljs.repl's remove-var.

  Only vars the model saw defined by a def form a reader wrote are candidates: a
  var a macro made up a name for (deftype's ->T) is never removed, which leaves one
  whose source is gone behind, and never removes one that is not.

  Refuses a file the model has no forms for, as clojure.analysis's does: it would
  remove vars it simply never recorded."
  [cenv source prior]
  (when-not (seq (get-in @model [:source->forms source]))
    (throw (ex-info (str "prune-file! refused: " source " has no analysed forms in the "
                         "model - prune is only valid right after it was compiled under "
                         "the sink")
                    {:source source})))
  (prune-vars! cenv prior))

(defn- strip-ext [^String res]
  (subs res 0 (.lastIndexOf res ".")))

(defn- mark-loaded! [files]
  (swap! model (fn [m]
                 (reduce (fn [m res]
                           (-> (if-let [t (mtime res)] (assoc-in m [:macro-loaded res] t) m)
                               (update :pending-macro-files disj res)))
                         m files))))

(defn- told!
  "Tell clojure.analysis/*reload-progress* about `event`, if anything is listening.

  THAT VAR AND NOT ONE OF OUR OWN, although this is the other model. A
  ClojureScript reload loads Clojure macro files on the JVM before it compiles
  anything - through clojure.analysis/reload-files!, which reports through that var
  - so two channels would mean a watcher that bound only one of them saw half of a
  single reload, in no particular order relative to the other half. One stream, in
  the order things happen, with :dialect saying which side of the reload an event
  came from: :cljs here, absent for the macro files, which is exactly what they are.

  See clojure.analysis/*reload-progress* for the shape of the maps."
  [event]
  (when-let [f clj-analysis/*reload-progress*] (f event))
  nil)

(defn- reload-macro-files!
  "Load the Clojure files `files` again and return them in the order loaded. Those
  the Clojure model knows go through clojure.analysis/reload-files!, which orders
  them by its macro graph - a file after those whose macros its code expands - and
  keeps that model in step; the rest are loaded first, with a plain load, sorted:
  nothing says what they depend on.

  `prune` is the caller's (stale-reload!), and it reaches only the covered files:
  unmapping what a file stopped defining needs the model that recorded what it
  defined, so a macro file the Clojure model does not know keeps a deleted macro
  interned until something analyses it. Pruning here is the jvm's namespaces, which
  is what makes a macro deleted from a .clj file stop expanding rather than expand
  its old body; the vars unmapped are not returned - clojure.analysis/reload-files!
  does not answer them - and a usage of one is warned about on *err*."
  [files prune]
  (let [{covered true plain false} (group-by #(boolean (seq (clj-analysis/file-forms %)))
                                             files)
        plain (sort plain)]
    ;; Announced here because nothing else will: these are the macro files the
    ;; Clojure model does not cover, so they never reach reload-files! and its
    ;; reporting. A load is a load, and one that hangs is worth having named.
    (when (seq plain)
      (told! {:event :plan :pass 0 :files (vec plain)}))
    (let [n (count plain)]
      (doseq [[i res] (map-indexed vector plain)]
        (told! {:event :loading :pass 0 :file res :nth (inc i) :of n})
        (load (str "/" (strip-ext res)))
        (mark-loaded! [res])))
    (let [order (if (seq covered)
                  (clj-analysis/reload-files! covered :prune prune)
                  [])]
      (mark-loaded! order)
      (into (vec plain) order))))

(defn- in-require-order
  "`sources` ordered so that a file comes after the files it requires, as far as
  they are among `sources` - the order a runtime should run them in."
  [cenv sources]
  (let [ns-of (into {} (for [s sources] [(first (file-namespaces s)) s]))
        deps  (fn [s] (keep ns-of (env/requires cenv (first (file-namespaces s)))))]
    (loop [order [] placed #{} left (set sources)]
      (if (empty? left)
        order
        (let [ready (filter (fn [s] (every? #(or (placed %) (not (left %))) (deps s)))
                            (sort left))
              ready (if (seq ready) ready [(first (sort left))])]   ; a cycle: break it
          (recur (into order ready) (into placed ready) (reduce disj left ready)))))))

(defn stale-reload!
  "Bring the compiled program back in step with the disk: load every stale macro
  file on the JVM (stale-macro-files), then recompile every stale file
  (stale-files, given `cenv`) under the sink, in require order - and then, in more
  rounds, the files compiled against metadata that recompiling changed
  (meta-stale-files). Files deleted from disk are retracted from the model first
  (deleted-files). Returns

    :macro-files  the Clojure files loaded again
    :reloaded     the files recompiled, in order
    :deleted      the files retracted
    :pruned       the vars removed from the compile environment (:prune)
    :scripts      [ns script] for every namespace compiled, in order - what a REPL
                  ships to its runtimes (clojure.cljs.repl's stale-reload)

  `opts` are the driver's (compile-file!). With :prune true, the vars a
  recompiled file no longer defines, and those of a deleted file, are removed from
  `cenv` (prune-file!) - before the next file compiles, so one that still uses them
  warns - and not from the runtime. The macro files are pruned too, on the jvm,
  where a reloaded Clojure file no longer defines a macro: that is
  clojure.analysis's own pruning (see reload-macro-files!), so what it unmapped is
  not in :pruned, which is `cenv`'s.

  The macro files are loaded in the Clojure model's macro order where it covers
  them (see reload-macro-files!). The stale sets are taken before anything is
  loaded - loading a macro file clears what made its expanders stale - and kept in
  the model as pending until each is done.

  FAIL-FAST, as clojure.analysis/stale-reload! is: a file that does not load or
  compile throws, and the ones after it are not reached. Nothing is lost - what was
  not done stays pending, and is stale again next time; a var not pruned then is
  not pruned later, though, since its def has left the model."
  [cenv opts & {:keys [prune]}]
  (let [mfiles  (stale-macro-files)
        sources (in-require-order cenv (stale-files cenv))
        deleted (sort (deleted-files))
        ;; The whole of what this is about to do, before any of it has cost
        ;; anything: the macro files it will load on the JVM, the files it will
        ;; recompile, and the files it is dropping. Which is the half nobody can
        ;; work out from their buffers - a .cljs file goes stale because a .clj
        ;; file it expands a macro from changed, and neither file says so.
        _       (told! {:event :plan :dialect :cljs :files sources
                        :macro-files (vec mfiles) :deleted (vec deleted)})
        _       (swap! model #(-> %
                                  (update :pending-macro-files into mfiles)
                                  (update :pending-sources into sources)))
        mfiles  (reload-macro-files! mfiles prune)
        pruned  (atom [])
        _       (doseq [s deleted]
                  (let [prior (when prune (file-def-var-snapshot cenv s))]
                    (retract-file! s)
                    (when prune (swap! pruned into (prune-vars! cenv prior)))))
        compile (fn [s]
                  (let [prior (when prune (file-def-var-snapshot cenv s))
                        r     (load-file! cenv (str (location-file
                                                     (get-in @model [:locations s])))
                                          opts)]
                    (when prune (swap! pruned into (prune-file! cenv s prior)))
                    r))
        ;; Each file named BEFORE it is compiled, for the reason
        ;; clojure.analysis/reload-files! names one before it loads it: the file
        ;; that never finishes is the one worth having on the screen, and a line
        ;; printed afterwards names every file except that one.
        compile-all (fn [ss]
                      (let [n (count ss)]
                        (into [] (map-indexed
                                  (fn [i s]
                                    (told! {:event :loading :dialect :cljs :file s
                                            :nth (inc i) :of n})
                                    (compile s)))
                              ss)))
        ;; a round's recompiles can change the metadata another file was compiled
        ;; against; each round settles the files the last one unsettled. Bounded,
        ;; because a file's metadata could in principle follow another's in a cycle:
        ;; what is left then is meta-stale, and found next time.
        [order results]
        (loop [order sources, results (compile-all sources), rounds 0]
          (let [more (in-require-order cenv (meta-stale-files cenv))]
            (if (or (empty? more) (> rounds (count (:source->forms @model))))
              [order results]
              (do (swap! model update :pending-sources into more)
                  ;; A round nobody could have predicted from the plan above - these
                  ;; files were settled until the last round recompiled something
                  ;; whose metadata they were compiled against - so it is announced
                  ;; as its own plan rather than left to look like the first one
                  ;; going on longer than it said.
                  (told! {:event :plan :dialect :cljs :files more
                          :round (inc rounds)})
                  (recur (into order more) (into results (compile-all more))
                         (inc rounds))))))]
    {:macro-files (vec mfiles)
     :reloaded    order
     :deleted     (vec deleted)
     :pruned      @pruned
     :scripts     (into [] (mapcat :scripts) results)}))
