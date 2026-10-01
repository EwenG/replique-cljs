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
  hook in clojure.cljs.macroexpand (*on-expand*), which run-analysis binds. A
  protocol named in an implementation is the third: it has become a munged
  property name before the analyzer sees anything, and comes from the hook beside
  it (*on-protocol-impl*) - see on-protocol-impl.

  CODE THE PROGRAM DOES NOT RUN - a #_, a (comment ...) - is not compiled, so it
  has no AST; it is resolved instead, by clojure.analysis's walk, and its uses are
  recorded marked :dead, for find-usages. The unused-* lints count a use in a
  comment and not one in a #_ (see commit-dead! and from-ns?).

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
  find-macro-usages, find-host-usages, find-host-usages-where, macro-deps,
  ns-referenced-namespaces, unused-locals, unused-aliases, unused-refers,
  unused-imports, unused-macro-aliases, unused-macro-refers, changed-files,
  stale-macro-files, stale-files, meta-stale-files, deleted-files,
  file-def-vars, file-def-var-snapshot, file-forms, file-namespaces, ns-forms,
  file-facts, file-mtime, file-failure, version, snapshot."
      :author "replique-cljs"}
    clojure.cljs.analysis
  (:require [clojure.analysis :as clj-analysis]
            [clojure.cljs.analyzer :as ana]
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
;;                         :host-usages :var-meta-deps :invokes :warnings
;;                         :ns-specs}}
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
;; derived (built from :forms by `index`, each cached by :forms identity):
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
;;   :ns-usages      {lib #{span-map}}    where each ns form requires lib, read out of
;;                                        the :ns-specs facts (see find-namespace-usages)
(def ^:private empty-model
  {:forms {} :source->forms {} :locations {} :file-mtime {} :macro-files {}
   :macro-loaded {} :pending-macro-files #{} :pending-sources #{} :next-fid 0})

(defonce ^:private model (atom empty-model))

;; A usage/def span, as clojure.analysis has it: primitive coordinates, an absent
;; end stored as -1, and `entity` - the var key the span is about - carried on the
;; span so a fact is one object. from-ns is a namespace SYMBOL here (a
;; ClojureScript namespace is not something to hold on to); nil for a def. dead is
;; :discard or :comment for a use in code the program does not run (commit-dead!).
;; declaration is :refer for the name an ns form's clause writes rather than a use
;; of it (record-declares!), :declare for a def that only declares its name
;; (`declare'), else nil. written and var-form are clojure.analysis's: the symbol a
;; use was spelled by where it is not the var's own name unqualified, and true for
;; a use through the `var' special form. role is clojure.analysis's too: :defmethod
;; for the multimethod a defmethod adds to, :destructuring for a keyword a :keys
;; writes as the local it binds.
(defrecord Span [entity source ^int line ^int column ^int end-line ^int end-column from-ns
                 dead declaration written var-form role])

(defn- norm-pos [x] (if (nat-int? x) (int x) -1))

(defn- span
  ([entity source line column el ec from-ns]
   (span entity source line column el ec from-ns nil))
  ([entity source line column el ec from-ns dead]
   (span entity source line column el ec from-ns dead nil))
  ([entity source line column el ec from-ns dead declaration]
   (span entity source line column el ec from-ns dead declaration nil nil))
  ([entity source line column el ec from-ns dead declaration written var-form]
   (span entity source line column el ec from-ns dead declaration written var-form nil))
  ([entity source line column el ec from-ns dead declaration written var-form role]
   (->Span entity source (norm-pos line) (norm-pos column) (norm-pos el) (norm-pos ec)
           from-ns dead declaration written (when var-form true) role)))

(defn- written-as
  "clojure.analysis/written-as: the spelling worth keeping, nil for the var's own
  name unqualified."
  [k written]
  (when (and (symbol? written)
             (or (namespace written) (not= (name written) (name k))))
    (with-meta written nil)))

(defn- span->map [s]
  (cond-> {:source (:source s) :line (:line s) :column (:column s)}
    (nat-int? (:end-line s))   (assoc :end-line (:end-line s))
    (nat-int? (:end-column s)) (assoc :end-column (:end-column s))
    (:from-ns s)               (assoc :from-ns (:from-ns s))
    (:dead s)                  (assoc :dead (:dead s))
    (:declaration s)           (assoc :declaration (:declaration s))
    (:written s)               (assoc :written (:written s))
    (:var-form s)              (assoc :var-form true)
    (:role s)                  (assoc :role (:role s))))

(defn- spans->maps [spans]
  (when spans (into #{} (map span->map) spans)))

;; A call the source wrote of a var, and how many arguments it was given -
;; clojure.analysis's Invoke, from the :invoke node rather than from the compiler.
(defrecord Invoke [entity source ^int line ^int column ^int end-line ^int end-column from-ns
                   ^int argc])

;; kind is :field for the binding of a deftype or defrecord field, what the type
;; is and not a local its code has to read, and :fn for the name an fn* gives
;; itself, which is there so that the fn can call itself and not for anything to
;; read - see unused-locals. nil for any other binding.
(defrecord LocalSpan [binding source ^int line ^int column ^int end-line ^int end-column lns lname
                      kind])

(defn- local->map
  "A LocalSpan as the plain map the :locals index holds - clojure.analysis's
  shape, :name omitted for a use, :field for a field, :fn-name for an fn's name."
  [l]
  (cond-> {:source (:source l) :line (:line l) :column (:column l) :ns (:lns l)}
    (nat-int? (:end-line l))   (assoc :end-line (:end-line l))
    (nat-int? (:end-column l)) (assoc :end-column (:end-column l))
    (:lname l)                 (assoc :name (:lname l))
    (= :field (:kind l))       (assoc :field true)
    (= :fn (:kind l))          (assoc :fn-name true)))

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
(def ^:private ^:const CAT-INVOKES  9)
(def ^:private ^:const CAT-WARNINGS 10)
(def ^:private ^:const CAT-NSSPECS  11)
;; WHAT THE TEXT SPELLS, from the reader: the namespace part of every qualified
;; symbol it reads - see clojure.lang.IAnalysisSink/qualifierUsage.
(def ^:private ^:const CAT-QUALIFIERS 12)
(def ^:private ^:const N-CATS       13)

(def ^:private cat-keys
  [:usages :defs :locals :local-uses :keyword-usages :macro-usages :macro-deps
   :host-usages :var-meta-deps :invokes :warnings :ns-specs :qualifiers])

;; A form being compiled. `pos` is [line column], corrected by form-start once the
;; form has been read; `cats` holds one ArrayList per fact category, made on first use.
(deftype OpenForm [^long seq ^longs pos ^objects cats])

;; A file being compiled. `ignored` is cljs.core's frame, which is pushed like any
;; other - so a form's facts always land in the frame of the file it belongs to -
;; and whose facts go nowhere. `forms` is the stack of open forms, `buffer` the
;; finished ones, `counter` the next begin-order rank. `dead` is the file's dead code,
;; kept until the file ends and resolved then in `cenv` - see commit-dead!. `ns-sym`
;; is the namespace the file declares, which nothing in the model is keyed by and
;; which end-file says was recompiled - see defined!.
(deftype FileFrame [source location mtime ignored ^ArrayList forms ^ArrayList buffer
                    ^longs counter cenv ^ArrayList dead nsym])

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

(defn- record-def!
  "A def, marked :declare where the name is only declared - `declare' expands to a
  def of a name marked :declared, and the mark is on the name as it is written."
  [^OpenForm of source var-node]
  (let [^longs pos (.pos of)
        form (:form var-node)
        m (or (written-at form)
              {:line (aget pos 0) :column (aget pos 1)})]
    (add-fact! of CAT-DEFS (span (:name var-node) source (:line m) (:column m)
                                 (:end-line m) (:end-column m) nil nil
                                 (when (:declared (meta form)) :declare)))))

(defn- record-usage!
  "A use of a var, with the symbol it was spelled by (written-as) and whether it
  went through the `var' special form."
  ([of source from-ns node] (record-usage! of source from-ns node false))
  ([^OpenForm of source from-ns node var-form?]
   (let [form (:form node)]
     (when-let [m (written-at form)]
       (add-fact! of CAT-USAGES (span (:name node) source (:line m) (:column m)
                                      (:end-line m) (:end-column m) from-ns nil nil
                                      (written-as (:name node) form) var-form?
                                      ;; cljs.core/defmethod marks the multimethod
                                      (when (:clojure.analysis/defmethod (meta form))
                                        :defmethod)))))))

(defn- record-invoke!
  "A call of a var the source wrote: the :invoke node's :fn is a :var whose symbol
  carries the reader's position. At the call - the list as written - where the
  reader gave it a position, and at the symbol otherwise; after macroexpansion, so
  (-> x (f 1)) is a call of f with two arguments where (f 1) is written."
  [^OpenForm of source from-ns node]
  (let [f (:fn node)]
    (when (= :var (:op f))
      (when-let [sym (written-at (:form f))]
        (let [m (let [l (meta (:form node))] (if (:line l) l sym))]
          (add-fact! of CAT-INVOKES
                     (->Invoke (:name f) source (norm-pos (:line m)) (norm-pos (:column m))
                               (norm-pos (:end-line m)) (norm-pos (:end-column m))
                               from-ns (int (count (:args node))))))))))

(defn- record-declares!
  "What the ns form's clauses WRITE: every name a :refer, an :only or a :rename
  names, at the name as the spec writes it.

  Filed with the uses - a macro's with the macro uses, a var's with the var uses,
  a host name's with the host uses - so that where-is-this-name-written is one
  list, which is what a rename walks. And marked :declaration :refer (or :import,
  for the class an :import names), because it is not a use: from-ns? leaves it
  out of the unused-* lints, since a refer kept alive by its own :refer is one
  nothing could ever report.

  The analyzer puts them on the node (its declared-names), because by the time the
  ns form has been applied the written symbols are gone and only the namespace's
  state is left."
  [^OpenForm of source from-ns node]
  (doseq [[k written kind declaration] (:declares node)
          :let [m (meta written)]]
    (add-fact! of (case kind :macro CAT-MACROUSE :host CAT-HOST CAT-USAGES)
               (span k source (:line m) (:column m) (:end-line m) (:end-column m)
                     from-ns nil (or declaration :refer)))))

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

(defn- record-local!
  "A binding the source wrote, as a binding.

  NOT A REIFY'S CAPTURE OF ONE. cljs.core/reify makes a field of every local in
  scope and writes the field vector with the very symbols the source bound those
  locals with, so each capture lands on a binding that is already recorded - the
  programmer's - and recording it again would say two things are bound where one
  is. The analyzer marks a capture :captures (its field-bindings), and the local
  it captures keeps the site to itself."
  [^OpenForm of source ns node]
  (let [sym (:form node)]
    ;; a symbol the source wrote - not a macro's gensym, and not the try form a
    ;; catch's own binding hangs off
    (when-let [m (and (symbol? sym) (nil? (:captures node)) (written-at sym))]
      (add-fact! of CAT-LOCALS
                 (->LocalSpan [source (:js-name node)] source
                              (norm-pos (:line m)) (norm-pos (:column m))
                              (norm-pos (:end-line m)) (norm-pos (:end-column m))
                              ns (:name node) (#{:field :fn} (:local node)))))))

(defn- record-local-use! [^OpenForm of source ns js-name m]
  (when m
    (add-fact! of CAT-LOCALUSE
               (->LocalSpan [source js-name] source
                            (norm-pos (:line m)) (norm-pos (:column m))
                            (norm-pos (:end-line m)) (norm-pos (:end-column m))
                            ns nil nil))))

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

                :ns (do (record-declares! of source ns n)
                        ;; the clauses as written, positioned: the namespace's
                        ;; state says what is unused, and not where it is written
                        (add-fact! of CAT-NSSPECS
                                   (assoc (clj-analysis/ns-specs (:form n)) :ns (:name n))))

                :invoke (do (record-invoke! of source ns n)
                            (run! visit (ast/children n)))

                :var (do (record-usage! of source ns n)
                         (record-meta-deps! of n))

                ;; (var x), #'x: a use of x that names the var rather than taking
                ;; its value - which is what makes it legal of a private one
                :the-var
                (let [v (:var n)]
                  (record-usage! of source ns v true)
                  (record-meta-deps! of v)
                  (doseq [c (ast/children n) :when (not (identical? c v))]
                    (visit c)))

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
                   ;; it compiled to the end, so whatever failed before is behind it
                   (update :failures dissoc source)
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

;; --- dead code: #_ and (comment ...) -------------------------------------------

;; clojure.analysis's dead code, for the same reason and by the same walk
;; (clojure.analysis/walk-dead-code): the form a #_ discards, which the reader hands
;; the reader sink (deadForm), and the form of a (comment ...), which on-expand
;; sees. Neither is compiled; each symbol written in them is resolved, at the end of
;; the file, the way the analyzer would resolve it - a ClojureScript var, or a macro
;; - and recorded as a use marked :dead. No defs, no locals, no macro edges, no
;; metadata dependencies: nothing that makes a file stale or orders a reload.

(defn- close-dead!
  "Open form `of` of frame `fr` has ended: give the dead code written in it the
  locals its live code bound, which are complete only now - a #_ is read before
  the form around it is compiled - and mark dead the keywords the reader reported
  inside it (clojure.analysis/mark-dead!), and the qualifiers it reported with them.
  The reader's other reports, syntax-quote references, are not kept here at all."
  [^FileFrame fr ^OpenForm of]
  (let [^ArrayList dead (.dead fr)
        outer (delay (clj-analysis/locals-at (aget ^objects (.cats of) CAT-LOCALS)))
        spans (ArrayList.)]
    (dotimes [i (.size dead)]
      (let [d (.get dead i)]
        (when (identical? of (:of d))
          (when-let [sp (:span d)] (.add spans [(:kind d) sp]))
          (.set dead i (-> d (dissoc :of) (assoc :outer @outer))))))
    (when-not (.isEmpty spans)
      (let [spans (vec spans)]
        (clj-analysis/mark-dead! (aget ^objects (.cats of) CAT-KEYWORDS) spans)
        (clj-analysis/mark-dead! (aget ^objects (.cats of) CAT-QUALIFIERS) spans))))
  nil)

(defn- dead-resolvers
  "The walk's :target and :op in `cenv`, for the namespace env/*current-ns* names
  when they are called.

  A head prefers a macro and anything else a var, which is the analyzer's order:
  (str x) is a call of the macro, and str passed to map is the function. The core
  macros are named as clojure.core's for the walk, which knows the binding forms by
  those names."
  [cenv]
  (let [macro (fn [sym] (mx/macro-var cenv {} sym))
        core  (:core-macros cenv)]
    {:target (fn [sym head?]
               (if head?
                 (or (macro sym) (env/resolve-var cenv sym))
                 (or (env/resolve-var cenv sym) (macro sym))))
     :op     (fn [sym]
               (when-let [^Var m (macro sym)]
                 (let [n (.getName (.ns m))]
                   (if (or (= core n) (= 'clojure.core n))
                     (symbol "clojure.core" (str (.sym m)))
                     (jvm-var-key m)))))}))

(defn- commit-dead!
  "Resolve the dead code of file frame `fr` - it has compiled to the end, so what
  it defines and requires is there - and add what it names to the frame's buffer,
  as one more form: ClojureScript vars as :usages, macros as :macro-usages. A form
  that cannot be walked is skipped: it is the program's to be wrong, never the
  compile's."
  [^FileFrame fr]
  (let [^ArrayList dead (.dead fr)]
    (when-not (.isEmpty dead)
      (let [source (.source fr)
            cenv   (.cenv fr)
            uses   (ArrayList.)
            macros (ArrayList.)]
        (doseq [{:keys [form kind ns outer]} dead]
          (binding [env/*current-ns* ns]
            (let [emit (fn [^Var v sym]
                         (let [m (meta sym)]
                           (when (:column m)
                             (if (.isMacro v)
                               (.add macros (span (jvm-var-key v) source (:line m) (:column m)
                                                  (:end-line m) (:end-column m) ns kind))
                               (when-let [k (var-key v)]
                                 (.add uses (span k source (:line m) (:column m)
                                                  (:end-line m) (:end-column m) ns kind
                                                  nil (written-as k sym) nil
                                                  (when (:clojure.analysis/defmethod m)
                                                    :defmethod))))))))]
              (try
                (clj-analysis/walk-dead-code (clj-analysis/dead-body form kind)
                                             (assoc (dead-resolvers cenv)
                                                    :outer outer :emit emit))
                (catch Exception _ nil)))))
        (when-not (and (.isEmpty uses) (.isEmpty macros))
          (let [^longs c (.counter fr)
                rank     (aget c 0)
                ^Span s1 (first (concat uses macros))]
            (aset c 0 (inc rank))
            (.add ^ArrayList (.buffer fr)
                  (cond-> {:seq rank :source source :line (.line s1) :column (.column s1)
                           :ns nil}
                    (not (.isEmpty uses))   (assoc :usages (vec uses))
                    (not (.isEmpty macros)) (assoc :macro-usages (vec macros)))))))))
  nil)

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
  (varUsage [_ _ _ _ _ _ _ _ _ _])
  (varDef [_ _ _ _ _ _ _ _])
  (localDef [_ _ _ _ _ _ _ _ _])
  (localUsage [_ _ _ _ _ _ _ _])
  (classUsage [_ _ _ _ _ _ _ _])
  (macroExpansion [_ _ _ _ _ _ _ _ _])
  (deadForm [_ form kind _ _ line column el ec]
    ;; a #_ - LispReader does not report one in a branch not taken
    (when-let [^FileFrame fr (peek-list files)]
      (when-not (.ignored fr)
        (.add ^ArrayList (.dead fr)
              {:form form :kind kind :ns env/*current-ns* :of (peek-list (.forms fr))
               :span (when (and (nat-int? line) (nat-int? el)) [line column el ec])})))
    nil)
  (keywordUsage [_ kw _ _ line column el ec]
    ;; the branch of a reader conditional this platform does not take is read with
    ;; *suppress-read* on - it is another platform's code, not this program's. A #_
    ;; discard is read normally and IS recorded: it is still written in the file.
    (when-let [of (and (not (RT/suppressRead)) (open-form files))]
      (add-fact! of CAT-KEYWORDS
                 (span kw (.source ^FileFrame (peek-list files)) line column el ec
                       env/*current-ns*))))
  (qualifierUsage [_ qualifier _ _ line column el ec]
    ;; the namespace part of a qualified symbol, which is the only record of an
    ;; alias a macro ate or re-spelled - keywordUsage's lines, for its reasons
    (when-let [of (and (not (RT/suppressRead)) (open-form files))]
      (add-fact! of CAT-QUALIFIERS
                 (span qualifier (.source ^FileFrame (peek-list files)) line column el ec
                       env/*current-ns*)))))

(defn- comment-macro?
  "Is macro `v` a (comment ...) - cljs.core's, or clojure.core's in a .cljc read as
  Clojure's by a :require-macros?"
  [^Var v]
  (and (= "comment" (str (.sym v)))
       (contains? '#{cljs.core clojure.core} (.getName (.ns v)))))

(defn- on-expand
  "The macroexpand hook for one run: every expansion inside an open form is an edge
  from the namespace being compiled to the macro, and a call the source wrote -
  its symbol carries the reader's position - is a use of the macro too. A
  (comment ...) is also dead code (commit-dead!): its body is never compiled, and
  this is the only sight of it anything gets."
  [^ArrayList files]
  (fn [^Var v op form]
    (when-let [of (open-form files)]
      (let [k  (jvm-var-key v)
            ns env/*current-ns*]
        (when (comment-macro? v)
          (.add ^ArrayList (.dead ^FileFrame (peek-list files))
                {:form form :kind :comment :ns ns :of of
                 ;; from the end of the comment symbol, a live call, to the end of
                 ;; the form
                 :span (let [h (written-at op) m (meta form)]
                         (when (and (:end-line h) (:end-column h)
                                    (:end-line m) (:end-column m))
                           [(:end-line h) (:end-column h) (:end-line m) (:end-column m)]))}))
        (add-fact! of CAT-MACRODEP [ns k (:file (meta v))])
        (when-let [m (written-at op)]
          (add-fact! of CAT-MACROUSE
                     (span k (.source ^FileFrame (peek-list files)) (:line m) (:column m)
                           (:end-line m) (:end-column m) ns)))))))

(defn- on-protocol-impl
  "The protocol hook for one run: naming a protocol in a `deftype', a `defrecord',
  a `reify', a `specify!' or an `extend-type' is a use of it, recorded where the
  source wrote it.

  WHICH MAKES WHO-IMPLEMENTS-THIS THE SAME QUESTION AS WHERE-IS-THIS-USED, asked
  with one op and answered with one list. It is how Clojure answers it too, and by
  accident rather than design: a protocol there generates an interface, a `deftype'
  names that interface by the time the compiler sees it, and the place lands among
  the interface's usages. ClojureScript generates no interface - see
  clojure.cljs.macroexpand/*on-protocol-impl* for what it generates instead - so the
  same answer has to be put together on purpose.

  ONLY WHAT SOMEBODY WROTE. A protocol with no reader position was named by a
  macro, not in the file: `defrecord' extends fourteen of cljs.core's own, and a
  place nobody can be taken to is not a place. `on-expand' turns a macro call away
  by the same test.

  Not a method's implementations, which this is not and does not become: a method
  answers its call sites, because a type need not implement every method it could
  and the two questions part company there."
  [^ArrayList files]
  (fn [qsym written]
    (when-let [of (open-form files)]
      (when-let [m (written-at written)]
        (add-fact! of CAT-USAGES
                   (span qsym (.source ^FileFrame (peek-list files))
                         (:line m) (:column m) (:end-line m) (:end-column m)
                         env/*current-ns*))))
    nil))

(defn- on-destructured-keyword
  "The destructuring hook for one run (clojure.cljs.macroexpand/
  *on-destructured-keyword*): {:keys [id]} is a use of :id the source spells id,
  recorded where the local is written and marked :destructuring - clojure.analysis's
  destructuredKeyword, for the other compiler. Only a symbol the reader read."
  [^ArrayList files]
  (fn [kw written]
    (when-let [of (open-form files)]
      (when-let [m (written-at written)]
        (add-fact! of CAT-KEYWORDS
                   (span kw (.source ^FileFrame (peek-list files))
                         (:line m) (:column m) (:end-line m) (:end-column m)
                         env/*current-ns* nil nil nil nil :destructuring))))
    nil))

(defn- warned-at
  "Where a warning about `info` was written: the first thing in it the reader read,
  or nil. A warning says what it is about in its own terms - {:sym foo}, {:form
  (recur ...)}, {:protocol IFoo} - and what the reader read carries its position."
  [info]
  (some (fn [v] (let [m (written-at v)] (when (:line m) m))) (vals info)))

(defn- on-warning
  "The warning hook for one run (clojure.cljs.analyzer/*on-warning*): a warning is a
  fact of the form being compiled, at what it is about where that can be told, and
  at the form otherwise."
  [^ArrayList files]
  (fn [type info]
    (when-let [^OpenForm of (open-form files)]
      (let [^longs pos (.pos of)
            m (or (warned-at info) {:line (aget pos 0) :column (aget pos 1)})]
        (add-fact! of CAT-WARNINGS
                   (cond-> {:kind type :info info
                            :source (.source ^FileFrame (peek-list files))
                            :line (:line m) :column (:column m) :ns env/*current-ns*}
                     (:end-line m) (assoc :end-line (:end-line m))
                     (:end-column m) (assoc :end-column (:end-column m))))))
    nil))

(defn- defined!
  "Tell clojure.analysis/*defined* about `event`, if anything is listening.

  THAT VAR AND NOT ONE OF OUR OWN, for `told!'s reason and one more besides. A
  reload of this compiler loads Clojure macro files on the JVM, which define
  Clojure vars and say so through that var, and half of what a ClojureScript
  reload replaces is therefore reported from the other side - so a watcher that
  bound two vars would see half of one reload in each. One stream, in the order
  things happen, with :dialect saying which side an event came from.

  See clojure.analysis/*defined* for the shape of the maps."
  [event]
  (when-let [f clj-analysis/*defined*] (f event))
  nil)

(defn defined-by!
  "Say what `node` - one analysed top-level form - defines.

  FOR A FORM THAT IS INSIDE NO FILE, which is the one thing the sink below cannot
  answer for: a `defn' typed at a prompt compiles under no file frame, so nothing
  is recorded and there is nothing for `end-file' to report. It is also exactly
  what somebody fixing one function does, so it is the case the hooks this feeds
  exist for as much as a whole file is. clojure.cljs.repl/compile-form calls this;
  a file goes through the sink and is reported once, whole.

  Cheap where nobody is listening, which is why the walk is inside the test: an
  AST walk per REPL input costs nothing next to having compiled it, and it still
  should not happen for nothing.

  A :def and a :deftype each hold the var they define as a :var child, which is
  where the name is - `record-facts!' reads it the same way and says why."
  [node]
  (when clj-analysis/*defined*
    (letfn [(visit [n]
              (case (:op n)
                (:def :deftype)
                (when-let [k (:name (:var n))]
                  (defined! {:dialect :cljs :op :define
                             :ns (symbol (namespace k)) :var k}))
                nil)
              (run! visit (ast/children n)))]
      (visit node)))
  nil)

(defn removed!
  "Say that `qsym` has been taken away - clojure.cljs.repl's remove-var, which is a
  removal nothing else here reports: it names one var, needs no model, and takes it
  out of `cenv` and out of the runtime both. A reload's removals are `prune-vars!'s."
  [qsym]
  (defined! {:dialect :cljs :op :remove :ns (symbol (namespace qsym)) :var qsym})
  nil)

;; One per run-analysis. `files` is the stack of files being compiled; it is touched
;; only by the thread the compilation runs on, which is the thread that bound it.
(defn- failed-at
  "Where `t` says the compile failed, as {:line :column}, or nil: the first of its
  causes whose data names a line, or holds a :form the reader positioned -
  analysis-error hands over the form it refuses."
  [^Throwable t]
  (some (fn [^Throwable c]
          (let [d (ex-data c)]
            (cond (:line d) (select-keys d [:line :column])
                  (:line (written-at (:form d))) (select-keys (written-at (:form d))
                                                              [:line :column :end-line
                                                               :end-column]))))
        (take-while some? (iterate #(.getCause ^Throwable %) t))))

(defn- root-message
  "The message of the deepest cause of `t` that has one."
  [^Throwable t]
  (or (last (keep #(.getMessage ^Throwable %)
                  (take-while some? (iterate #(.getCause ^Throwable %) t))))
      (.getName (class t))))

(defn- record-failure!
  "The compile of the file `fr` is threw `t`: remember it against the version of the
  file that failed, until the file next compiles to the end - see file-failure. At
  the form being compiled when nothing more precise is known."
  [^FileFrame fr ^Throwable t]
  (let [^OpenForm of (peek-list (.forms fr))
        pos (or (failed-at t)
                (when of {:line (aget ^longs (.pos of) 0) :column (aget ^longs (.pos of) 1)}))]
    (swap! model assoc-in [:failures (.source fr)]
           (merge {:mtime (mtime (.location fr)) :message (root-message t)} pos))))

(deftype AnalysisSink [^ArrayList files reader]
  driver/CompileSink
  (reader-sink [_] reader)
  (begin-file [_ cenv ns-sym source location]
    (.add files (FileFrame. source location (mtime location) (= 'cljs.core ns-sym)
                            (ArrayList.) (ArrayList.) (long-array 1) cenv (ArrayList.)
                            ns-sym))
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
          (close-dead! fr of)
          (when-let [fe (freeze-form of (.source fr))]
            (.add ^ArrayList (.buffer fr) fe)))))
    nil)
  (end-file [_ _source]
    (when-let [^FileFrame fr (peek-list files)]
      (pop-list! files)
      (when-not (.ignored fr)
        (commit-dead! fr)
        (commit-frame! fr))
      ;; AND THE FILE'S CODE HAS BEEN REPLACED, which is a fact about the program
      ;; rather than about the model - so it is said for cljs.core's frame too,
      ;; whose facts go nowhere.
      ;;
      ;; THE UNIT IS THE NAMESPACE because the unit of a compile IS the namespace:
      ;; the module is rewritten whole and every function in it is a new object,
      ;; whether or not a single def in it reads any differently than it did. Which
      ;; is what watching a namespace's definitions for a change gets wrong, and
      ;; gets wrong in the direction of saying that nothing happened. A def typed
      ;; at a prompt is the other unit and is `defined-by!'s.
      (defined! {:dialect :cljs :op :define :ns (.nsym fr) :source (.source fr)}))
    nil)
  (abort-file [_ _source error]
    ;; its open forms go with it: they are on the frame, not beside it
    (when-not (.isEmpty files)
      (let [^FileFrame fr (peek-list files)]
        (when-not (.ignored fr)
          (record-failure! fr error)))
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
    (binding [driver/*sink*          (->AnalysisSink files (->ReaderSink files))
              mx/*on-expand*         (on-expand files)
              mx/*on-protocol-impl*  (on-protocol-impl files)
              mx/*on-destructured-keyword* (on-destructured-keyword files)
              ana/*on-warning*       (on-warning files)]
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
                           (update :failures dissoc source)
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

;; ONE CACHE PER SUB-INDEX, for the reason clojure.analysis's are one each: they are
;; all pure functions of the same form log and so go stale by the same rule, but they
;; are not wanted at the same moments. A reload reads `:defs` while it prunes and
;; reads nothing else; `:usages`, `:locals` and `:macro-usages` answer an editor's
;; questions. Held as one index they were all rebuilt whenever any of them was, and
;; every file compiled is a new form log - so recompiling K files replayed the whole
;; model K times.
(defonce ^:private index-caches
  (into {} (for [k [:usages :defs :locals :keyword-usages :macro-usages :macro-deps
                    :host-usages :ns-usages :qualifiers]]
             [k (atom {:forms nil :value nil})])))

(defn- sorted-fids
  "The live form ids, ascending, in a primitive array. `:defs` is the one index whose
  answer depends on the order the log is replayed in, so it is the one place this is
  needed - and boxing the keys of a large log to sort them is not free."
  ^longs [forms]
  (let [^longs a (long-array (keys forms))]
    (java.util.Arrays/sort a)
    a))

(defn- build-spans
  "{entity #{Span}} over one fact category - `:usages`, `:keyword-usages`,
  `:macro-usages` or `:host-usages`, which differ in nothing but which category they
  fold. No replay order to respect: each fact joins the set under its own entity key."
  [forms cat]
  (persistent!
   (reduce-kv (fn [idx _ fe]
                (reduce (fn [idx ^Span s]
                          (let [e (.entity s)]
                            (assoc! idx e (conj (get idx e #{}) s))))
                        idx (get fe cat)))
              (transient {}) forms)))

(defn- build-defs
  "{qsym {:span span}} - replayed in fid order, because it is the one index where a
  later fact has to beat an earlier one: a later def of the same var overwrites the
  earlier entry, so the highest fid wins."
  [forms]
  (let [^longs fids (sorted-fids forms)
        n           (alength fids)]
    (loop [i 0, idx (transient {})]
      (if (< i n)
        (recur (inc i)
               (reduce (fn [idx ^Span s] (assoc! idx (.entity s) {:span s}))
                       idx (:defs (get forms (aget fids i)))))
        (persistent! idx)))))

(defn- build-locals
  "{binding {:ns :name ...span :uses #{use}}} - two fact categories in one index,
  since a local's uses belong to its entry. A form's bindings are folded before its
  uses, so every binding is registered before a use can attach to it; a local is
  scoped to its own form, so the order between forms does not come into it."
  [forms]
  (persistent!
   (reduce-kv
    (fn [idx _ fe]
      (as-> idx idx
        (reduce (fn [idx ^LocalSpan l]
                  (let [b (.binding l)]
                    (assoc! idx b (assoc (local->map l)
                                         :uses (get (get idx b) :uses #{})))))
                idx (:locals fe))
        (reduce (fn [idx ^LocalSpan l]
                  (let [b (.binding l)]
                    (if-let [cur (get idx b)]
                      (assoc! idx b (update cur :uses conj (local->map l)))
                      idx)))
                idx (:local-uses fe))))
    (transient {}) forms)))

(defn- build-macro-deps
  "{ns-sym {macro-qsym #{fid}}} - the compile-time edges. Each carries the fid of the
  form that expanded it, which is its file."
  [forms]
  (persistent!
   (reduce-kv (fn [idx fid fe]
                (reduce (fn [idx [n mk]]
                          (assoc! idx n (update (get idx n {}) mk (fnil conj #{}) fid)))
                        idx (:macro-deps fe)))
              (transient {}) forms)))

(defn- build-ns-usages
  "{lib #{span}} - where each live ns form writes a library in a :require, a :use,
  a :require-macros or a :use-macros, read out of the form's :ns-specs facts: a
  symbol for a namespace, a string for an npm module. clojure.analysis/
  build-ns-usages, over this model's facts; a library written with no position is
  left out."
  [forms]
  (persistent!
   (reduce-kv (fn [idx _ fe]
                (reduce (fn [idx {:keys [ns requires]}]
                          (reduce (fn [idx {:keys [lib at clause]}]
                                    (if at
                                      (assoc! idx lib (conj (get idx lib #{})
                                                            (assoc at :source (:source fe)
                                                                   :from-ns ns
                                                                   :declaration clause)))
                                      idx))
                                  idx requires))
                        idx (:ns-specs fe)))
              (transient {}) forms)))

(def ^:private index-keys
  "The indexes `derived` is all of, which is what `snapshot` shows."
  [:usages :defs :locals :keyword-usages :macro-usages :macro-deps :host-usages])

(defn- index
  "One derived index of model value `m`, built from its form log and cached until that
  log changes. Ask for the one that answers the question: nothing here forces any of
  the others, which is why there is a cache each."
  [m k]
  (let [forms (:forms m)]
    (cached-by-forms
     (get index-caches k) forms
     (fn []
       (case k
         :usages         (build-spans forms :usages)
         :keyword-usages (build-spans forms :keyword-usages)
         :macro-usages   (build-spans forms :macro-usages)
         :host-usages    (build-spans forms :host-usages)
         :qualifiers     (build-spans forms :qualifiers)
         :defs           (build-defs forms)
         :locals         (build-locals forms)
         :macro-deps     (build-macro-deps forms)
         :ns-usages      (build-ns-usages forms))))))

(defn- derived
  "Every by-entity index for model value `m` as one map - what `snapshot` shows, and
  what a caller wanting several of them off one consistent log should take. It forces
  all of them, so prefer `index` with the key actually needed."
  [m]
  (into {} (for [k index-keys] [k (index m k)])))

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
  :end-column [:dead] [:declaration]}.

  Code the program does not run is included: a use in a #_ carries :dead :discard,
  one in a (comment ...) :dead :comment. It is resolved rather than compiled - see
  commit-dead! - so it can name something the compiler would not have.

  The ns form's own mention is included too, carrying :declaration :refer - the
  name as a :refer, an :only or a :rename writes it. It is not a use of the var and
  does not count as one (from-ns?), but it is a place the name is written and one a
  rename has to rewrite. See record-declares!; clojure.analysis says the same of the
  other compiler. An :import is not among them: what a ClojureScript one names is a
  Closure namespace, which is a host reference - see find-host-usages."
  [var-or-sym]
  (spans->maps (get (index @model :usages) (->var-key var-or-sym))))

(defn definition
  "Definition site recorded for a var, or nil - nil too for a var no live form
  defines (deleted from its file, or in a file never analysed, cljs.core's among
  them)."
  [var-or-sym]
  (some-> (:span (get (index @model :defs) (->var-key var-or-sym))) span->map))

(defn find-keyword-usages
  "Occurrence sites recorded for keyword `kw`. An auto-resolved keyword is recorded
  fully qualified, so ::x in app.core is found as :app.core/x."
  [^Keyword kw]
  (spans->maps (get (index @model :keyword-usages) kw)))

(defn find-namespace-usages
  "Where the namespace named `ns-sym` is required - a set of {:from-ns :source :line
  :column :end-line :end-column :declaration}, the library as an ns form writes it
  and :declaration the clause that writes it, as
  clojure.analysis/find-namespace-usages answers. Its vars and keywords are asked
  about with find-usages and find-keyword-usages. A Closure namespace is answered
  its requires here and nothing else: where it is used as a value, and where its
  vars are, are host references (find-host-usages)."
  [ns-sym]
  (get (index @model :ns-usages) ns-sym))

(defn find-macro-usages
  "Where the source calls macro `macro` - the JVM Var, or its fully-qualified name
  symbol. A set of spans shaped like find-usages'.

  Only calls the source WROTE: a macro called by another macro's expansion is a
  dependency (macro-deps) and not a use. Uses of the same name as a VALUE -
  cljs.core/str passed to map rather than called - are the ClojureScript var's,
  and find-usages has them. A call in a #_ or a (comment ...) is here too, marked
  :dead as find-usages marks one - and so is the name a :refer of a macro writes,
  marked :declaration :refer for its reason."
  [macro]
  (spans->maps (get (index @model :macro-usages)
                    (if (instance? Var macro) (jvm-var-key macro) macro))))

(defn macro-deps
  "The compile-time dependency of ClojureScript namespaces on macros: every macro
  expanded while compiling them, whether the source called it or another macro's
  expansion did. No argument: {ns-sym #{macro-qsym}}. With a namespace symbol: the
  set for that namespace."
  ([] (reduce-kv (fn [acc n mm] (assoc acc n (set (keys mm))))
                 {} (index @model :macro-deps)))
  ([ns-sym] (set (keys (get (index @model :macro-deps) ns-sym)))))

(defn unused-locals
  "Local bindings the source wrote and nothing uses, optionally only those of
  namespace `ns-sym`. Each is the binding's site plus :name and :ns.

  A SITE, NOT A BINDING. A macro may bind one written symbol more than once - a
  variadic defn's parameters are bound by each function it expands to - and a
  binding the macro never reads is not the programmer's to remove while another
  one at the same place is read. So a site is unused only when every binding
  written there is.

  A deftype or defrecord field is never one: it is what the type is, and a field
  nothing reads is still a field every instance has. Nor is the name an fn gives
  itself - (fn step [x] ...) - which clj-kondo does not report either, and which a
  macro often writes as the name of the var it defines: hx's defnc expands to
  (def C (fn C [props] ...)), where the one symbol the source wrote is both.

  A REIFY IS NOT A DEFTYPE FOR THIS, although it compiles to one. Its fields are
  the locals around it, captured wholesale and named where the source bound them,
  and a capture is neither a binding nor a use: the binding is the local's, and
  reading the bare name inside a method body is reading that local. The analyzer
  says which field is which (field-bindings' :captures), record-local! leaves the
  capture out, and analyze-symbol files the body's reads under the local - so a
  local the reify reads is used, and one nothing reads is reported however many
  reifys stand between it and the end of its scope."
  ([] (unused-locals nil))
  ([ns-sym]
   (for [[_ infos] (group-by (juxt :source :line :column)
                             (vals (index @model :locals)))
         :let  [info (first infos)]
         :when (not-any? #(or (:field %) (:fn-name %)) infos)
         :when (every? (comp empty? :uses) infos)
         :when (or (nil? ns-sym) (= ns-sym (:ns info)))]
     (dissoc info :uses))))

(defn find-local-usages
  "Where the local written at `line`:`column` of file `source` is - its binding,
  marked :declaration :binding, and every use of it - or nil where no local is
  written there. clojure.analysis/find-local-usages, and by site for its reason:
  a variadic defn binds its parameters once per function it expands to, and the
  programmer wrote one local."
  [source line column]
  (let [m      @model
        forms  (keep #(get-in m [:forms %]) (get-in m [:source->forms source]))
        defs   (mapcat :locals forms)
        uses   (mapcat :local-uses forms)
        covers (fn [s]
                 (let [l (:line s) c (:column s)
                       el (if (nat-int? (:end-line s)) (:end-line s) l)
                       ec (if (nat-int? (:end-column s)) (:end-column s) c)]
                   (and (not (neg? (compare [line column] [l c])))
                        (not (pos? (compare [line column] [el ec]))))))
        hit    (into #{} (comp (filter covers) (map :binding)) (concat defs uses))
        site   (juxt :line :column)
        sites  (into #{} (comp (filter #(hit (:binding %))) (map site)) defs)
        bound  (into hit (comp (filter #(sites (site %))) (map :binding)) defs)
        place  (fn [l] (cond-> {:source (:source l) :line (:line l) :column (:column l)
                                :from-ns (:lns l)}
                         (nat-int? (:end-line l))   (assoc :end-line (:end-line l))
                         (nat-int? (:end-column l)) (assoc :end-column (:end-column l))))]
    (when (seq bound)
      (into (into #{} (comp (filter #(bound (:binding %)))
                            (map #(assoc (place %) :declaration :binding)))
                  defs)
            (comp (filter #(bound (:binding %))) (map place))
            uses))))

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
        (index @model :host-usages)))

(defn find-host-usages-where
  "Every host reference whose ref satisfies `pred`, with the places it is used:
  {ref #{span}}, the ref in host-ref's shape, :written and all.

  For the questions find-host-usages' partial match cannot ask, and they are
  the ones a person asks about a PACKAGE: every var of one Closure namespace
  (goog.string/trim and goog.string/format are two refs whose names share only
  a namespace), every global under js/console (js/console and js/console.log
  are two names), and for each place which of them it was - which the spans
  alone do not say, since they are filed under the ref and do not carry it."
  [pred]
  (into {}
        (keep (fn [[k spans]] (when (pred k) [k (spans->maps spans)])))
        (index @model :host-usages)))

;; --- namespace lints ------------------------------------------------------------
;;
;; clojure.analysis reads live namespace state for these, and so do they - but a
;; ClojureScript namespace lives in a compile environment rather than in the JVM,
;; so each takes the environment. What a namespace's ns form ESTABLISHED comes from
;; there; what its code USES comes from the model. Both are about the last compile:
;; a file edited since is answered as it was.

(defn- from-ns?
  "Is `s` a use from `ns-sym`, as the unused-* lints count one? A use in a #_ is
  not: the code is gone. A use in a (comment ...) is: a rich comment block is code
  meant to be run at the REPL - clojure.analysis/counts-as-use?.

  Neither is a DECLARATION: what a :refer writes is the very thing these lints ask
  about, so counting it would answer \"is this refer used\" with the refer itself."
  [ns-sym ^Span s]
  (and (= ns-sym (.from-ns s)) (not= :discard (.dead s)) (nil? (.declaration s))))

(defn- used-from
  "The keys of index `m` with at least one span from `ns-sym`."
  [m ns-sym]
  (for [[k spans] m :when (some #(from-ns? ns-sym %) spans)] k))

(defn- written-from
  "Every symbol `ns-sym` wrote to reach the host - see host-ref's :written. Takes the
  `:host-usages` index, which is the only one it reads."
  [host-usages ns-sym]
  (into #{} (keep :written) (used-from host-usages ns-sym)))

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
  (let [m   @model
        nss (fn [ks] (keep #(some-> (namespace %) symbol) ks))]
    (into #{}
          (concat (nss (used-from (index m :usages) ns-sym))
                  (nss (used-from (index m :keyword-usages) ns-sym))
                  (nss (used-from (index m :macro-usages) ns-sym))
                  (keep (fn [r] (case (:kind r)
                                  :goog-var (symbol (namespace (:name r)))
                                  :goog-ns  (:name r)
                                  nil))
                        (used-from (index m :host-usages) ns-sym))))))

(defn unused-aliases
  "Aliases in `ns-sym` nothing uses: {alias target}. A ClojureScript or Closure
  namespace alias is unused when nothing from its target namespace is referenced
  (ns-referenced-namespaces) AND the source nowhere writes the alias itself; a
  JavaScript module's alias when the source never writes it. The target is the
  namespace symbol, or the module's specifier - or [specifier path] for one that
  named a path into the module.

  THE SECOND QUESTION IS THE READER'S, and it is asked because the first cannot
  always be answered: a macro that consumes a qualified symbol at expansion time
  emits nothing naming the target, and one that rebuilds the body it was given -
  core.async's `go' - hands back `cljs.string/f' where the source wrote `s/f'. The
  alias is written either way and the file stops reading without it. It is the union
  of the two and not the spelling alone, because `::s/k' reaches the model as the
  keyword it auto-resolves to and never as the alias token. See
  clojure.lang.IAnalysisSink/qualifierUsage.

  The aliases an :import made are unused-imports', not these."
  [cenv ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns cenv ns-sym)]
    (let [used     (ns-referenced-namespaces ns-sym)
          spelt    (set (used-from (index @model :qualifiers) ns-sym))
          written  (written-from (index @model :host-usages) ns-sym)
          imported (set (keys (env/imports cenv ns-sym)))]
      (merge
       (into {} (for [[a ^Namespace target] (.getAliases n)
                      :let  [t (.getName target)]
                      :when (not (imported a))
                      :when (not (used t))
                      :when (not (spelt a))]
                  [a t]))
       (into {} (for [[a [specifier path]] (env/js-aliases cenv ns-sym)
                      :when (not (written-as? written a))
                      :when (not (spelt a))]
                  [a (if path [specifier path] specifier)]))))))

(defn- macro-view
  "`ns-sym`'s view of the JVM, where :require-macros put its aliases and refers -
  found, never created."
  ^Namespace [cenv ns-sym]
  (.find ^clojure.lang.NamespaceWorld (:macro-world cenv) ns-sym))

(defn- referred-macros
  "The macros `ns-sym`'s ns form brought in by name: {name macro-qsym}, whichever
  clause did it - a :refer in a :require-macros, a :refer-macros, or the plain
  :refer of a :require that the compiler inferred a macro for."
  [cenv ns-sym]
  (when-let [view (macro-view cenv ns-sym)]
    (into {} (for [[sym v] (.getMappings view)
                   :when (instance? Var v)]
               [sym (jvm-var-key v)]))))

(defn unused-refers
  "Names `ns-sym` referred and never uses: {name target}. The target is the var's
  qualified name, a macro's, a Closure name, or a JS module's [specifier export].
  cljs.core's implicit refers are not refers here and are never reported.

  BY HOW THE NAME IS SPELLED, as clojure.analysis/unused-refers has it, because
  that is what a refer is: `(:require [a.b :as x :refer [f]])' and then only ever
  `x/f' is a refer nothing needs, and taking it out changes nothing. So a use
  counts for the refer only where the source wrote the short name - :written nil,
  which is the span's way of saying the var's own name unqualified, or the local
  name a :rename gave it. A name drawn out of a JavaScript module or a Closure
  namespace counts the same way, by the spelling the source wrote.

  The exception is a protocol, which cannot be spelled at all: implementing one in
  a `deftype' or a `reify' is recorded where the protocol was named and with no
  spelling on it (on-protocol-impl), so implementing it counts however it was
  written. clojure.analysis has the same exception for the same reason.

  A NAME MAY BE A VAR, A MACRO, OR BOTH, which is where this parts company with
  Clojure's: a ClojureScript namespace and the macro namespace behind it are two
  universes, and a plain :refer reaches into both - the compiler infers macros for
  a `:require', so (:require [hx.react :refer [defnc]]) refers a macro and nothing
  else. A name is unused when every universe that holds it says so. Not when one
  of them does: where a library has a macro and a var of the same name, calling the
  macro leaves the var unused, and the refer is doing its job."
  [cenv ns-sym]
  (when-let [^Namespace n (env/find-cljs-ns cenv ns-sym)]
    (let [m          @model
          uses       (index m :usages)
          macro-used (set (used-from (index m :macro-usages) ns-sym))
          written    (written-from (index m :host-usages) ns-sym)
          spelt?     (fn [local ^Span s]
                       (let [w (.written s)] (or (nil? w) (= w local))))
          var-used?  (fn [local k]
                       (boolean (some #(and (from-ns? ns-sym %) (spelt? local %))
                                      (get uses k))))
          macros     (or (referred-macros cenv ns-sym) {})
          vars       (into {} (for [[sym v] (.getMappings n)
                                    :when (instance? Var v)
                                    :let  [home (.getName (.ns ^Var v))]
                                    :when (not (#{ns-sym 'cljs.core} home))]
                                [sym (var-key v)]))]
      (merge
       (into {} (for [sym  (distinct (concat (keys vars) (keys macros)))
                      :let [k (get vars sym) mk (get macros sym)]
                      :when (and (or (nil? k) (not (var-used? sym k)))
                                 (or (nil? mk) (not (macro-used mk))))]
                  [sym (or k mk)]))
       (into {} (for [[sym target] (env/goog-refers cenv ns-sym)
                      :when (not (written sym))]
                  [sym target]))
       (into {} (for [[sym target] (env/js-refers cenv ns-sym)
                      :when (not (written sym))]
                  [sym target]))))))

(defn unused-imports
  "Classes `ns-sym` :imported and never names: {name closure-name}."
  [cenv ns-sym]
  (let [written (written-from (index @model :host-usages) ns-sym)]
    (into {} (for [[sym target] (env/imports cenv ns-sym)
                   :when (not (written-as? written sym))]
               [sym target]))))

(defn unused-macro-aliases
  "Macro-namespace aliases in `ns-sym` through which no macro is called:
  {alias jvm-ns}. As with unused-aliases, used means a macro of the target
  namespace is called from `ns-sym`, by whatever name."
  [cenv ns-sym]
  (when-let [view (macro-view cenv ns-sym)]
    (let [used (set (keep #(some-> (namespace %) symbol)
                          (used-from (index @model :macro-usages) ns-sym)))]
      (into {} (for [[a ^Namespace target] (.getAliases view)
                     :let  [t (.getName target)]
                     :when (not (used t))]
                 [a t])))))

(defn unused-macro-refers
  "Macros `ns-sym` referred and never calls: {name macro-qsym}. The macro half of
  unused-refers, which a :require-macros clause is answered out of; a macro call
  carries no spelling, so this is by the macro and not by how it was named."
  [cenv ns-sym]
  (when-let [refs (referred-macros cenv ns-sym)]
    (let [used (set (used-from (index @model :macro-usages) ns-sym))]
      (into {} (remove (comp used val)) refs))))

(defn file-facts
  "What the model holds of file `source`, as it was when it was last compiled -
  clojure.analysis/file-facts, in the same shape:

    {:mtime    the file's mtime when its compile began: the version these are about
     :usages   [{:var qsym ...span}]  var uses, and macro calls marked :macro true;
                                       :written and :var-form as clojure.analysis
     :defs     [{:var qsym ...span}]  in the order the forms define them, a
                                       `declare' marked :declaration :declare
     :invokes  [{:var qsym :argc n ...span}]
     :warnings [{:kind :info ...span}]  what the analyzer warned about, :info its data
     :forms    [{:line :column :ns}]
     :ns-specs [{:ns sym :requires [...] :imports [...]}]  clojure.analysis/ns-specs
                                       of each ns form}

  Nothing here is a verdict: whether a call has the wrong arity, or a use names a var
  that has gone, is a question about the compile environment as it is now, and the
  caller's to ask."
  [source]
  (let [m     @model
        forms (map #(get-in m [:forms %]) (sort (get-in m [:source->forms source])))
        fact  (fn [s] (assoc (span->map s) :var (:entity s)))]
    {:mtime    (get-in m [:file-mtime source])
     :usages   (into [] (concat (sequence (comp (mapcat :usages) (map fact)) forms)
                                (sequence (comp (mapcat :macro-usages) (map fact)
                                                (map #(assoc % :macro true)))
                                          forms)))
     :defs     (into [] (comp (mapcat :defs) (map fact)) forms)
     :invokes  (into [] (comp (mapcat :invokes)
                              (map (fn [i] (assoc (span->map i) :var (:entity i)
                                                  :argc (:argc i)))))
                     forms)
     :warnings (into [] (mapcat :warnings) forms)
     :forms    (mapv #(select-keys % [:line :column :ns]) forms)
     :ns-specs (into [] (mapcat :ns-specs) forms)}))

(defn version
  "An opaque token for the model as it is now: `identical?' to one taken earlier
  exactly when nothing has been analysed, retracted or failed since. What a tool
  compares around an evaluation to know whether what it showed from the model is
  still what the model says."
  []
  @model)

(defn file-mtime
  "The mtime of file `source` when its last compile began - the version of it the
  model is about - or nil for a file the model does not hold, or one that is not a
  file."
  [source]
  (get-in @model [:file-mtime source]))

(defn file-failure
  "How the last compile of file `source` failed, or nil when it compiled to the end:
  {:mtime :line :column :message} - clojure.analysis/file-failure. :mtime is the
  version on disk that does not compile, which is not the one the rest of the model
  is about: a file that fails keeps the facts of its last compile that did not."
  [source]
  (get-in @model [:failures source]))

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

(defn analysed-files
  "The sources this process has compiled and has not since had retracted, as the
  model names them.

  The population `changed-files` and `stale-files` are answers about, and here for
  the difference between the two ways their answer can be empty: \"nothing has
  changed since this process compiled these files\" and \"this process has compiled
  no files\" read identically in an empty answer and are not the same fact. See
  `clojure.analysis/analysed-files`, which answers it for the JVM side."
  []
  (set (for [[source fids] (:source->forms @model) :when (seq fids)] source)))

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
  side's to reload. Without a Clojure model this is `seed`.

  The Clojure files that are gone are asked for once and handed to every call, since
  this asks the same question once per file it tests and each asking costs the
  classpath a lookup per analysed file (clojure.analysis/stale-files)."
  [seed tracked]
  (let [gone (clj-analysis/deleted-files)]
    (into #{} (filter #(some tracked (clj-analysis/stale-files #{%} gone)))
          (clj-analysis/stale-files seed gone))))

(defn changed-macro-files
  "The Clojure macro files (classpath resources, e.g. \"app/macros.clj\") this
  compiler expanded and that the disk has moved on from since the JVM loaded them -
  edited, as far as :macro-loaded knows.

  THE OTHER HALF OF `changed-files', and kept apart from it because they are not
  the same population and cannot be recompiled the same way. `changed-files'
  answers about the files this compiler COMPILED, which is what `stale-files'
  builds on and what `stale-reload!' hands to the ClojureScript compiler; these are
  Clojure files, they are loaded on the JVM rather than compiled here, and putting
  one in that set would hand a .clj to a driver that reads .cljs.

  Answered on its own all the same, because of what a client is left with
  otherwise. A .cljs file goes stale with nothing in it touched, and the only thing
  that can say why is the macro file that changed - so a reload that names the
  stale file and never names its cause is describing an effect. See
  `replique.cljs-analysis/stale', which reports these as changed beside the
  ClojureScript files, and `stale-macro-files', which is this plus the Clojure
  files that expand their macros in turn - the ones that are stale rather than
  edited."
  []
  (let [m       @model
        tracked (into #{} (mapcat keys) (vals (:macro-files m)))]
    (into #{} (for [file tracked
                    :let [t   (get-in m [:macro-loaded file])
                          now (mtime file)]
                    :when (and t now (not= now t))]
                file))))

(defn stale-macro-files
  "The Clojure files (classpath resources, e.g. \"app/macros.clj\") to load again
  before anything is recompiled: the macro files some analysed file expanded that
  changed on disk since the JVM loaded them (`changed-macro-files'); the Clojure
  files the Clojure model has as edited since it loaded them; and, through its macro
  graph, the files that expand their macros at load time - as far as they lead to a
  macro file an analysed file expanded. Plus any a stale-reload! that threw left
  unloaded."
  []
  (let [m       @model
        tracked (into #{} (mapcat keys) (vals (:macro-files m)))]
    (into (into #{} (filter mtime) (:pending-macro-files m))
          (macro-closure (into (changed-macro-files) (clj-analysis/changed-files))
                         tracked))))

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

(defn deleted-files
  "Analysed files that were compiled from a file on disk and whose file is gone -
  deleted, renamed, or left behind by a branch switch. changed-files skips them:
  there is nothing to recompile them from."
  []
  (let [m @model]
    (into #{} (for [[source t] (:file-mtime m)
                    :when (and t (nil? (mtime (get-in m [:locations source]))))]
                source))))

(defn- stale-files*
  "stale-files, given `gone` - the files the disk no longer has. Taken as an
  argument and not asked for here, because both arities below need it and asking
  the disk about every analysed file is a thing to do once."
  [gone]
  (let [m      @model
        reload (stale-macro-files)]
    (into #{} (remove gone)
          (-> (changed-files)
              (into (keys (changed-macro-files* m)))
              (into (for [[source files] (:macro-files m)
                          :when (some reload (keys files))]
                      source))
              ;; one deleted since has nothing to recompile it from
              (into (filter #(mtime (get-in m [:locations %]))) (:pending-sources m))))))

(defn stale-files
  "The analysed files to recompile: those edited since they were compiled
  (changed-files); those that expanded a version of a macro file other than the
  one on disk now; those that expanded a macro from a file stale-macro-files will
  load again, which an edit to another Clojure file can put there; and any a
  stale-reload! that threw left uncompiled. Given `cenv`, also meta-stale-files.

  No cascade among ClojureScript files past that metadata: a var a file uses is
  looked up at run time, so editing the var's file leaves its users' code right.

  AND NEVER A FILE THAT IS GONE. changed-files asks the disk and so skips one by
  itself; the macro paths and meta-stale-files name files the model holds and ask
  the disk about nothing, so a file deleted by a branch switch that also changed a
  macro file it expanded arrived here as a file to compile - and was handed to the
  driver as the empty path its retracted location spells. What has no file to be
  read is deleted-files, which is a different answer and a different thing to do
  about it.

  `gone` is deleted-files, for a caller that has already asked. Asking costs one
  classpath lookup per analysed file, and a caller that wants both answers - what
  to compile and what to drop - would otherwise pay for that walk twice and be
  free to get two answers from two moments of the disk."
  ([] (stale-files* (deleted-files)))
  ([cenv] (stale-files cenv (deleted-files)))
  ([cenv gone]
   (into (stale-files* gone) (remove gone) (meta-stale-files cenv))))

;; --- prune ----------------------------------------------------------------------

(defn file-def-vars
  "The fully-qualified names of the vars file `source` has a def form for, as the
  model has it now.

  READ OFF THE FILE'S OWN FORMS rather than by walking every def in the model, which
  is what it did and what it was asked once per file recompiled: the model it walked
  grows with the project while the file does not.

  The same answer, and the `:defs` lookup is what keeps it so: a name two files define
  belongs to the one whose def WON - the highest fid - so a file's own def form is in
  its answer only while `:defs` still names it as that def's file. Which is what
  filtering the whole index by span source said."
  [source]
  (let [m     @model
        defs  (index m :defs)
        forms (:forms m)]
    (into #{} (for [fid     (get (:source->forms m) source)
                    ^Span s (:defs (get forms fid))
                    :let    [k (.entity s)]
                    :when   (= source (:source (:span (get defs k))))]
                k))))

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
  (let [m    @model
        ;; `:defs` and nothing else, since that is all it takes to say whether a def
        ;; has gone. The usage index is what the warning reads, and it is forced only
        ;; once something has actually been pruned.
        defs (index m :defs)
        gone (vec (for [[k old] prior
                        :when (and old
                                   (nil? (get defs k))
                                   (identical? old (cljs-var cenv k)))]
                    k))]
    (when (seq gone)
      (let [usages (index m :usages)]
        (doseq [k gone]
          (when-let [us (seq (remove :dead (get usages k)))]
            (binding [*out* *err*]
              (println "WARN: pruning" (str k) "still referenced at"
                       (vec (sort (for [u us] [(:source u) (:line u) (:column u)])))))))))
    (doseq [k gone] (env/remove-var! cenv k))
    ;; AFTER the removal and not before it: what this says is that the name has
    ;; gone, and it has not gone until it is gone. A reload is the one thing that
    ;; takes a definition away without anybody having typed anything, so it is the
    ;; one that has to say so - see clojure.analysis/*defined*.
    (doseq [k gone]
      (defined! {:dialect :cljs :op :remove :ns (symbol (namespace k)) :var k}))
    gone))

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

(defn- lib-names
  "The namespace-name symbols the specs of a `:require' / `:use' /
  `:require-macros' / `:use-macros' clause name, prefix lists expanded.

  A spec is a symbol, or a sequential whose first element is a name and whose rest
  is either options - which start with a keyword - or, when it does not, more specs
  carrying that name as a prefix. That is the rule the ns parser itself reads them
  by, and the reason the shapes cannot be told apart any other way: `[a b]' is the
  prefix list a.b and `[a :as b]' is the lib a.

  A STRING WHERE THE NAME WOULD BE IS NOT ONE, and that is ClojureScript's own
  addition: `[\"react\" :as react]' requires a JavaScript module, which is not a
  file this compiles and not a file anything here could be ordered against.
  (See `clojure.analysis/lib-names', which is this without that case.)"
  [specs]
  (mapcat (fn [spec]
            (cond
              (symbol? spec) [spec]
              (sequential? spec)
              (let [[head & more] spec]
                (when (symbol? head)
                  (if (or (empty? more) (keyword? (first more)))
                    [head]
                    (map #(symbol (str head "." %)) (lib-names more)))))
              :else nil))
          specs))

(defn- ns-declaration
  "The `ns' form of source `source', read off the disk AS IT IS NOW - the one thing
  about a file that is about to be recompiled that neither the model nor the compile
  environment can answer, because everything either of them holds about it was
  written the last time it compiled.

  Read with the :cljs feature, since that is the dialect being ordered: a .cljc
  whose requires differ by dialect is being read for what a ClojureScript compile
  of it will do.

  Nil when the file has no `ns' form, and nil when it will not read for any reason
  whatever, which is why every last thing in here is caught. The only use of the
  answer is to put two files being recompiled in an order, nothing is lost by not
  having it, and a file that does not read is the compiler's to complain about a
  moment later, in its own words and at the right place."
  [source]
  (try
    (when-let [f (location-file (or (get-in @model [:locations source]) source))]
      (with-open [r (java.io.PushbackReader. (io/reader f))]
        (binding [*read-eval* false
                  *default-data-reader-fn* (fn [_tag value] value)]
          (let [opts {:read-cond :allow :features #{:cljs} :eof ::eof}]
            (loop []
              (let [form (read opts r)]
                (cond
                  (= ::eof form)                         nil
                  (and (seq? form) (= 'ns (first form))) form
                  :else                                  (recur))))))))
    (catch Throwable _ nil)))

(defn- ns-sources
  "The sources namespace `n' could be compiled from: the classpath path the compiler
  derives from the name, in each extension this side reads. No .clj: a Clojure file
  is a macro file here, and macro files are loaded before any of this and are never
  among the sources being ordered."
  [n]
  (let [base (-> (str n) (.replace \- \_) (.replace \. \/))]
    [(str base ".cljs") (str base ".cljc")]))

(defn- disk-require-graph
  "Forward dependency graph over `sources' only, read from their `ns' forms ON DISK:
  {source #{dep-source}} where the new source of `source' requires a namespace that
  another file being recompiled holds. Nothing outside `sources', and no self-edges.

  THE EDGE THE COMPILE ENVIRONMENT CANNOT HAVE. `env/requires' answers what the ns
  form said the LAST time this namespace compiled, so it knows every dependency the
  old source had and none that the edit introduces - and an edit that first reaches
  into a file this one never required before is exactly the one whose order matters,
  because the definition it has come for is a definition that was not there before.
  Compiled in the wrong order it is `No such var', from the analyzer, naming the
  alias. Switching branches does it wholesale.

  A require is the declaration of that reach, it is written at the top of the new
  file, and reading it costs one pass of the reader over a file that is about to be
  handed to the compiler anyway.

  A namespace is matched to a file the way the compiler matches one - the name, with
  dashes to underscores and dots to slashes - and also through the model, for a file
  whose namespace is not named after it. Neither has to find anything: a require of
  something not being recompiled says nothing about the order of what is.

  This is `clojure.analysis/file-require-graph', for the ClojureScript sources of a
  ClojureScript reload."
  [sources]
  (let [m        @model
        nodes    (set sources)
        ns->srcs (reduce-kv (fn [acc _ fe]
                              (if-let [n (:ns fe)]
                                (update acc n (fnil conj #{}) (:source fe))
                                acc))
                            {} (:forms m))
        srcs-of  (fn [n] (filter nodes (into (set (ns-sources n)) (get ns->srcs n))))
        clause?  (fn [x] (and (sequential? x)
                              (#{:require :use :require-macros :use-macros} (first x))))]
    (reduce
     (fn [g source]
       (if-let [form (ns-declaration source)]
         (let [deps (into #{} (comp (filter clause?)
                                    (mapcat #(lib-names (rest %)))
                                    (mapcat srcs-of)
                                    (remove #(= source %)))
                          (rest form))]
           (if (seq deps) (assoc g source deps) g))
         g))
     {} nodes)))

(defn- in-require-order
  "`sources' ordered so that a file comes after the files it requires, as far as
  they are among `sources' - the order a runtime should run them in.

  Two graphs, and the second is the one an edit can change: what the compile
  environment recorded when each namespace last compiled, and what the `ns' forms on
  disk say now - see `disk-require-graph'. A require that is new since the last
  compile exists only in the second, and it is the one most likely to matter."
  [cenv sources]
  (let [ns-of (into {} (for [s sources] [(first (file-namespaces s)) s]))
        disk  (disk-require-graph sources)
        deps  (fn [s] (into (set (keep ns-of (env/requires cenv (first (file-namespaces s)))))
                            (get disk s)))]
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
  (deleted-files), and with :prune their namespaces stop being ones this
  environment compiled (env/forget-ns!), so that one whose file comes back is
  compiled again rather than held as the empty shell pruning leaves. Returns

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
  ;; The one reading of the disk both answers come from: what is gone is what is
  ;; dropped, and it is also what must not be in what is compiled.
  (let [gone    (deleted-files)
        mfiles  (stale-macro-files)
        sources (in-require-order cenv (stale-files cenv gone))
        deleted (sort gone)
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
                  ;; Read before the retraction, which is what knows them.
                  (let [nss   (file-namespaces s)
                        prior (when prune (file-def-var-snapshot cenv s))]
                    (retract-file! s)
                    (when prune
                      (swap! pruned into (prune-vars! cenv prior))
                      ;; AND THE NAMESPACE STOPS BEING ONE THIS ENVIRONMENT
                      ;; COMPILED - env/forget-ns!, which is what
                      ;; clojure.analysis's forget-lib! is on the jvm. Without it
                      ;; the vars go and the namespace stays, marked compiled,
                      ;; and the driver never compiles that namespace again
                      ;; because it is sure it already has: the file coming back
                      ;; - a branch switched away from and back - leaves every
                      ;; use of it unresolvable.
                      ;;
                      ;; Only where no live form still holds the namespace: two
                      ;; files can share one, and the one still there declares
                      ;; it.
                      (doseq [n nss :when (empty? (ns-forms n))]
                        (env/forget-ns! cenv n)))))
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
