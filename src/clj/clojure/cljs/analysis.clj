;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "In-memory semantic model of the ClojureScript this compiler compiled:
  var usages and definitions, local bindings and their uses, and keyword
  occurrences, with precise source spans, across files.

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
  the ClojureScript namespace being compiled.

  DISK ONLY. Nothing typed at a REPL reaches the model - the REPL does not go
  through the driver's file loop - so it stays in step with what is on disk.

  cljs.core IS NOT ANALYSED, as clojure.core is not analysed on the JVM (it loads
  AOT and never passes the sink). Uses of its vars from analysed files are
  recorded like any other; its own definitions are not, so `definition` of a core
  var is nil, and the var's own :file / :line metadata is where to look instead.

  The reload unit is the FILE, keyed by the label the driver gives it - the path
  under its source directory, my_lib/core.cljs, which is also what a var's :file
  records. Each form keeps the namespace it was compiled in as :ns.

  Drivers: run-analysis, load-file!, retract-file!, reset-model!. Queries:
  find-usages, definition, find-keyword-usages, unused-locals, file-forms, file-namespaces, ns-forms,
  snapshot."
      :author "replique-cljs"}
    clojure.cljs.analysis
  (:require [clojure.cljs.ast :as ast]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env])
  (:import [clojure.lang IAnalysisSink Keyword RT Var]
           [java.util ArrayList]))

;; stored (write model - mutated only by commit-frame! and retraction):
;;   :forms          {fid {:ns :source :line :column + one key per non-empty fact
;;                         category: :usages :defs :locals :local-uses
;;                         :keyword-usages}}
;;   :source->forms  {source #{fid}}
;;   :locations      {source File-or-URL}  where each file was last found
;;   :next-fid       long
;; derived (build-index, cached by :forms identity):
;;   :usages         {qsym #{span}}
;;   :defs           {qsym {:span span}}   only vars a live form defines
;;   :locals         {binding {:ns :name ...span :uses #{span}}}
;;   :keyword-usages {kw #{span}}
(def ^:private empty-model
  {:forms {} :source->forms {} :locations {} :next-fid 0})

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
(def ^:private ^:const N-CATS       5)

(def ^:private cat-keys [:usages :defs :locals :local-uses :keyword-usages])

;; A form being compiled. `pos` is [line column], corrected by form-start once the
;; form has been read; `cats` holds one ArrayList per fact category, made on first use.
(deftype OpenForm [^long seq ^longs pos ^objects cats])

;; A file being compiled. `ignored` is cljs.core's frame, which is pushed like any
;; other - so a form's facts always land in the frame of the file it belongs to -
;; and whose facts go nowhere. `forms` is the stack of open forms, `buffer` the
;; finished ones, `counter` the next begin-order rank.
(deftype FileFrame [source location ignored ^ArrayList forms ^ArrayList buffer ^longs counter])

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

                :var (record-usage! of source ns n)

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
                          :locations (assoc (:locations m) source (.location fr))
                          :next-fid (+ base (long begin-count)))))))
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
                         (assoc fe (nth cat-keys i) (vec l))
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

;; One per run-analysis. `files` is the stack of files being compiled; it is touched
;; only by the thread the compilation runs on, which is the thread that bound it.
(deftype AnalysisSink [^ArrayList files reader]
  driver/CompileSink
  (reader-sink [_] reader)
  (begin-file [_ ns-sym source location]
    (.add files (FileFrame. source location (= 'cljs.core ns-sym)
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
  (binding [driver/*sink* (let [files (ArrayList.)]
                            (->AnalysisSink files (->ReaderSink files)))]
    (thunk)))

(defn load-file!
  "Compile the file at `path` under the sink - clojure.cljs.driver/compile-file!,
  whose options these are - replacing that file's forms in the model. A file that
  fails to compile keeps its prior forms. Returns the driver's result."
  [cenv path opts]
  (run-analysis #(driver/compile-file! cenv path opts)))

(defn retract-file!
  "Remove every form of file `source` (its label, e.g. \"app/util.cljs\") from the
  model. Other files' usages of its vars are theirs, and stay."
  [source]
  (swap! model (fn [m] (reduce retract-form m (get-in m [:source->forms source]))))
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
                           idx (:keyword-usages fe)))))
             (transient {:usages (transient {}) :defs (transient {}) :locals (transient {})
                         :keyword-usages (transient {})})
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
            :defs   (reduce-kv (fn [a k e] (assoc a k (update e :span span->map)))
                               {} (:defs idx))})))
