;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Reading ClojureScript source with the vendored reader.

  The reader needs no ClojureScript-specific fork. Everything that resolves a
  symbol while reading - auto-resolved keywords (::kw, ::alias/kw), namespaced
  map literals (#::alias{}), and syntax-quote - already routes through
  clojure.lang.LispReader$Resolver when *reader-resolver* is bound, an extension
  point upstream added for exactly this purpose. WorldResolver below implements it
  against a NamespaceWorld, so those forms resolve in the ClojureScript symbol
  table rather than the JVM's.

  Reading adds the three things the fork made switchable: the platform feature
  (:cljs instead of :clj, so reader conditionals take the right branch), source
  positions (recorded without an analysis sink), and #= disabled. See
  doc/cljs-compiler.md.

  Two entry points over the same machinery: read-forms for a file, read-one for a
  REPL, which must not read past the form it was given - and read-one+text beside
  it, which also hands back the characters the form was written with, because a
  source map for a typed form has nowhere else to get them (doc/cljs-compiler.md
  §5.46).

  Reading only. Nothing here evaluates, analyses, or interns: the forms come back
  as data with source spans attached, and it is the caller's job to advance
  env/*current-ns* as it processes each (ns ...) form."}
  clojure.cljs.reader
  (:require [cljs.instant]
            ;; for JSValue alone, and requiring it is what makes the class LOAD:
            ;; an :import does not load a namespace, and somebody else's macro
            ;; imports this class without requiring anything that would
            [cljs.tagged-literals]
            [clojure.cljs.env :as env]
            [clojure.cljs.macroexpand :as mx]
            [clojure.java.io :as io])
  (:import [cljs.tagged_literals JSValue]
           [clojure.lang Compiler LispReader LispReader$Resolver
            LineNumberingPushbackReader Namespace NamespaceWorld Symbol Var]
           [java.io Reader StringReader]))

;; --- #js ------------------------------------------------------------------

(defn read-js
  "Data reader for #js. Wraps the form rather than building anything: what
  #js [1 2] and #js {:a 1} become is the emitter's decision, not the reader's.

  THE MARKER IS ClojureScript'S OWN CLASS, and not a second one of ours, because
  the question it answers is asked by code this project did not write. A macro
  that rewrites the body it was handed has to recognise a #js literal on the way
  past: core.async's ioc_macros.clj imports cljs.tagged_literals.JSValue and asks
  `instance?' about every form it lifts into a state machine. A private marker
  answers that question NO - and answers it SILENTLY, because upstream's dispatch
  tests map? before it tests the class and a defrecord is a map, so #js {:a 1}
  inside a (go ...) came out as (hash-map :val {:a 1}): a ClojureScript map where
  a JavaScript object was written, compiled clean. ClojureScript's own
  cljs/tagged_literals.cljc is vendored verbatim for this, in src/compat rather
  than beside the compiler - two copies of a deftype in one jvm are two classes
  with one name, which is this same bug read backwards. See
  doc/cljs-compiler.md 5.68.

  The TABLE below is still ours. Upstream's read-js also refuses an object literal
  whose keys are not strings or unqualified keywords, and taking that on would be
  a behaviour change nobody asked for - what was wanted is the type."
  [form]
  (JSValue. form))

;; --- resolution -----------------------------------------------------------

(deftype WorldResolver [cenv ^NamespaceWorld world ^NamespaceWorld macro-world]
  LispReader$Resolver

  ;; Never nil: LispReader dereferences this without a null check when reading
  ;; #::{...} (LispReader.java:783).
  (currentNS [_]
    env/*current-ns*)

  ;; ClojureScript has no host classes, so a symbol is never a class name. Returning
  ;; nil here is what makes the reader fall through to alias resolution for Foo/bar
  ;; and leave js/Date alone.
  (resolveClass [_ _sym]
    nil)

  ;; A MACRO ALIAS RESOLVES TOO, and that is the whole of ::macros/foo.
  ;;
  ;; A :require-macros alias lives on the namespace's MACRO VIEW - a namespace in
  ;; the macro world whose aliases point at JVM namespaces (env/require-macros!) -
  ;; so a resolver that consults only the runtime world cannot see it, and
  ;; ::macros/foo reached LispReader as `Invalid token`. It is a keyword: what it
  ;; needs from the alias is a NAME, and the macro namespace has one.
  ;;
  ;; cljs.analyzer merges the same two maps for the same purpose - its reader is
  ;; given (merge (:requires ns) (:require-macros ns)) as an alias map
  ;; (analyzer.cljc:4729). The merge order there lets a macro alias WIN a
  ;; collision; this asks the runtime world first, so the runtime alias wins.
  ;; Nothing in either suite has a collision to distinguish them - the shape that
  ;; would, requiring two different namespaces under one alias, is a mistake in
  ;; either reading - and resolving the way every other name in this compiler
  ;; resolves is the tie-break worth having.
  (resolveAlias [_ sym]
    (or (when-let [^Namespace ns (.find world ^Symbol env/*current-ns*)]
          (when-let [^Namespace target (.lookupAlias ns sym)]
            (.getName target)))
        (when-let [^Namespace view (.find macro-world ^Symbol env/*current-ns*)]
          (when-let [^Namespace target (.lookupAlias view sym)]
            (.getName target)))))

  ;; A ClojureScript var is a root-unbound Var interned in a namespace of that world:
  ;; identity plus metadata, never invoked.
  ;;
  ;; env/resolve-var RATHER THAN getMapping, and the difference is cljs.core.
  ;; Mappings cover what a namespace interns and what it refers, and cljs.core is
  ;; neither: every namespace gets it through the implicit require, whose refer
  ;; half is a RULE in resolve-var rather than a mapping on the Namespace
  ;; (doc/cljs-compiler.md 5.12). So `keyword? read against getMapping found
  ;; nothing and syntax-quote fell back to the current namespace, making it
  ;; app.core/keyword? - a name that does not exist, in every macro and every
  ;; quoted form in the tree. cljs.spec.alpha is what showed it: it records the
  ;; resolved predicate of a spec, so (s/explain-data keyword? nil) reported
  ;; :pred cljs.spec-test/keyword?.
  ;;
  ;; Asking the same function the analyzer asks is also the point of that function
  ;; existing - see its docstring. A macro, an analyzed symbol and a syntax-quote
  ;; now agree by construction.
  (resolveVar [_ sym]
    ;; A DOTTED NAME IS LEFT ALONE, and left alone before anything is asked about
    ;; it. `clojure.core is 'clojure.core, not app.core/clojure.core -
    ;; cljs/core_test.cljs checks exactly that (test-cljs-2109, "syntax quoted
    ;; dotted symbol without namespace should resolve to itself").
    ;;
    ;; Clojure says the same thing in Compiler.resolveSymbol's first two lines -
    ;; "already qualified or classname?" - and cljs.tools.reader says it in
    ;; resolve-symbol's, with the comment "if there is a period, it is interop".
    ;; It has to be said HERE because LispReader's syntax-quote takes the Resolver
    ;; path whenever there is a resolver and so never reaches
    ;; Compiler.resolveSymbol, which would otherwise have answered it.
    ;; A MACRO RESOLVES TOO, after the var and never instead of one - the same
    ;; order analyzer-api/resolve uses, and for a reason that is particular to
    ;; ClojureScript: a macro is NOT a var of the world being compiled. `fn is a
    ;; core macro with no cljs.core var behind it, so asking resolve-var alone
    ;; answered nil and syntax-quote fell back to the current namespace - making
    ;; `(fn [~'%] ...) inside cljs/spec/alpha.cljs read as cljs.spec.alpha/fn,
    ;; which is the name (s/explain-data (s/? keyword?) :k) then reports. In
    ;; Clojure the question does not arise, because a macro IS a var there.
    ;;
    ;; mx/macro-var with no analysis env, because there is none at READ time and
    ;; none is wanted: Clojure's own syntax-quote does not consult locals either.
    ;; What it does consult is (:refer-clojure :exclude [...]), which it must.
    ;; §5.34.
    (if (pos? (.indexOf (name sym) "."))
      sym
      (when-let [^Var v (or (env/resolve-var cenv sym)
                            (mx/macro-var cenv nil sym))]
        (Symbol/intern (str (.getName (.ns v))) (str (.sym v)))))))

(defn resolver
  "A LispReader$Resolver resolving in `cenv`'s ClojureScript world, against
  whichever namespace `cenv` names at the moment each form is read."
  ^LispReader$Resolver [cenv]
  (->WorldResolver cenv (:world cenv) (:macro-world cenv)))

;; --- reading --------------------------------------------------------------

(def ^:private reader-resolver-var
  "clojure.core/*reader-resolver* is interned by RT, not def'd in core.clj, so it
  has no reader syntax of its own here."
  (resolve 'clojure.core/*reader-resolver*))

(defn read-queue
  "#queue [1 2] - ClojureScript's own tagged literal, and the only one of the
  three this namespace has to add. #inst and #uuid are Clojure's and arrive in
  default-data-readers already.

  A FORM RATHER THAN A VALUE, which is cljs.tagged-literals/read-queue verbatim
  and is why nothing in the emitter knows about queues: what the reader hands
  back is an ordinary call, analyzed and emitted like any other. The elements are
  a vector literal, so they are expressions and a queue literal can hold one."
  [form]
  (when-not (vector? form)
    (throw (RuntimeException. "Queue literal expects a vector for its elements.")))
  (list 'cljs.core/into 'cljs.core.PersistentQueue.EMPTY form))

(def ^:private cljs-data-readers
  "The tags this compiler reads. Clojure's, plus ClojureScript's #queue, minus
  Clojure's #inst.

  #INST IS OVERRIDDEN AND IT MATTERS. Clojure's reader builds a java.util.Date,
  and a java.util.Date is parsed with the JVM's hybrid calendar - Julian before
  the 1582 cutover, Gregorian after. JavaScript's Date is PROLEPTIC Gregorian all
  the way back, so #inst \"1500-01-10\" read Clojure's way and emitted as its
  epoch milliseconds is a JavaScript Date reading 1500-01-01. Nine days out, and
  silently.

  cljs.instant/read-instant-instant is ClojureScript's answer to the same problem
  (CLJS-3291) and is vendored beside this: it parses with Clojure's own grammar
  and constructs a java.time.Instant, which is ISO-8601 and so proleptic, which
  is JavaScript's model exactly. Their reader-test asserts the difference at four
  dates around the cutover."
  (assoc default-data-readers
         'js #'read-js
         'queue #'read-queue
         'inst #'cljs.instant/read-instant-instant))

(defn- load-data-reader-file
  "One data_readers.cljc, merged into `mappings`.

  Read with the platform feature set to :cljs, which is the whole reason this
  cannot simply borrow clojure.core/*data-readers*: RT loads the same files at
  startup and takes the :clj branch of every reader conditional in them, so a tag
  whose reader differs per platform - test/custom-form in ClojureScript's own
  fixture - would be bound to the wrong function. cljs.analyzer reads them itself
  for the same reason (load-data-reader-file, analyzer.cljc:637).

  Refuses a file that is not a map, a key that is not a symbol, and a tag two
  files disagree about, with the messages cljs.analyzer uses."
  [mappings ^java.net.URL url]
  (with-open [rdr (LineNumberingPushbackReader. (io/reader (.openStream url)))]
    (let [new-mappings (with-bindings* {LispReader/PLATFORM_FEATURE :cljs
                                        #'*read-eval* false}
                         #(read {:eof nil :read-cond :allow} rdr))]
      (when-not (map? new-mappings)
        (throw (ex-info "Not a valid data-reader map" {:url url})))
      (reduce (fn [m [k v]]
                (when-not (symbol? k)
                  (throw (ex-info "Invalid form in data-reader file"
                                  {:url url :form k})))
                (when (and (contains? mappings k) (not= (mappings k) v))
                  (throw (ex-info "Conflicting data-reader mapping"
                                  {:url url :conflict k :mappings m})))
                (assoc m k v))
              mappings
              new-mappings))))

(defn- user-data-readers*
  []
  (let [syms (reduce load-data-reader-file {}
                     (enumeration-seq
                      (.getResources (.getContextClassLoader (Thread/currentThread))
                                     "data_readers.cljc")))]
    ;; the reader function is a JVM var, so its namespace has to be loaded before
    ;; it can be found. A namespace that will not load is not an error here:
    ;; ClojureScript's own fixture is a .cljc whose :cljs branch names js/Array,
    ;; and loading it as Clojure is neither possible nor needed unless one of its
    ;; tags is actually used. cljs.analyzer swallows the same throw.
    (doseq [ns (distinct (map (comp symbol namespace) (vals syms)))]
      (try (require ns) (catch Throwable _)))
    (into {}
          (keep (fn [[tag sym]]
                  (when-let [v (find-var sym)]
                    ;; the FUNCTION, not the var: a var is IReference and cannot
                    ;; carry with-meta. :sym is how the runtime half names the
                    ;; function again - cljs.reader/add-data-readers emits a call
                    ;; to it, in ClojureScript, from this symbol
                    [tag (with-meta @v {:sym sym})])))
          syms)))

;; What `user-data-readers' read, until something says it is to be read again.
(def ^:private data-readers-read (atom nil))

(def user-data-readers
  "Every tag a data_readers.cljc on the classpath registers, as {tag f}, where f is
  the JVM function that reads it, carrying the symbol that names it under :sym.

  THE TAGS OF A PROGRAM, as against cljs-data-readers, which are the tags of the
  language. Both are read at compile time; only these have a runtime half, because
  #js and #queue hand back a marker and a form rather than a value.

  Read once and kept, as cljs.analyzer's load-data-readers is: scanning every jar
  for each form read would be the reader's dominant cost. Kept until
  `forget-data-readers!', which is what a library added to the running process
  asks for - the one way the files change while a JVM runs."
  (fn []
    (or @data-readers-read
        (reset! data-readers-read (user-data-readers*)))))

(defn forget-data-readers!
  "Read the data_readers.cljc files again the next time a tag is asked for.

  For whoever has just put something on the classpath - replique, adding a
  library to a running process. A library is where those files come from, so
  the tags it brings are not known until they are read again."
  []
  (reset! data-readers-read nil))

(def ^:dynamic *host-data-readers*
  "Tags the thing DRIVING this reader adds, on top of the language's and the
  program's. Nil, which is what a compilation uses.

  It exists because `with-cljs-reader*' below binds *data-readers* rather than
  adding to it - it has to, since the JVM's own tags are read with the JVM's
  reader conditional and so cannot simply be inherited (see load-data-reader-file)
  - and a REPL host that speaks to its client in tagged literals is then unable to
  read its own directives. Replique's #replique/ns is the case: a client says
  which namespace to read the next form in, in band, and the reader that must
  understand it is this one.

  THE HOST'S TAGS WIN, which is the reverse of what a program would want for its
  own and is right for these: a host that cannot read the directives it documents
  cannot be driven at all, while a program that defined a tag under the host's
  name has shadowed something it does not own.

  DYNAMIC, because it is a property of the caller rather than of the environment:
  one REPL reading on one thread adds them, and another thread compiling in the
  same environment does not. A host binds it around the READ and not around what
  follows - a form that sends the driver into a file must not put the host's tags
  into that file's language."
  nil)

(def ^:dynamic *analysis-sink*
  "What Compiler/ANALYSIS_SINK is while ClojureScript is read: nil, or the sink
  clojure.cljs.analysis hands the driver for the read of one top-level form.

  ALWAYS BOUND BY with-cljs-reader*, nil included, and the nil is the half that
  is not about ClojureScript analysis at all. The reader reports a keyword to
  whatever sink is bound (LispReader, keywordUsage), and Clojure's analysis binds
  one around a whole load - so a ClojureScript compile triggered inside a Clojure
  analysis would file this file's keywords under the Clojure form that triggered
  it, attributed to the JVM's *ns*."
  nil)

(defn with-cljs-reader*
  "Invoke `thunk` with the vendored reader configured to read ClojureScript in
  `cenv`, resolving against whichever namespace `cenv` names.

  Six bindings, three of them the switches the fork added:
    *data-readers*      the language's tags, the program's (user-data-readers),
                        and the host's (*host-data-readers*)
    *reader-resolver*   resolution goes to the ClojureScript world, not the JVM's
    PLATFORM_FEATURE    :cljs, replacing :clj, so #?(:clj a :cljs b) yields b
    RECORD_POSITIONS    spans on symbols/keywords/collections, with no sink
    *read-eval*         false - #= evaluates JVM code and has no place here
    ANALYSIS_SINK       *analysis-sink* - see that var"
  [cenv thunk]
  (with-bindings* {reader-resolver-var    (resolver cenv)
                   LispReader/PLATFORM_FEATURE :cljs
                   Compiler/RECORD_POSITIONS   true
                   Compiler/ANALYSIS_SINK      *analysis-sink*
                   #'*read-eval*          false
                   #'*data-readers*       (merge cljs-data-readers
                                                 (user-data-readers)
                                                 *host-data-readers*)}
    thunk))

(defn push-back-reader
  "`src` - a string, a Reader, or a reader already of this kind - as the reader
  read-one and read-forms read from. Line-numbering, so the positions recorded
  while reading are real ones.

  Idempotent, so a caller that holds a reader across forms (a REPL does) can pass
  it to either function without it being wrapped a second time and losing the
  characters the outer buffer had already taken."
  ^LineNumberingPushbackReader [src]
  (if (instance? LineNumberingPushbackReader src)
    src
    (LineNumberingPushbackReader.
     (if (string? src) (StringReader. ^String src) ^Reader src))))

(def positional-meta
  "The metadata keys the READER hangs on everything it reads: where the form was.

  Here rather than at either caller because this is the namespace that puts them
  there, and both the analyzer and the emitter have to take them off again -
  metadata on a literal is carried into the output (doc/cljs-compiler.md 5.21),
  and carrying these would put the line number of a source file into a running
  program's data.

  :file and :source are not added by the reader as it is called here, which reads
  from a string with no name; they are added when tools.reader is given one, and
  are in the list so that the answer does not depend on how the reader was
  started. cljs.analyzer elides the same keys, in elide-reader-meta."
  #{:line :column :end-line :end-column :file :source})

(defn program-meta
  "The metadata on `form` that a PROGRAM can see: what was written, without what
  the reader added. nil when there is nothing left, so a caller can ask `if`.

  Not simply (meta form): every collection the reader reads carries its position,
  so `(meta '[1 2])` is never empty and a naive carry would emit a map of line
  numbers around every literal in the file."
  [form]
  (when (instance? clojure.lang.IObj form)
    (not-empty (apply dissoc (meta form) positional-meta))))

(defn read-one
  "The next form of `rdr`, read in `cenv`, or `eof` if there is nothing left to
  read.

  The one-form sibling of read-forms, and what a REPL reads with. Two differences
  follow from reading one form at a time rather than a file:

  The caller keeps the reader, so the position survives between calls, and only
  the characters of this form are consumed. That is what lets a form change the
  current namespace and have the next form resolve in the new one - nothing has
  been read ahead of it yet.

  `eof` is the caller's own object, compared by identity. Every value is a form
  some source can read, nil and false included, so there is no sentinel that could
  be reserved in-band.

  A malformed form throws, leaving `rdr` positioned wherever the reader gave up -
  usually inside the form. Recovering from that, by discarding the rest of the
  line or dropping the connection, is a policy the REPL owns; the reader has no
  basis for choosing."
  [cenv rdr eof]
  (let [rdr (push-back-reader rdr)]
    (with-cljs-reader* cenv
      #(read {:read-cond :allow :eof eof} rdr))))

(defn- newlines-in ^long [^String s]
  (loop [i 0, n 0]
    (let [j (.indexOf s (int \newline) i)]
      (if (neg? j) n (recur (inc j) (inc n))))))

(defn- form-text
  "The captured characters `captured` cut back to the form itself, or nil if the
  arithmetic below does not land inside them.

  THE CAPTURE ENDS AT THE FORM'S LAST CHARACTER - a terminator is read and then
  unread, and LineNumberingPushbackReader's unread pops it back off the capture -
  so what is in front of the form is everything the capture holds that the form
  does not. Counting it is arithmetic and not a scan, because a scan would have to
  decide what being in front of a form means: whitespace, a comment and a #_ form
  are all in front of it and look nothing alike.

  The newlines in front of it are (those in the capture) minus (those in the form),
  and the form spans end-line minus line of them. Skipping that many lands at the
  start of the form's first line, and (dec column) more characters lands on the
  form.

  WHEN THERE ARE NONE the form shares a line with whatever came before it, and then
  - and only then - the reader's column before the read is where the capture began.
  In the other case it is not trustworthy: a form terminated by a newline leaves
  that newline pushed back, and the reader has counted the line without being able
  to give it back."
  [^String captured ^long col0 m]
  (let [line (long (:line m))
        col  (long (:column m))
        span (- (long (or (:end-line m) line)) line)
        ahead (- (newlines-in captured) span)
        i (if (pos? ahead)
            (loop [i 0, k ahead]
              (if (zero? k)
                (+ i (dec col))
                (let [j (.indexOf captured (int \newline) i)]
                  (if (neg? j) -1 (recur (inc j) (dec k))))))
            (- col col0))]
    (when (<= 0 i (.length captured))
      (subs captured i))))

(defn read-one+text
  "read-one, and the source text of the form it read: [form text].

  `text` is exactly the characters of the form, with whatever came before it on the
  way removed, so its first character is the one at the (:line, :column) the form
  carries. That is what a source map for a REPL input needs and the only place it
  can come from: a map embeds its source (clojure.cljs.source-map/encode) and a
  typed form is not on disk anywhere.

  `text` is nil at eof, nil for a form carrying no position - a bare number or
  keyword has no metadata, and emits nothing a map could point at - and nil if the
  reader cannot capture, which is every reader but this one.

  A SECOND ENTRY POINT rather than a change to read-one, because the capture costs
  a StringBuilder per form and most callers of read-one are reading a file, whose
  text they already hold as one string (clojure.cljs.driver/compile-source!)."
  [cenv rdr eof]
  (let [rdr (push-back-reader rdr)]
    (if-not (instance? LineNumberingPushbackReader rdr)
      [(read-one cenv rdr eof) nil]
      (let [^LineNumberingPushbackReader r rdr
            col0 (.getColumnNumber r)
            _    (.captureString r)
            form (try (read-one cenv r eof)
                      (catch Throwable t (.getString r) (throw t)))
            cap  (.getString r)]
        [form (when (and cap
                         (not (identical? form eof))
                         (instance? clojure.lang.IObj form)
                         (:line (meta form)))
                (form-text cap col0 (meta form)))]))))

(def ^:private EOF (Object.))

(defn read-forms
  "Every top-level form of ClojureScript source `src` (a string or Reader), read in
  `cenv`.

  The current namespace is read before each form, so a caller processing forms as
  it goes can env/set-current-ns! on an (ns ...) and have the rest of the file
  resolve correctly. Reading a whole file up front leaves every form resolved
  against the namespace that was current when reading started - fine for a
  single-namespace file, wrong for one that switches."
  [cenv src]
  (let [rdr (push-back-reader src)]
    (loop [forms []]
      (let [form (read-one cenv rdr EOF)]
        (if (identical? form EOF)
          forms
          (recur (conj forms form)))))))
