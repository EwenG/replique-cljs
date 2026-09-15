;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Reading, and the one property a REPL needs that reading a file does not.

  read-forms may read a whole file before anything looks at it. read-one may not
  read past the form it returns, because the form it returns can change what the
  next one means - it can switch namespace. The tests below are mostly about that
  boundary: what has been consumed, and what the reader resolved against.

  Needs neither node nor the ClojureScript jar."}
  clojure.cljs.reader-test
  (:require [clojure.cljs.env :as env]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]])
  (:import [clojure.lang LineNumberingPushbackReader]
           [java.io File]
           [java.net URL URLClassLoader]))

(use-fixtures :each h/cursor)

(def ^:private eof (Object.))

(defn- read-one
  "read-one with this file's eof sentinel."
  [cenv rdr]
  (reader/read-one cenv rdr eof))

;; --- one form at a time -----------------------------------------------------

(deftest test-read-one-reads-exactly-one-form
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "(+ 1 2) (+ 3 4) :done")]
    (is (= '(+ 1 2) (read-one cenv rdr)))
    (is (= '(+ 3 4) (read-one cenv rdr)))
    (is (= :done (read-one cenv rdr)))
    (is (identical? eof (read-one cenv rdr)))
    ;; and it stays exhausted rather than throwing on a second look
    (is (identical? eof (read-one cenv rdr)))))

(deftest test-the-eof-sentinel-is-the-callers-own
  ;; Every value is a form some source can read, so no in-band sentinel would do:
  ;; nil, false and even a keyword named ::eof are things a REPL user can type.
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "nil false :clojure.cljs.reader/eof")]
    (is (nil? (read-one cenv rdr)))
    (is (false? (read-one cenv rdr)))
    (is (= :clojure.cljs.reader/eof (read-one cenv rdr)))
    (is (identical? eof (read-one cenv rdr)))))

(deftest test-a-form-can-change-what-the-next-form-means
  ;; The reason read-one exists. ::x resolves against the current namespace, so
  ;; reading the second one AFTER the cursor moves is the whole difference between
  ;; a REPL and a file reader.
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "::x ::x")]
    (is (= :app.core/x (read-one cenv rdr)))
    (env/set-current-ns! 'other.ns)
    (is (= :other.ns/x (read-one cenv rdr))))
  ;; read-forms is the contrast: it consumes the file before the caller sees any of
  ;; it, so moving the cursor afterwards changes nothing that was already read.
  (let [cenv (h/fresh-env)]
    (is (= [:app.core/x :app.core/x] (reader/read-forms cenv "::x ::x")))))

(deftest test-nothing-past-the-form-is-consumed
  ;; Not a style point: a REPL over a socket must leave the bytes it has not been
  ;; asked for, and a driver that switches namespace must be able to.
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "1 ::rest")]
    (is (= 1 (read-one cenv rdr)))
    (env/set-current-ns! 'later.ns)
    (is (= :later.ns/rest (read-one cenv rdr)))))


;; --- the text a form was written with ---------------------------------------

(defn- texts
  "[form text] for every form of `src`, read one at a time from one reader, the way
  a REPL reads - so the reader's line number climbs across the whole string and the
  texts have to be cut back out of it."
  [src]
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader src)]
    (loop [acc []]
      (let [[form text] (reader/read-one+text cenv rdr eof)]
        (if (identical? form eof) acc (recur (conj acc [form text])))))))

(deftest test-a-form-comes-back-with-the-characters-it-was-written-with
  (is (= [['(+ 1 1) "(+ 1 1)"]
          ['(defn f [x] (inc x)) "(defn f [x]\n  (inc x))"]]
         (texts "(+ 1 1)\n(defn f [x]\n  (inc x))\n"))))

(deftest test-what-came-before-the-form-is-not-part-of-it
  ;; whitespace, a comment and a #_ form are all in front of a form and look nothing
  ;; alike, which is why the cut is arithmetic rather than a scan: the capture ends
  ;; at the form's last character, so what is in front of it is what the form is not
  (testing "a comment on its own line"
    (is (= ["(+ 1 1)"] (map second (texts ";; hello\n(+ 1 1)")))))
  (testing "a comment after the form before it"
    (is (= ["(+ 1 1)" "(+ 2 2)"] (map second (texts "(+ 1 1) ; trailing\n(+ 2 2)")))))
  (testing "a discarded form, which is neither whitespace nor a comment"
    (is (= ["(+ 1 1)" "(+ 2 2)"] (map second (texts "(+ 1 1) #_skip (+ 2 2)")))))
  (testing "leading whitespace, and a form that starts away from column one"
    (is (= ["(a\n   b)"] (map second (texts "  (a\n   b)"))))))

(deftest test-two-forms-on-one-line-each-get-their-own
  ;; the case the arithmetic cannot do alone: with no newline in front of the second
  ;; form there is no line start to count from, and the reader's own column is where
  ;; the capture began - which it reliably is when no newline was pushed back
  (is (= ["(+ 1 1)" "(+ 2 2)"] (map second (texts "(+ 1 1) (+ 2 2)")))))

(deftest test-a-form-terminated-by-a-newline-does-not-shift-the-next-one
  ;; A BARE TOKEN IS TERMINATED BY READING THE NEWLINE AFTER IT, which is then
  ;; unread - and LineNumberingPushbackReader counts the line without being able to
  ;; give it back, so its line number is one ahead of the next capture's first
  ;; character. Nothing here reads that number: the cut counts newlines inside the
  ;; capture against the form's own :line and :end-line.
  ;; the nils are the bare tokens themselves, which have no position to map
  (is (= ["(a)" nil "(b)"] (map second (texts "(a)\n123\n(b)"))))
  (is (= [nil "(c)"] (map second (texts "\"a string\"\n(c)")))))

(deftest test-a-form-with-no-position-has-no-text
  ;; a bare number or keyword carries no metadata, and emits nothing a source map
  ;; could point at - so there is nothing to embed and nothing is claimed
  (is (= [[42 nil] [:kw nil] ['(+ 1 1) "(+ 1 1)"]]
         (texts "42 :kw (+ 1 1)"))))

(deftest test-a-reader-that-cannot-capture-still-reads
  ;; read-one+text is defined over any reader read-one is, and only this one can
  ;; hand the characters back
  (let [rdr (java.io.PushbackReader. (java.io.StringReader. "(+ 1 1)"))]
    (is (= ['(+ 1 1) "(+ 1 1)"] (reader/read-one+text (h/fresh-env) rdr eof)))))

(deftest test-the-text-starts-where-the-form-says-it-does
  ;; the property the map depends on: text line 1 is the form's :line and text
  ;; column 1 of that line is its :column, whatever the reader's own count says
  (doseq [src ["(+ 1 1)\n(a\n  b)"
               ";; c\n\n\n(a\n  b)"
               "1\n2\n3\n(a\n  b)"
               "(z) (a\n  b)"]]
    (let [[form text] (last (texts src))
          {:keys [line column end-line]} (meta form)]
      (is (= "(a" (first (str/split-lines text))) src)
      (is (= (- (long end-line) (long line))
             (dec (count (str/split-lines text))))
          src)
      (is (= 1 (count (filter #(= \newline %) text))) src)
      (is (some? column) src))))

;; --- the reader is still the ClojureScript one ------------------------------

(deftest test-the-switches-apply-to-read-one-too
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "#?(:clj :jvm :cljs :js) #js [1 2]")]
    ;; the platform feature is :cljs, so a reader conditional takes that branch
    (is (= :js (read-one cenv rdr)))
    ;; and #js is wrapped, not built
    (is (= (reader/->JSValue [1 2]) (read-one cenv rdr)))))

(deftest test-read-eval-is-off
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "#=(+ 1 1)")]
    (is (thrown? Exception (read-one cenv rdr)))))

;; --- readers the caller keeps -----------------------------------------------

(deftest test-a-reader-survives-being-passed-again
  ;; push-back-reader has to be idempotent: wrapping a reader a second time would
  ;; leave the characters the first buffer had already taken inside it, and the
  ;; REPL would silently skip whatever it had read ahead.
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "1 2 3")]
    (is (identical? rdr (reader/push-back-reader rdr)))
    (is (= 1 (read-one cenv rdr)))
    ;; the rest of the same stream, read by the file entry point this time
    (is (= [2 3] (reader/read-forms cenv rdr)))))

(deftest test-read-one-line-numbers-a-reader-it-makes
  ;; Positions are recorded while reading, so the reader underneath has to be the
  ;; line-numbering one whichever way it was built.
  (is (instance? LineNumberingPushbackReader (reader/push-back-reader "x")))
  (is (instance? LineNumberingPushbackReader
                 (reader/push-back-reader (java.io.StringReader. "x"))))
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "x\n\ny")]
    (read-one cenv rdr)
    (is (= '{:line 3 :column 1}
           (select-keys (meta (read-one cenv rdr)) [:line :column])))))

;; --- failure ----------------------------------------------------------------

(deftest test-a-malformed-form-throws
  ;; And the reader is left wherever it gave up. Recovering is the REPL's policy,
  ;; not the reader's, so all that is promised here is the throw.
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "(1 2")]
    (is (thrown? Exception (read-one cenv rdr))))
  (let [cenv (h/fresh-env)
        rdr  (reader/push-back-reader "(1 2))")]
    (is (= '(1 2) (read-one cenv rdr)))
    (is (thrown? Exception (read-one cenv rdr)))))

;; --- what the reader resolves against ---------------------------------------

(deftest test-an-auto-resolved-keyword-sees-both-kinds-of-alias
  ;; ::other/foo is a :require alias and ::macros/foo is a :require-macros one.
  ;; The second lives on the namespace's MACRO VIEW rather than in the runtime
  ;; world, so a resolver that consulted only the runtime world left ::macros/foo
  ;; as `Invalid token` - and cljs.keyword-test writes all three.
  (let [cenv (h/fresh-env 'cljs.user)
        kw   #(read-one cenv (reader/push-back-reader %))]
    (h/analyze cenv '(ns app.core
                       (:require [my-lib.core :as other])
                       (:require-macros [clojure.cljs.env :as macros])))
    (is (= :app.core/bar (kw "::bar")))
    (is (= :my-lib.core/foo (kw "::other/foo")))
    (is (= :clojure.cljs.env/foo (kw "::macros/foo")))
    ;; an alias that is neither is still an error, which is what makes this a
    ;; resolution rather than a spelling
    (is (thrown? Exception (kw "::nope/foo")))))

(deftest test-a-runtime-alias-wins-a-collision
  ;; cljs.analyzer hands its reader (merge (:requires ns) (:require-macros ns)),
  ;; so there a macro alias would win. This asks the runtime world first, so the
  ;; alias resolves the way every other name in this compiler resolves. Nothing in
  ;; either suite has such a collision - requiring two namespaces under one alias
  ;; is a mistake in either reading - so the tie-break is ours to pick.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:require [my-lib.core :as a])
                       (:require-macros [clojure.cljs.env :as a])))
    (is (= :my-lib.core/foo (read-one cenv (reader/push-back-reader "::a/foo"))))))

(deftest test-a-syntax-quote-resolves-a-cljs-core-name
  ;; `keyword? is cljs.core/keyword?, and it was app.core/keyword? - a name that
  ;; does not exist, in every macro and every quoted form in the tree.
  ;;
  ;; getMapping was the bug. Mappings cover what a namespace interns and what it
  ;; refers, and cljs.core is NEITHER: every namespace gets it through the implicit
  ;; require, whose refer half is a rule inside env/resolve-var rather than a
  ;; mapping on the Namespace (doc/cljs-compiler.md 5.12). So the reader asked a
  ;; question the analyzer answers differently, and syntax-quote fell back to the
  ;; current namespace.
  ;;
  ;; cljs.spec.alpha is what showed it: a spec records its predicate's resolved
  ;; name, so (s/explain-data keyword? nil) reported :pred cljs.spec-test/keyword?.
  (let [cenv (h/core-env 'app.sq)]
    (is (= ''cljs.core/keyword? (reader/read-one cenv (reader/push-back-reader "`keyword?") eof)))
    (is (= ''cljs.core/map (reader/read-one cenv (reader/push-back-reader "`map") eof))))

  (testing "a var of this namespace still wins, and an unknown name is still qualified here"
    (let [cenv (h/core-env 'app.sq2)]
      (h/analyze cenv '(def keyword? 1))
      (is (= ''app.sq2/keyword? (reader/read-one cenv (reader/push-back-reader "`keyword?") eof)))
      (is (= ''app.sq2/nope (reader/read-one cenv (reader/push-back-reader "`nope") eof))))))

(deftest test-a-syntax-quote-resolves-a-cljs-core-macro-too
  ;; §5.34. The other half of the rule above, and the half Clojure never has to
  ;; state: a macro IS a var there, so `fn resolves like any other name. Here it is
  ;; not - cljs.core/fn is a JVM macro with no ClojureScript var behind it - so
  ;; resolve-var answered nil and syntax-quote fell back to the current namespace.
  ;;
  ;; cljs.spec.alpha is what showed this one too. alpha.cljs builds a predicate
  ;; form with `(fn [~'%] (c/or (nil? ~'%) (sequential? ~'%))), and every name in
  ;; it resolved to cljs.core EXCEPT fn - so (s/explain-data (s/? keyword?) :k)
  ;; reported a :pred headed by cljs.spec.alpha/fn, a name that expands to nothing.
  (let [cenv (h/core-env 'app.sqm)
        rd   #(reader/read-one cenv (reader/push-back-reader %) eof)]
    (is (= ''cljs.core/fn (rd "`fn")))
    (is (= ''cljs.core/when (rd "`when")))
    (is (= ''cljs.core/defn (rd "`defn")))
    ;; a var still wins, which is what keeps this after resolve-var and not before
    (is (= ''cljs.core/map (rd "`map"))))

  (testing "a name this namespace excluded is not a core macro here"
    (let [cenv (h/core-env 'app.sqm2)]
      (h/analyze cenv '(ns app.sqm2 (:refer-clojure :exclude [when])))
      (is (= ''app.sqm2/when
             (reader/read-one cenv (reader/push-back-reader "`when") eof))))))

(deftest test-a-syntax-quoted-dotted-symbol-resolves-to-itself
  ;; §5.29. `clojure.core is 'clojure.core, not app.core/clojure.core. A dot means
  ;; the name is already qualified or is interop, and either way there is nothing
  ;; for a namespace to be prepended to.
  ;;
  ;; Clojure's own Compiler.resolveSymbol opens with the check ("already qualified
  ;; or classname?") and cljs.tools.reader's resolve-symbol opens with it too ("if
  ;; there is a period, it is interop"). Neither was reached here: LispReader's
  ;; syntax-quote takes the Resolver path whenever a resolver is installed, so the
  ;; rule had to be stated in ours. cljs/core_test.cljs asks for it as
  ;; test-cljs-2109.
  (let [cenv (h/core-env 'app.dq)]
    (doseq [[src expected] [["`clojure.core"           ''clojure.core]
                            ["`goog.string"            ''goog.string]
                            ["`PersistentVector.EMPTY" ''PersistentVector.EMPTY]]]
      (is (= expected (reader/read-one cenv (reader/push-back-reader src) eof)) src))
    ;; and a name with no dot is unaffected
    (is (= ''cljs.core/map (reader/read-one cenv (reader/push-back-reader "`map") eof)))))

;; --- user data readers --------------------------------------------------------

(defn- with-data-readers-file*
  "Run `f` with `content` on the classpath as data_readers.cljc.

  A temporary directory in front of the context classloader, which is what
  user-data-readers* scans. The real thing is a file in somebody's jar; this is the
  same file in a directory nobody else can see, so the test does not depend on what
  the suite's own classpath happens to hold - and so that two tests can register
  two different tables."
  [content f]
  (let [dir (h/temp-dir)]
    (spit (io/file dir "data_readers.cljc") content)
    (let [thread (Thread/currentThread)
          before (.getContextClassLoader thread)]
      (try
        (.setContextClassLoader
         thread (URLClassLoader. (into-array URL [(.toURL (.toURI ^File dir))]) before))
        (f)
        (finally
          (.setContextClassLoader thread before)
          (h/delete-tree! dir))))))

(defmacro ^:private with-data-readers-file [content & body]
  `(with-data-readers-file* ~content (fn [] ~@body)))

(deftest test-a-data-readers-file-registers-tags
  ;; §5.30. The tags of a PROGRAM, as against the tags of the language: whatever
  ;; every data_readers.cljc on the classpath names, with the JVM function that
  ;; reads each one and the symbol that named it.
  (with-data-readers-file "{my/up clojure.string/upper-case\n my/inc clojure.core/inc}"
    (let [tags (#'reader/user-data-readers*)]
      (is (= '#{my/up my/inc} (set (keys tags))))
      (is (= "AB" ((get tags 'my/up) "ab")))
      ;; :sym is how the runtime half names the same function again
      (is (= 'clojure.string/upper-case (:sym (meta (get tags 'my/up))))))))

(deftest test-a-data-readers-file-is-read-as-cljs
  ;; the reason this cannot borrow clojure.core/*data-readers*, which RT fills from
  ;; the same files at startup: RT takes the :clj branch of every reader
  ;; conditional in them. ClojureScript's own fixture registers test/custom-form
  ;; that way, and the :clj reader is not the one a ClojureScript program wants.
  (with-data-readers-file
    "{my/x #?(:clj clojure.core/identity :cljs clojure.string/upper-case)}"
    (is (= 'clojure.string/upper-case
           (:sym (meta (get (#'reader/user-data-readers*) 'my/x)))))))

(deftest test-a-data-readers-file-is-checked
  (doseq [[content msg] [["[1 2]"                    "Not a valid data-reader map"]
                         ["{\"my/up\" clojure.core/identity}" "Invalid form in data-reader file"]]]
    (with-data-readers-file content
      (is (= msg (try (#'reader/user-data-readers*) nil
                      (catch Exception e (.getMessage e))))
          content))))

(deftest test-a-registered-tag-is-read-while-compiling
  ;; the compile-time half, end to end: the tag is read by the compiler's reader,
  ;; and what it hands back is analysed and emitted like any other form. Nothing in
  ;; the analyzer or the emitter knows a tag was involved.
  (with-data-readers-file "{my/up clojure.string/upper-case}"
    (with-redefs [reader/user-data-readers #'reader/user-data-readers*]
      (is (= "AB" (h/output-with-core "#my/up \"ab\"")))
      ;; and the language's own tags are still there beside it
      (is (= "#queue [1 2]" (h/output-with-core "(pr-str #queue [1 2])"))))))

(deftest test-the-runtime-half-emits-a-call-to-the-reader
  ;; cljs.reader/add-data-readers. THE CALL IS EMITTED, NOT THE FUNCTION: the
  ;; symbol data_readers.cljc named is resolved twice against two different worlds -
  ;; once on the JVM so a tag can be read while compiling, and once in this
  ;; expansion so the same name means the ClojureScript var of that name at runtime.
  (require 'cljs.reader)
  (with-redefs [reader/user-data-readers
                (constantly {'my/up (with-meta identity
                                      {:sym 'clojure.string/upper-case})})]
    (let [ex (macroexpand-1 '(cljs.reader/add-data-readers {'js read-js}))
          [_ default readers] ex]
      (is (= `merge (first ex)))
      (is (= '{'js read-js} default))
      (is (= '['my/up] (vec (keys readers))))
      (is (= 'clojure.string/upper-case (ffirst (drop 2 (first (vals readers)))))))))
