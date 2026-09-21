;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The analyzer on its own: what it refuses, and what it puts in the
  ClojureScript world.

  Needs neither node nor the ClojureScript jar, so these always run.

  The refusals matter as much as the acceptances. This analyzer is deliberately
  partial, and an unimplemented form has to fail loudly, naming what it saw and
  what is handled, rather than guessing and emitting something plausible."}
  clojure.cljs.analyzer-test
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.spec.alpha :as spec]
            [clojure.cljs.macroexpand :as macroexpand]
            [clojure.string :as str]
            [clojure.cljs.names :as names]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.test-harness :as h]
            [clojure.test :refer [are deftest is testing use-fixtures]])
  (:import [clojure.lang Namespace NamespaceWorld Var]))

(use-fixtures :each h/cursor)

(defn- refuses
  "The message from analysing `form`, or nil if it was accepted."
  [form]
  (h/message #(h/analyze form)))

(deftest test-arity-and-shape-errors
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(if)                     #"Too few arguments to if"
    '(if 1 2 3 4)             #"Too many arguments to if"
    '(let* [x])               #"even number of forms"
    '(let* x 1)               #"even number of forms"
    '(fn*)                    #"at least one method"
    '(fn* ([x] x) ([y] y))    #"cannot have the same arity"
    '(fn* ([& a] a) ([x & b] b)) #"only one variadic method"
    '(fn* ([x & y z] x))      #"& must be followed by exactly one parameter"
    '(def "x" 1)              #"must be a simple symbol"
    '(def x 1 2)              #"Too many arguments to def"
    '(js* 42)                 #"requires a string template"
    '(throw)                  #"exactly one argument"
    '(throw 1 2)              #"exactly one argument"
    '(quote a b)              #"Wrong number of args to quote"))

(deftest test-recur-errors
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(recur 1)                          #"outside of a loop\* or fn\* method"
    '(loop* [i 0] (recur 1 2))          #"recur expects 1 argument"
    ;; a consumed value is not a tail position
    '(loop* [i 0] (js* "~{}" (recur 1))) #"Can only recur from tail position"))

(deftest test-interop-errors
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(. "a" -length 1)        #"Cannot provide arguments"
    '(. "a" (split ",") 2)    #"Cannot provide arguments"
    '(. "a" 42)               #"Bad dot form"
    '(.)                      #"Bad dot form: no target"
    '(new)                    #"new requires a constructor"))

(deftest test-set!-errors
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(set! 1 2)               #"must be a var or a property access"
    '(set! x)                 #"set! expects"
    '(fn* ([x] (set! x 1)))   #"a local is immutable"))

(deftest test-letfn-and-case-errors
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(letfn* [f])                          #"even number of forms"
    '(letfn* f (fn* ([] 1)))               #"even number of forms"
    '(case* 1 [[1]] ["a"] "b")             #"must switch on a symbol"
    '(let* [x 1] (case* x [1] ["a"] "b"))  #"grouped in vectors"
    '(let* [x 1] (case* x [[]] ["a"] "b")) #"at least one test"
    '(let* [x 1] (case* x [[1] [2]] ["a"] "b")) #"one branch per group"
    ;; a keyword is a constant, but not one JavaScript's switch compares usefully
    '(let* [x 1] (case* x [[:k]] ["a"] "b")) #"numbers, strings or characters"))

(deftest test-letfn-is-self-recursive
  ;; where cljs.analyzer resolves the inner f to a var - see
  ;; clojure.cljs.oracle-test/test-known-divergences
  (let [node (h/analyze '(letfn* [f (fn* ([] (f)))] (f)))]
    (is (= :local (-> node :bindings first :init :methods first
                      :body :ret :fn :op)))))

(deftest test-names-that-cannot-become-javascript
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    ;; a.b is a simple symbol, and munge leaves the dot alone
    '(let* [a.b 1] a.b)          #"local name cannot contain a dot"
    '(fn* ([a.b] a.b))           #"local name cannot contain a dot"
    ;; a Ratio has no reading in JavaScript at all; ClojureScript refuses it in
    ;; these words, and 10N and 1.5M it simply makes doubles (see emitter-test)
    (/ 1 2)                      #"not a valid ClojureScript constant"
    (/ 3 4)                      #"not a valid ClojureScript constant"))

(deftest test-numbers-javascript-can-hold-are-accepted
  (are [form] (nil? (refuses form))
    10N 1.5M 42 -3 1.5 ##Inf ##-Inf ##NaN))

(deftest test-js-placeholder-count
  ;; the dangerous direction is too many: (js* "~{}" 1 2) used to emit `12`
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(js* "~{}" 1 2)      #"1 placeholder\(s\) but was given 2"
    '(js* "~{} + ~{}" 1)  #"2 placeholder\(s\) but was given 1"
    '(js* "no holes" 1)   #"0 placeholder\(s\) but was given 1")
  (is (nil? (refuses '(js* "~{} + ~{}" 1 2))))
  (is (nil? (refuses '(js* "42")))))

(deftest test-fn-arity-rules
  ;; a fixed arity may equal the variadic method's fixed arity - that is conj
  (is (nil? (refuses '(fn* ([x] x) ([x & ys] ys)))))
  (is (nil? (refuses '(fn* ([] 0) ([x] x) ([x y & r] r)))))
  ;; but not exceed it, and two fixed methods may not share one
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(fn* ([x y] x) ([x & ys] ys)) #"more parameters than the variadic"
    '(fn* ([x] 1) ([y] 2))         #"cannot have the same arity"
    '(fn* ([& a] a) ([x & b] b))   #"only one variadic method"
    ;; a method that is not a list at all reached the destructuring first and
    ;; failed with "Don't know how to create ISeq from java.lang.Long" - a Clojure
    ;; error about our implementation rather than a sentence about the form
    '(fn* 1)                       #"fn\* method must be a list"
    '(fn* ([x] 1) 2)               #"fn\* method must be a list"
    '(fn* "s")                     #"fn\* method must be a list"))

(deftest test-case-tests-must-be-distinct
  ;; JavaScript takes the first matching label, so a repeat silently makes a
  ;; later branch unreachable
  (are [form] (some? (re-find #"tests must be distinct" (or (refuses form) "")))
    '(let* [x 1] (case* x [[1] [1]] ["a" "b"] "c"))      ; across groups
    '(let* [x 1] (case* x [[1 1]] ["a"] "c")))           ; within one group
  ;; distinct in CLOJURESCRIPT, not in Clojure: 1 and 1.0 are two Clojure
  ;; constants and one JavaScript number, so `case 1:` and `case 1.0:` are the
  ;; same label and the second branch is dead. cljs.analyzer has no check here at
  ;; all - it accepts even [[1] [1]] - so this one is ours to get right.
  (are [form] (some? (re-find #"tests must be distinct" (or (refuses form) "")))
    '(let* [x 1] (case* x [[1] [1.0]] ["a" "b"] "c"))
    '(let* [x 1] (case* x [[1] [1N]] ["a" "b"] "c")))
  ;; a CHARACTER is a one-character string in ClojureScript (§5.7), so \a and "a"
  ;; are the same label for the same reason 1 and 1.0 are
  (are [form] (some? (re-find #"tests must be distinct" (or (refuses form) "")))
    '(let* [x 1] (case* x [[\a] ["a"]] ["p" "q"] "r"))
    '(let* [x 1] (case* x [[\a \a]] ["p"] "r")))
  ;; several constants sharing one branch is the normal case and stays legal
  (is (nil? (refuses '(let* [x 1] (case* x [[1] [2 3]] ["a" "b"] "c")))))
  ;; and a number is not a string, however it prints
  (is (nil? (refuses '(let* [x 1] (case* x [[1] ["1"]] ["a" "b"] "c"))))))

(deftest test-a-case-test-may-be-a-character
  ;; cljs.analyzer's list is numbers, strings and characters (analyzer.cljc:1884)
  ;; and this was the odd one out - character literals analyse and emit fine, only
  ;; case* refused them. cljs.pprint, cljs.reader and cljs.tools.reader all switch
  ;; on one.
  (let [js (h/js "(let* [x 1] (case* x [[\\a] [\\b 1]] [\"p\" \"q\"] \"r\"))")]
    ;; a one-character string label, which is what a ClojureScript character IS -
    ;; no conversion of its own and nothing to distinguish it from "a"
    (is (str/includes? js "case \"a\":") js)
    (is (str/includes? js "case \"b\":") js)
    ;; and it groups with constants of other kinds, as any label does
    (is (str/includes? js "case (1):") js))
  ;; the message names all three kinds, so a keyword says what was expected
  (is (re-find #"numbers, strings or characters"
               (refuses '(let* [x 1] (case* x [[:kw]] ["p"] "r"))))))

(deftest test-name-scope-spans-a-compile-unit
  ;; analyze-top used to reset the counter per form, so two forms binding the
  ;; same name emitted the same `let` into one JavaScript scope
  (let [cenv (h/fresh-env 'app.core)
        aenv (env/analysis-env cenv)]
    (names/with-name-scope
      (let [a (ana/analyze-top cenv aenv '(let* [x 1] x))
            b (ana/analyze-top cenv aenv '(let* [x 2] x))]
        (is (not= (-> a :bindings first :js-name)
                  (-> b :bindings first :js-name)))))))

(deftest test-malformed-forms-are-named-not-crashed
  ;; Each of these used to reach the emitter and produce either a JavaScript
  ;; syntax error at load time or an exception from deep inside emission.
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    ;; the rest position holding nil is falsey, so it slipped the guard and left
    ;; a method :variadic? with no rest binding
    '(fn* [& nil] 1)       #"& must be followed by a symbol"
    '(fn* [& 5] 1)         #"& must be followed by a symbol"
    ;; nothing after the minus, and no method in the list: both emitted `o.`
    '(. "s" -)             #"a field name is missing"
    '(. "s" ())            #"a method name is missing"))

(deftest test-var-names-are-names-we-can-own
  ;; a var is emitted as a property named after it, so (def a.b 1) would write
  ;; onto whatever the var a holds - and did, silently, when a was a JS object.
  ;; cljs.analyzer has no guard here either; it emits a bare global instead.
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(def a.b 1)      #"Cannot use a.b as a var name"
    '(def a.b.c 1)    #"Cannot use a.b.c as a var name")
  (are [form] (nil? (refuses form))
    '(def a 1)
    '(def foo-bar 1)
    '(def foo? 1)
    ;; a reserved word is a fine property name
    '(def if 1)))

(deftest test-js-globals-must-be-names-in-javascript
  ;; js/foo-bar emitted the text foo-bar, which JavaScript reads as a subtraction
  ;; what survives host-name and is still not a name: a dot out of place, a
  ;; space, a leading digit. (A hyphen or a ? does not - both munge to something
  ;; legal, which is the point.)
  (are [sym] (some? (re-find #"not a name there" (or (refuses sym) "")))
    (symbol "js" "foo.")
    (symbol "js" "a..b")
    (symbol "js" "a b")
    (symbol "js" "1a"))
  ;; a hyphen is fine - it spells the host's way, to foo_bar, as in ClojureScript
  (are [sym] (nil? (refuses sym))
    'js/foo-bar
    'js/foo?
    'js/Math.PI
    'js/-Infinity))

(deftest test-unimplemented-forms-say-so
  ;; the message names what was seen and what is handled - the list is generated
  ;; from the parser table, so it cannot drift
  ;; a Ratio has no reading in JavaScript at all, which is also cljs.compiler's
  ;; answer - and it is the last literal the reader can build that we refuse
  (let [msg (refuses 1/2)]
    (is (re-find #"Not implemented yet" msg))
    (is (re-find #"the ratio 1/2" msg))
    (is (re-find #"This analyzer handles" msg)))
  ;; There used to be a second example here, a literal the READER builds from a
  ;; tag: #inst was a java.util.Date and we had no spelling for it. All three tags
  ;; are constants now (§5.22), and the reader can no longer build anything this
  ;; branch refuses - so what is left of that case is this note. The branch stays,
  ;; because a data reader a user registers can hand back anything at all.
  ;; an undefined name is not an unimplemented form, and does not get the list:
  ;; one message says wait for a milestone, the other says fix the code
  (let [msg (refuses 'no-such-thing)]
    (is (re-find #"neither a local nor a var" msg))
    (is (re-find #"app.core" msg))
    (is (not (re-find #"This analyzer handles" msg))))
  ;; a goog name OUTSIDE THE SUBSET refuses, and says which question it is: the
  ;; whole goog. prefix is reserved, so the answer is that we do not ship the name
  ;; rather than that we have never heard of it. See
  ;; test-an-unknown-prefix-is-a-javascript-global for what does fall through.
  (let [msg (refuses 'goog.nonesuch/thing)]
    (is (re-find #"No such namespace: goog.nonesuch" msg))
    (is (re-find #"subset of the Closure Library" msg))
    (is (not (re-find #"add it to the ns form" msg))
        "there is nothing to add - the file is not in the tree")))

(deftest test-a-def-name-may-be-qualified-with-this-namespace
  ;; doc/cljs-compiler.md §5.23. Clojure's rule and cljs.analyzer's: parse 'def
  ;; refuses only (and sym-ns (not= sym-ns ns-name)). A macro reaches it without
  ;; meaning to - a syntax-quoted (def ~name ...) resolves `name` against the
  ;; namespace expanding it, which is how test.check's defspec arrives here as
  ;; (def cljs.core-test/foo-1274 ...).
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core))
    (let [node (h/analyze cenv '(def app.core/x 1))]
      (is (= :def (:op node)))
      (is (= 'app.core/x (:name node))))
    ;; and it is the same var the simple name reaches
    (is (= 'app.core/x (:name (h/analyze cenv 'x)))))

  (testing "metadata on the qualified symbol survives the unqualifying"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core))
      (is (:dynamic (meta (env/resolve-var cenv (:name (h/analyze cenv '(def ^:dynamic app.core/d 1)))))))))

  (testing "another namespace is still refused, and says which is allowed"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core))
      (let [msg (h/message #(h/analyze cenv '(def other.ns/x 1)))]
        (is (re-find #"must be a simple symbol or one qualified with app.core" msg)))))

  (testing "and a dotted name is still not a var name"
    ;; a var is emitted as a property named after it, so (def a.b 1) would write
    ;; onto whatever the var a holds - names/check-own-name!, unchanged
    (is (re-find #"not a JavaScript name"
                 (h/message #(h/analyze (h/fresh-env 'app.core) '(def a.b 1)))))))

(deftest test-a-dotted-name-is-a-var-and-then-its-properties
  ;; doc/cljs-compiler.md §5.22. cljs.core.PersistentQueue.EMPTY is the var
  ;; PersistentQueue and then its EMPTY property. Splitting at the LAST dot made
  ;; it a var called EMPTY in a namespace called cljs.core.PersistentQueue -
  ;; which is nothing, so it fell through to a JavaScript global and the emitted
  ;; name was a ReferenceError at load.
  ;; the SLASH spelling, which is what cljs/reader.cljs:101 writes
  (let [cenv (h/fresh-env 'app.core)]
    (h/analyze cenv '(def PersistentQueue 1))
    (let [node (h/analyze cenv 'app.core/PersistentQueue.EMPTY)]
      (is (= :host-field (:op node)))
      (is (= 'EMPTY (:field node)))
      (is (= 'app.core/PersistentQueue (-> node :target :name)))))

  ;; and the DOTTED one, which is what their tests write four times. Unchecked,
  ;; like every dotted name (analyze-dotted-symbol), so the var need not exist yet
  (let [node (h/analyze (h/fresh-env 'app.core) 'cljs.core.PersistentQueue.EMPTY)]
    (is (= :host-field (:op node)))
    (is (= 'EMPTY (:field node)))
    (is (= 'cljs.core/PersistentQueue (-> node :target :name))))

  (testing "one dot and no properties still resolves the whole name"
    ;; cljs.core.Var is cljs.core/Var, and UNCHECKED - core.cljs writes
    ;; (instance? cljs.core.Var v) at 1162 and defines Var at 1186
    (let [node (h/analyze (h/fresh-env 'app.core) 'cljs.core.Var)]
      (is (= :var (:op node)))
      (is (= 'cljs.core/Var (:name node)))))

  (testing "a prefix nothing knows is still a JavaScript global"
    ;; the fallback when no prefix resolves is the last dot, which is what §5.8
    ;; says Foo.Bar.baz is
    (let [node (h/analyze 'Foo.Bar.baz)]
      (is (= :js-var (:op node)))
      (is (= 'js/Foo.Bar.baz (:name node))))))

(deftest test-the-three-tagged-literals
  ;; #inst and #uuid are CLOJURE'S: the reader builds them from
  ;; default-data-readers with no help from us, so what was missing was only
  ;; somewhere for the value to go.
  ;; READ THROUGH OUR READER, which is the point: this file is a .clj, so an
  ;; #inst written here is Clojure's own tag and hands back a java.util.Date. Ours
  ;; hands back a java.time.Instant, because a Date is Julian before the 1582
  ;; cutover and a JavaScript Date is proleptic Gregorian - see
  ;; clojure.cljs.reader/cljs-data-readers, and §5.23 for the nine days it cost.
  (let [read1 (fn [src]
                (let [cenv (h/fresh-env 'app.core)]
                  (reader/read-one cenv (reader/push-back-reader
                                         (java.io.StringReader. src))
                                   ::eof)))]
    (let [v (read1 "#inst \"2020-01-02T03:04:05.678-00:00\"")]
      (is (instance? java.time.Instant v))
      (is (= 1577934245678 (.toEpochMilli ^java.time.Instant v))))
    ;; before the cutover, where the two calendars part company
    (is (= -14830992000000
           (.toEpochMilli ^java.time.Instant
                          (read1 "#inst \"1500-01-10T00:00:00.000-00:00\""))))
    (is (instance? java.util.UUID
                   (read1 "#uuid \"550e8400-e29b-41d4-a716-446655440000\""))))

  ;; and both are constants the analyzer takes
  (let [d (h/analyze (java.time.Instant/ofEpochMilli 1577934245678))]
    (is (= :const (:op d)))
    (is (instance? java.time.Instant (:val d))))
  (let [u (h/analyze #uuid "550e8400-e29b-41d4-a716-446655440000")]
    (is (= :const (:op u)))
    (is (instance? java.util.UUID (:val u))))

  (testing "#queue is ClojureScript's, and is a FORM rather than a value"
    ;; cljs.tagged-literals/read-queue verbatim - which is why nothing in the
    ;; emitter knows about queues: what the reader hands back is an ordinary call
    (is (= '(cljs.core/into cljs.core.PersistentQueue.EMPTY [1 2])
           (reader/read-queue '[1 2])))
    (is (re-find #"expects a vector"
                 (h/message #(reader/read-queue '(1 2)))))))

(deftest test-a-fully-qualified-closure-name-is-its-own-require
  ;; doc/cljs-compiler.md 5.18. What a require buys is a SHORT name; a name written
  ;; out in full carries its own referent, and the require is RECORDED as the name
  ;; is read so that the module still gets its import.
  (testing "a var in a goog namespace"
    (let [cenv (h/fresh-env 'app.core)
          node (h/analyze cenv 'goog.object/get)]
      (is (= :goog-var (:op node)))
      (is (= 'goog.object/get (:name node)))
      (is (contains? (env/requires cenv 'app.core) 'goog.object)
          "recorded, or the module emits no import for it")))

  (testing "a provide is one name, however it is spelled"
    ;; goog.string/StringBuffer is the CLASS stringbuffer.js provides, not a var in
    ;; the 11-function reduction that string.js provides - reading it as a var
    ;; would put goog.string.StringBuffer in the output, and that is undefined.
    (doseq [sym '[goog.string/StringBuffer goog.string.StringBuffer]]
      (let [cenv (h/fresh-env 'app.core)
            node (h/analyze cenv sym)]
        (is (= :goog-ns (:op node)) (str sym))
        (is (= 'goog.string.StringBuffer (:name node)) (str sym))
        (is (= sym (:form node))
            "the source form is what was written, not what it turned out to mean")
        (is (contains? (env/requires cenv 'app.core) 'goog.string.StringBuffer)
            (str sym)))))

  (testing "the case that settles it - a macro's expansion"
    ;; cljs.core/with-out-str expands to (goog.string/StringBuffer.) and lands in
    ;; whichever namespace called it. That namespace cannot know to require
    ;; goog.string, and asking it to would publish an implementation detail of a
    ;; cljs.core macro as part of its contract.
    ;; the form itself, rather than the macro call: the rest of that expansion
    ;; binds cljs.core/*print-fn*, so calling it needs a compiled cljs.core.
    (let [cenv (h/fresh-env 'app.core)
          node (h/analyze cenv '(goog.string/StringBuffer.))]
      (is (= :new (:op node)))
      (is (= 'goog.string.StringBuffer (-> node :class :name)))
      (is (contains? (env/requires cenv 'app.core) 'goog.string.StringBuffer))))

  (testing "an alias reaches the provide too"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core (:require [goog.string :as gstring])))
      (let [node (h/analyze cenv 'gstring/StringBuffer)]
        (is (= :goog-ns (:op node)))
        (is (= 'goog.string.StringBuffer (:name node))))))

  (testing "strictness is untouched where it says something"
    ;; an alias with no require has no referent at all
    (is (re-find #"neither a local nor a var"
                 (h/message #(h/analyze 'gstring))))
    ;; a name we do not ship is still refused, by goog/known?
    (is (re-find #"subset of the Closure Library"
                 (h/message #(h/analyze 'goog.nonesuch/thing))))
    ;; and a var of a reduction that the reduction does not have. NOT `format`,
    ;; which was this example until §5.29 and is now a provide of its own - see
    ;; goog_test's test-format-is-a-provide-and-so-escapes-the-reduction.
    (is (re-find #"not in the Closure subset"
                 (h/message #(h/analyze 'goog.string/repeat))))))

(deftest test-an-unknown-prefix-is-a-javascript-global
  ;; Math/floor is Math.floor. cljs.analyzer says the same, and NOT through
  ;; externs - the branch never consults them; it spells the symbol out and lets
  ;; the host answer for it (doc/cljs-compiler.md §5.8).
  (let [node (h/analyze 'Math/floor)]
    (is (= :js-var (:op node)))
    (is (= 'js/Math.floor (:name node)))
    (is (= 'js (:ns node)))
    (is (= 'Math/floor (:form node))
        "the source form is what was written, not what it turned out to mean"))
  ;; the node is a :js-var where cljs.analyzer builds a :var whose :ns is Math.
  ;; Both emit Math.floor; theirs can say :var because a ClojureScript var IS a
  ;; global path, and ours cannot because it is a property of a namespace object.
  (is (= :js-var (:op (h/analyze 'String/fromCharCode))))

  (testing "two prefixes are unsurprising and the rest get a warning"
    (are [sym] (= "" (h/warnings #(h/analyze sym)))
      'Math/floor
      'Math/PI
      'String/fromCharCode)
    (let [w (h/warnings #(h/analyze 'Date/now))]
      (is (re-find #"undeclared-ns" w))
      (is (re-find #"Date" w)))
    ;; and the warning is ALL that happens - the form still compiles, which is
    ;; the whole of what changed here
    (let [node (atom nil)
          w    (h/warnings #(reset! node (h/analyze 'Widget/render)))]
      (is (re-find #"undeclared-ns" w))
      (is (= 'js/Widget.render (:name @node)))))

  (testing "a name that is not a name in JavaScript is still refused"
    (let [msg (atom nil)]
      ;; the warning comes first and is not the point, so it is swallowed here
      (h/warnings #(reset! msg (h/message (fn [] (h/analyze (symbol "Foo" "a b"))))))
      (is (re-find #"not a name there" @msg)))))

(deftest test-locals-get-unique-names
  ;; the emitter flattens nested scopes into one JavaScript scope, so two `x`es
  ;; would collide; the analyzer renames rather than the emitter
  (let [node (h/analyze '(let* [x 1] (let* [x 2] x)))
        outer (-> node :bindings first :js-name)
        inner (-> node :body :ret :bindings first :js-name)]
    (is (not= outer inner))
    (is (= 'x (-> node :bindings first :name)))))

(deftest test-js-symbols
  (is (= :js-var (:op (h/analyze 'js/console))))
  (is (= 'js/console.log (:name (h/analyze 'js/console.log)))
      "dots stay in the name: this is one js-var, not a field access")
  ;; a local of the same name wins, as in ClojureScript
  (is (= :local (-> (h/analyze '(fn* ([x] js/x)))
                    :methods first :body :ret :op))))

(deftest test-def-interns-in-the-cljs-world
  (let [cenv (h/fresh-env 'app.core)]
    (h/analyze cenv '(def answer 42))
    (let [^Namespace ns (env/cljs-ns cenv)
          v (.findInternedVar ns 'answer)]
      (is (instance? Var v))
      (is (= 'app.core/answer (symbol (str (.getName (.ns v))) (str (.sym v)))))
      ;; root-unbound: there is no runtime value on this side
      (is (not (.isBound v)))
      ;; and the JVM's own registry is untouched, which is what NamespaceWorld is for
      (is (nil? (.find NamespaceWorld/DEFAULT 'app.core))))))

(deftest test-def-metadata
  (let [cenv (h/fresh-env 'app.core)]
    (h/analyze cenv '(def ^{:doc "the answer"} answer 42))
    (is (= "the answer" (:doc (meta (.findInternedVar ^Namespace (env/cljs-ns cenv)
                                                      'answer)))))))

;; --- the ns form ------------------------------------------------------------

(defn- two-namespaces
  "A cenv where my-lib.core holds one var, and the cursor is back at cljs.user.
  The starting point for anything that needs a namespace to require."
  []
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns my-lib.core))
    (h/analyze cenv '(def helper 41))
    (env/set-current-ns! 'cljs.user)
    cenv))

(deftest test-ns-moves-the-cursor
  (let [cenv (h/fresh-env 'cljs.user)]
    (is (= 'cljs.user env/*current-ns*))
    (h/analyze cenv '(ns app.core))
    (is (= 'app.core env/*current-ns*))
    ;; and the namespace exists in the ClojureScript world, not the JVM's
    (is (some? (env/find-cljs-ns cenv 'app.core)))
    (is (nil? (find-ns 'app.core)))))

(deftest test-ns-records-requires-and-aliases
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core (:require [my-lib.core :as lib])))
    (is (= #{'my-lib.core} (env/declared-requires cenv 'app.core)))
    (is (= 'my-lib.core
           (.getName ^Namespace (.lookupAlias ^Namespace (env/cljs-ns cenv) 'lib))))))

(deftest test-a-qualified-symbol-resolves-through-an-alias-or-a-full-name
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core (:require [my-lib.core :as lib])))
    (are [sym] (= '{:op :var :name my-lib.core/helper :ns my-lib.core}
                  (select-keys (h/analyze cenv sym) [:op :name :ns]))
      'lib/helper
      'my-lib.core/helper)
    ;; and the namespace's own name works without requiring itself
    (h/analyze cenv '(def here 1))
    (is (= 'app.core/here (:name (h/analyze cenv 'app.core/here))))))

(deftest test-a-compiled-namespace-written-out-in-full-is-its-own-require
  ;; §5.27 REPLACED the rule this test used to assert, which was that a namespace
  ;; this file had not required stayed an error however visible it was. The reason
  ;; given for it was that a var of ours is a property of a namespace object nobody
  ;; bound until the require puts it in the module's imports - so resolving one
  ;; without a require would compile and then fail to run.
  ;;
  ;; It would. But RECORDING the require is what binds it, and that is what happens
  ;; now, exactly as require-goog! has done for a Closure name since §5.18.
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core))
    (is (= 'my-lib.core/helper (:name (h/analyze cenv 'my-lib.core/helper))))
    ;; and the module will import it, because module-text reads env/requires after
    ;; the whole body is analysed
    (is (contains? (env/requires cenv 'app.core) 'my-lib.core))
    ;; saying so in the ns form changes nothing about the answer
    (h/analyze cenv '(ns app.core (:require [my-lib.core])))
    (is (= 'my-lib.core/helper (:name (h/analyze cenv 'my-lib.core/helper))))
    ;; the var is still checked
    (is (re-find #"No such var: my-lib.core/nope"
                 (h/message #(h/analyze cenv 'my-lib.core/nope)))))

  (testing "DECLARED, not merely named - that is the whole of the remaining rule"
    ;; add-require! creates the Namespace on being named, so existence says only
    ;; that something mentioned it. There is no module for an import to reach, and
    ;; the driver needs the name in the ns form UP FRONT to compile it at all.
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.a (:require [app.ghost])))
      (h/analyze cenv '(ns app.b))
      (is (re-find #"No such namespace: app.ghost"
                   (h/message #(h/analyze cenv 'app.ghost/x)))))))

(deftest test-refer-maps-a-var-in
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core (:require [my-lib.core :refer [helper]])))
    ;; unqualified, and it is the same var - not a copy
    (is (= 'my-lib.core/helper (:name (h/analyze cenv 'helper))))
    ;; what a namespace refers is NOT reachable through its name: Clojure and
    ;; cljs.analyzer both resolve a qualified symbol against what a namespace
    ;; DEFINES
    (h/analyze cenv '(ns other.ns (:require [app.core :as a])))
    (is (re-find #"No such var: a/helper"
                 (h/message #(h/analyze cenv 'a/helper))))))

(deftest test-refer-of-a-var-that-is-not-there-says-why
  (let [cenv (two-namespaces)]
    (let [msg (h/message #(h/analyze cenv '(ns app.core
                                             (:require [my-lib.core :refer [nope]]))))]
      (is (re-find #"Cannot refer nope from my-lib.core" msg))
      ;; the likely cause, named: requiring does not compile anything yet
      (is (re-find #"does not compile it yet" msg)))))

(deftest test-use-is-require-with-only
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core (:use [my-lib.core :only [helper]])))
    (is (= 'my-lib.core/helper (:name (h/analyze cenv 'helper))))
    (is (= #{'my-lib.core} (env/declared-requires cenv 'app.core))))
  (let [cenv (two-namespaces)]
    (is (re-find #":use of my-lib.core needs :only"
                 (h/message #(h/analyze cenv '(ns app.core (:use [my-lib.core]))))))))

(deftest test-a-local-may-shadow-catch-and-finally
  ;; doc/cljs-compiler.md §5.24. Neither is a special form - cljs.analyzer's
  ;; `specials` set has neither, and both are recognised positionally by try's
  ;; parser and nowhere else - so a local shadows them. core_test.cljs:1496 does
  ;; it on purpose: (is (= 1 (let [catch identity] (catch 1))))
  (are [form] (= :invoke (:op (-> (h/analyze form) :body :ret)))
    '(let* [catch (fn* ([x] x))] (catch 1))
    '(let* [finally (fn* ([x] x))] (finally 1)))

  ;; they stay in the parser table for the message. Someone who gets the shape of
  ;; a try wrong writes (catch ...) in the open, and "the symbol catch is neither
  ;; a local nor a var" would send them looking for a var they never meant to name
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(catch js/Error e 1) #"catch is only valid inside a try"
    '(finally 1)          #"finally is only valid inside a try")

  ;; and inside a try they are still the clauses
  (is (= :try (:op (h/analyze '(try 1 (catch js/Error e 2) (finally 3)))))))

(deftest test-rename-refers-a-var-under-another-name
  ;; doc/cljs-compiler.md §5.24. A rename is a refer under another name, and the
  ;; name it replaces is NOT also referred - cljs.analyzer computes the same set
  ;; as referred-without-renamed.
  (let [lib (fn []
              (let [cenv (h/fresh-env 'cljs.user)]
                (h/analyze cenv '(ns lib.a))
                (h/analyze cenv '(def one 1))
                (h/analyze cenv '(def two 2))
                (env/set-current-ns! 'cljs.user)
                cenv))
        mapped (fn [cenv]
                 (set (map first (.getMappings ^Namespace
                                  (env/cljs-ns cenv 'app.core)))))]
    (let [cenv (lib)]
      (h/analyze cenv '(ns app.core (:require [lib.a :refer [one] :rename {one uno}])))
      (is (= '#{uno} (mapped cenv))
          "the source name is gone: two names on one var would make :rename useless"))

    (testing "naming it in :rename is enough to ask for it"
      ;; :refer [x] :rename {x y} and :rename {x y} mean the same thing, so
      ;; neither spelling is a trap
      (let [cenv (lib)]
        (h/analyze cenv '(ns app.core (:require [lib.a :rename {two dos}])))
        (is (= '#{dos} (mapped cenv)))))

    (testing "and it leaves the other refers alone"
      (let [cenv (lib)]
        (h/analyze cenv '(ns app.core (:require [lib.a :refer [one two] :rename {one uno}])))
        (is (= '#{two uno} (mapped cenv))))))

  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    ;; a renamed name is checked like any other referred name
    '(ns app.core (:require [cljs.core :rename {nope n}]))  #"Cannot refer nope"
    '(ns app.core (:require [cljs.core :rename [a b]]))     #"map of simple symbols"
    ;; one name for two vars would silently keep whichever applied last
    '(ns app.core (:require [cljs.core :rename {first a rest a}])) #"one name to two vars"))

(deftest test-cljs-core-is-its-own-macro-namespace-without-saying-so
  ;; §5.17's rule is that a namespace keeping its macros beside it is one
  ;; namespace to whoever requires it, and the evidence is its own ns form.
  ;; cljs.core is the exception: its ns form asks for five goog namespaces and
  ;; nothing else, because every namespace gets its macros through :core-macros
  ;; anyway (§5.12). Same fact, reached through the mechanism.
  ;;
  ;; (:require [cljs.core :refer [await]]) is what needs it - await is a macro at
  ;; core.cljc:1036 and nothing at all in core.cljs.
  (let [cenv (h/fresh-env 'cljs.user)]
    (is (nil? (h/message #(h/analyze cenv '(ns app.core (:require [cljs.core :refer [when-not]]))))))
    ;; and it is a MACRO refer, so nothing was interned as a var here
    (is (not (contains? (set (map first (.getMappings ^Namespace (env/cljs-ns cenv 'app.core))))
                        'when-not)))))

(deftest test-ns-refusals
  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(ns "app.core")                    #"must be an unqualified symbol"
    '(ns foo/bar)                       #"must be an unqualified symbol"
    '(ns app.core (:require 1))         #"Bad :require spec"
    '(ns app.core (:require [a :as]))   #"Bad :require spec"
    ;; the shape someone reaching for Clojure's ns writes
    '(ns app.core (:require [a [b :as c]])) #"no prefix lists"
    '(ns app.core (:require [a :as 1]))     #":as must be a simple symbol"
    ;; a.b rather than a: an UNDOTTED name with no source is shadow's spelling of a
    ;; JavaScript module (§5.53), and a module's :refer is checked by the other
    ;; half - which is the row below this one
    '(ns app.core (:require [a.b :refer x]))  #"sequence of simple symbols"
    '(ns app.core (:require [a :refer x]))    #":refer takes a vector of symbols"
    ;; :rename is supported now (§5.24); what is still refused is its shape
    '(ns app.core (:require [a :rename [b c]])) #"map of simple symbols"
    ;; :import works now (M5's goog subset), so what is refused is a class that is
    ;; not a Closure one and a spec that is not a class at all
    '(ns app.core (:import [my.lib Thing]))  #"names a CLOSURE class"
    '(ns app.core (:import StringBuffer))    #"needs a namespace"
    '(ns app.core (:import [goog.string]))   #"Bad :import spec"
    '(ns app.core (:import [goog.string Nonesuch])) #"No such Closure class"
    ;; a REFERENCE may be spelled with a slash and mean the same class (§5.18); an
    ;; :import SPEC may not, and ClojureScript refuses it too - taking it would be a
    ;; spelling that compiles here and nowhere else
    '(ns app.core (:import goog.string/StringBuffer)) #"written with a dot, not a slash"
    '(ns app.core (:nonsense))          #"Unknown ns reference :nonsense"
    '(ns app.core :require)             #"Bad ns reference"))

(deftest test-the-two-import-spellings-are-one-spec
  ;; The class written out is the spelling cljs.core uses and the one
  ;; ClojureScript's ns form documents; [ns Class*] is the other. plan-import used
  ;; to refuse the first with a message recommending it, and accept
  ;; goog.string/StringBuffer, which no ClojureScript ns form has ever taken.
  (are [form] (nil? (refuses form))
    '(ns app.core (:import goog.math.Long))
    '(ns app.core (:import [goog.math Long]))
    '(ns app.core (:import goog.string.StringBuffer)))
  ;; and both reach the same class: the LAST dot splits the namespace from it, so
  ;; the require is of goog.math.Long and not of a Long in goog.math
  (doseq [form '[(ns app.core (:import goog.math.Long))
                 (ns app.core (:import [goog.math Long]))]]
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv form)
      (is (contains? (env/requires cenv 'app.core) 'goog.math.Long) (pr-str form))
      (is (= :goog-ns (:op (h/analyze cenv 'Long))) (pr-str form)))))

(deftest test-an-import-is-recorded-as-one
  ;; §5.30. An :import applies as a require plus an alias, and the alias is all the
  ;; rest of the compiler needs. What an alias cannot say is WHICH of a namespace's
  ;; aliases came from an :import - which is the whole of what cljs.core/ns-imports
  ;; asks, and the reason that macro used to hand back an empty map.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:require [goog.string :as gstring])
                       (:import [goog.math Long] goog.string.StringBuffer)))
    (is (= '{Long goog.math.Long
             StringBuffer goog.string.StringBuffer}
           (env/imports cenv 'app.core)))
    ;; the :require's alias is not one of them
    (is (not (contains? (env/imports cenv 'app.core) 'gstring)))

    (testing "and a second ns form replaces rather than adds"
      ;; an ns form DECLARES, so re-analysing one - which is what recompiling an
      ;; edited file is - has to drop what the last one left
      (h/analyze cenv '(ns app.core (:import [goog.math Long])))
      (is (= '{Long goog.math.Long} (env/imports cenv 'app.core))))))

(deftest test-a-def-of-a-core-name-takes-the-macro-too
  ;; §5.32. Interning is enough for RESOLUTION - resolve-var asks this namespace
  ;; before it asks cljs.core - but a macro is expanded before anything is
  ;; resolved, so a namespace that defines `/` would still see every (/ x y) in it
  ;; expand to cljs.core's division. cljs/extend_to_native_test.cljs is the case:
  ;; (defprotocol Slashy (/ [_])).
  (let [cenv (h/core-env 'app.ex1)]
    (is (not (env/excluded? cenv 'app.ex1 '/)))
    (h/analyze cenv '(def / 1))
    (is (env/excluded? cenv 'app.ex1 '/))
    ;; and the name now resolves here, which it already did
    (is (= 'app.ex1// (:name (h/analyze cenv '/)))))

  (testing "a name cljs.core does not have is not excluded"
    (let [cenv (h/core-env 'app.ex2)]
      (h/analyze cenv '(def not-a-core-name 1))
      (is (not (env/excluded? cenv 'app.ex2 'not-a-core-name)))))

  (testing "a core VAR counts, not only a core macro"
    ;; core-name? asks both, as cljs.analyzer's does
    (let [cenv (h/core-env 'app.ex3)]
      (h/analyze cenv '(def reduce 1))
      (is (env/excluded? cenv 'app.ex3 'reduce))))

  (testing "not in cljs.core, which would exclude every name it defines"
    (let [cenv (h/core-env 'cljs.core)]
      (h/analyze cenv '(def map 1))
      (is (not (env/excluded? cenv 'cljs.core 'map))))))

(deftest test-boolean-is-the-one-tag-this-analyzer-carries
  ;; §5.32. ^boolean is an assertion by the PROGRAM - nothing here infers a tag -
  ;; and it reaches a node from three places, because cljs.core writes it in three.
  (let [cenv (h/core-env 'app.tg)]
    (testing "on a var, read where the var is referred"
      (h/analyze cenv '(def ^boolean b true))
      (is (= 'boolean (:tag (h/analyze cenv 'b)))))

    (testing "on a defn name, which is a RETURN tag - so it is kept apart"
      (h/analyze cenv '(defn ^boolean p [x] true))
      (let [v (h/analyze cenv 'p)]
        (is (= 'boolean (:tag v)))
        (is (= 'boolean (:ret-tag v))))
      ;; and the invoke wears it, not the var reference
      (is (= 'boolean (:tag (h/analyze cenv '(p 1)))))
      ;; a plain defn tags neither
      (h/analyze cenv '(defn q [x] true))
      (is (nil? (:tag (h/analyze cenv '(q 1))))))

    (testing "on a js* form, which is how cljs.core spells it for what it inlines"
      ;; cljs.core/bool-expr (core.cljc:952) is (vary-meta e assoc :tag 'boolean),
      ;; and it wraps the js* of coercive-=, ==, < and twenty more
      (is (= 'boolean (:tag (h/analyze cenv (with-meta '(js* "(~{} == null)" 1)
                                              {:tag 'boolean})))))
      (is (nil? (:tag (h/analyze cenv '(js* "(~{} == null)" 1))))))

    (testing "on a local binding, and on a reference to it"
      (let [node (h/analyze cenv '(let* [^boolean x true] x))]
        (is (= 'boolean (:tag (first (:bindings node)))))
        ;; a let's body is a :do, whose :ret is the reference
        (is (= 'boolean (:tag (:ret (:body node)))))))))

(deftest test-refer-global-names-a-host-global
  ;; (:refer-global :only [Object String]) - the ns form's way of saying `Object
  ;; here is the host's`. There is nothing to require: js is a symbol prefix
  ;; rather than a namespace, so this maps one name to another and no module,
  ;; import or namespace object is involved.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core (:refer-global :only [Object String])))
    (let [node (h/analyze cenv 'Object)]
      (is (= :js-var (:op node)))
      (is (= 'js/Object (:name node)))))

  (testing ":rename gives it another name here"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core (:refer-global :only [Object] :rename {Object Obj})))
      (is (= 'js/Object (:name (h/analyze cenv 'Obj))))
      ;; and the original name is no longer referred, which is what rename means
      (is (re-find #"neither a local nor a var"
                   (h/message #(h/analyze cenv 'Object))))))

  (testing "a def in this namespace wins, as it does over any refer"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core (:refer-global :only [Object])))
      (h/analyze cenv '(def Object 1))
      (is (= :var (:op (h/analyze cenv 'Object))))))

  (testing "and it is declared, not assumed"
    (is (re-find #"neither a local nor a var"
                 (h/message #(h/analyze (h/fresh-env 'app.core) 'Object)))))

  (are [form expected] (some? (re-find expected (or (refuses form) "")))
    '(ns app.core (:refer-global :only []))            #"non-empty vector"
    '(ns app.core (:refer-global :only [a] :extra 1))  #"Unsupported option :extra"
    '(ns app.core (:refer-global :only [Object] :rename {Nope N})) #"which is not in :only"))

(deftest test-ns-must-be-top-level
  ;; the reason is not pedantry: the ns form's work happens during ANALYSIS, so
  ;; inside a function body it would move the compiler's namespace while the
  ;; emitted code moved nothing
  (let [msg (refuses '(fn* ([] (ns app.core))))]
    (is (re-find #"ns must appear at the top level" msg))
    (is (re-find #"analysis-time effect" msg)))
  ;; a do keeps it: (do (ns a) ...) is top level in Clojure too
  (is (nil? (refuses '(do (ns app.core))))))

(deftest test-a-failed-ns-form-applies-none-of-itself
  ;; Every reference is checked before any is applied. Without that, the require
  ;; below was recorded before the refer beside it was checked - and then every
  ;; later script in the session asked the runtime to fetch a namespace that was
  ;; never going to exist, so one typo cost the whole session rather than one form.
  (let [cenv (two-namespaces)]
    (is (some? (h/message #(h/analyze cenv '(ns app.core
                                              (:require [my-lib.core :refer [nope]]))))))
    ;; a REPL user retypes the corrected form from the namespace they were in
    (is (= 'cljs.user env/*current-ns*))
    (is (empty? (env/declared-requires cenv 'app.core))))
  ;; and it holds across specs: the good one beside the bad one is not applied
  (let [cenv (two-namespaces)]
    (is (some? (h/message #(h/analyze cenv '(ns app.core
                                              (:require [my-lib.core :as lib]
                                                        [nope.ns :refer [gone]]))))))
    (is (empty? (env/declared-requires cenv 'app.core)))
    (is (nil? (.lookupAlias ^Namespace (env/cljs-ns cenv 'app.core) 'lib))))
  ;; a macro namespace that does not load fails the same way
  (let [cenv (two-namespaces)]
    (is (some? (h/message #(h/analyze cenv '(ns app.core
                                              (:require [my-lib.core :as lib])
                                              (:require-macros [no.such.macros]))))))
    (is (empty? (env/declared-requires cenv 'app.core)))))

(deftest test-refer-clojure-exclude-is-recorded
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core (:refer-clojure :exclude [map when])))
    (is (env/excluded? cenv 'app.core 'map))
    (is (env/excluded? cenv 'app.core 'when))
    (is (not (env/excluded? cenv 'app.core 'inc)))))

(deftest test-refer-clojure-rename-excludes-the-name-it-replaces
  ;; §5.28. (:refer-clojure :rename {mapv core-mapv}) gives the var ONE name here
  ;; and it is the new one - which is the reading :require :rename already has, and
  ;; the one cljs/ns_test.cljs checks with (exists? mapv) / (exists? core-mapv).
  (let [cenv (h/core-env 'app.renaming)]
    (h/analyze cenv '(ns app.renaming (:refer-clojure :rename {mapv core-mapv})))
    (is (env/excluded? cenv 'app.renaming 'mapv))
    (is (= 'cljs.core/mapv (env/var-sym cenv 'core-mapv)))
    ;; the source is gone rather than aliased: nothing here resolves `mapv`
    (is (nil? (env/resolve-var cenv 'mapv)))
    ;; and :exclude beside it still works, on names it did not rename
    (h/analyze cenv '(ns app.renaming2 (:refer-clojure :exclude [inc]
                                                       :rename {mapv core-mapv})))
    (is (env/excluded? cenv 'app.renaming2 'inc))
    (is (env/excluded? cenv 'app.renaming2 'mapv))))

(deftest test-refer-clojure-rename-refuses-what-it-cannot-do
  (let [cenv (h/core-env 'app.badrename)]
    (is (re-find #"cljs.core/no-such-core-var, which does not exist"
                 (h/message
                  #(h/analyze cenv '(ns app.badrename
                                      (:refer-clojure
                                       :rename {no-such-core-var x}))))))
    (is (re-find #":rename takes a map of simple symbols"
                 (h/message
                  #(h/analyze cenv '(ns app.badrename
                                      (:refer-clojure :rename [mapv m]))))))
    (is (re-find #"Unsupported option :only in :refer-clojure"
                 (h/message
                  #(h/analyze cenv '(ns app.badrename
                                      (:refer-clojure :only [mapv]))))))))

(deftest test-ns-docstring-and-attrs-land-on-the-namespace
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core "what it does" {:author "someone"}))
    (let [m (meta (env/cljs-ns cenv 'app.core))]
      (is (= "what it does" (:doc m)))
      (is (= "someone" (:author m))))))

;; --- macros, which arrive from the JVM rather than from the ns's own world ----

(defmacro twice
  "A ClojureScript macro is an ordinary Clojure macro in a real JVM namespace, so
  this file can be one - which is all a :require-macros target has to be."
  [x]
  (list 'js* "(~{} + ~{})" x x))

(defn- macro-env
  "A cenv whose core macros are this namespace, so `twice` is in scope unqualified
  the way a cljs.core macro will be."
  []
  (env/compile-env {:ns 'cljs.user :core-macros 'clojure.cljs.analyzer-test}))

(deftest test-refer-clojure-exclude-suppresses-a-core-macro
  (let [cenv (macro-env)]
    (h/analyze cenv '(ns app.core))
    (is (= :js (:op (h/analyze cenv '(twice 21)))))
    ;; the same name, excluded: no expansion, so it is read as a function call and
    ;; the head symbol resolves to nothing
    (h/analyze cenv '(ns other.ns (:refer-clojure :exclude [twice])))
    (is (re-find #"neither a local nor a var"
                 (h/message #(h/analyze cenv '(twice 21)))))
    ;; and it is per namespace: back in app.core the macro is there again
    (env/set-current-ns! 'app.core)
    (is (= :js (:op (h/analyze cenv '(twice 21)))))))

(deftest test-require-macros-brings-a-jvm-namespace-in
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:require-macros [clojure.cljs.analyzer-test :as m
                                         :refer [twice]])))
    ;; both spellings expand
    (is (= :js (:op (h/analyze cenv '(twice 21)))))
    (is (= :js (:op (h/analyze cenv '(m/twice 21)))))
    ;; and nothing about the macro namespace entered the ClojureScript world
    (is (nil? (env/find-cljs-ns cenv 'clojure.cljs.analyzer-test)))))

(deftest test-require-macros-rename-is-the-macro-side-of-the-same-rule
  ;; §5.28. Same reading as :require :rename: the new name expands and the old one
  ;; does not, whether or not :refer also asked for it.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:require-macros [clojure.cljs.analyzer-test :as m
                                         :refer [twice] :rename {twice double-it}])))
    (is (= :js (:op (h/analyze cenv '(double-it 21)))))
    ;; qualified through the alias, the macro is still under its own name
    (is (= :js (:op (h/analyze cenv '(m/twice 21)))))
    ;; the renamed source is not also referred
    (is (re-find #"neither a local nor a var"
                 (h/message #(h/analyze cenv '(twice 21))))))
  ;; :rename alone is enough to ask for the macro - no :refer needed
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.two
                       (:require-macros [clojure.cljs.analyzer-test
                                         :rename {twice double-it}])))
    (is (= :js (:op (h/analyze cenv '(double-it 21))))))
  ;; and a rename of something that is not a macro there says so
  (let [cenv (h/fresh-env 'cljs.user)]
    (is (re-find #"does not exist"
                 (h/message
                  #(h/analyze cenv '(ns app.three
                                      (:require-macros
                                       [clojure.cljs.analyzer-test
                                        :rename {no-such-macro m}]))))))))

(defmacro upstream-expansion-of
  "What core.async's `go` does to its body, in miniature.

  `go` walks its body to build a state machine, and walking means macroexpanding -
  so ioc_macros.clj:728 calls cljs.analyzer/macroexpand-1, UPSTREAM's, on an &env
  it was handed by ours. This is that call and nothing else, with the expansion
  handed back quoted so a test can read it. See doc/cljs-compiler.md 5.55.

  requiring-resolve rather than a :require, because the ClojureScript jar is a test
  dependency and this file has to load without it; every test that uses this macro
  is guarded by h/cljs-analyzer?."
  [form]
  (list 'quote ((requiring-resolve 'cljs.analyzer/macroexpand-1) &env form)))

(defmacro spec-checked
  "A macro with an :args spec, for the one test that needs clojure.spec to have an
  opinion about a macro CALL rather than about a value."
  [x]
  (list 'js* "~{}" x))

(spec/fdef spec-checked :args (spec/cat :x number?))

(h/deftest-when h/cljs-analyzer? test-specs-macro-check-does-not-run
  ;; :spec-skip-macros, the one thing macroexpand/upstream-compiler-state actually
  ;; decides - and it is a decision rather than a default. Upstream's
  ;; do-macroexpand-check runs clojure.spec.alpha/macroexpand-check on every macro
  ;; it expands unless that option says not to, and the option is the only thing
  ;; stopping it: clojure.spec.alpha is loaded in this JVM before any test runs and
  ;; macroexpand-check resolves, so the guard around it passes.
  ;;
  ;; We skip it because OUR macroexpander does not run it, and a form that expands
  ;; one way through clojure.cljs.macroexpand and throws through cljs.analyzer
  ;; would be two compilers in one process disagreeing about the same file.
  ;;
  ;; Written because the defeat that removes the option came back INERT: nothing in
  ;; the suite had an :args spec to violate, so the option could be deleted without
  ;; a test noticing. It is not dead code - defeat it now and this throws
  ;; :macro-syntax-check.
  (let [cenv (h/core-env 'app.spec)]
    (h/analyze cenv '(ns app.spec
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [upstream-expansion-of spec-checked]])))
    ;; "nope" violates (spec/cat :x number?) on purpose
    (is (= '(js* "~{}" "nope")
           (second (macroexpand/macroexpand-1
                    cenv (env/analysis-env cenv)
                    '(upstream-expansion-of (spec-checked "nope"))))))))

(deftest test-the-analysis-env-carries-what-a-macro-reads
  ;; 5.55. Three keys that used to be part of `ClojureScript's shape, minus what
  ;; does not exist yet` and now exist, because somebody else's macro reads them.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:refer-clojure :exclude [time])
                       (:require [clojure.string :as string])
                       (:require-macros [clojure.cljs.analyzer-test :refer [twice]])))
    (let [ns-map (:ns (env/analysis-env cenv))]
      ;; :requires is EVERY name by which this namespace can call something it
      ;; requires, mapped to that thing's real name - the alias and the full name
      ;; both, because both are things a program may write. core.async's
      ;; fixup-aliases is the reader that matters: it turns the a/<! everybody
      ;; writes into the cljs.core.async/<! its terminator table is keyed by.
      (is (= 'clojure.string (get (:requires ns-map) 'string)))
      (is (= 'clojure.string (get (:requires ns-map) 'clojure.string)))
      ;; a JavaScript module is NOT in it - it is not a namespace here (5.51)
      (is (= #{} (set (filter string? (vals (:requires ns-map))))))
      (is (= #{'time} (:excludes ns-map)))
      (is (= 'clojure.cljs.analyzer-test (get (:use-macros ns-map) 'twice))))))

(h/deftest-when h/cljs-analyzer? test-a-macro-may-call-upstreams-analyzer
  ;; The whole of what core.async's `go` needed. With cljs.env/*compiler* unbound
  ;; this is a NullPointerException out of clojure.core/deref-future - upstream's
  ;; excluded? derefs that var, (deref nil) is not an IDeref so it is tried as a
  ;; java.util.concurrent.Future, and 241 of nosco-gamma's 414 namespaces died
  ;; there. See macroexpand/upstream-compiler-state.
  (let [cenv (h/core-env 'app.upstream)]
    (h/analyze cenv '(ns app.upstream
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [upstream-expansion-of]])))
    (let [expanded (second (macroexpand/macroexpand-1
                            cenv (env/analysis-env cenv)
                            '(upstream-expansion-of (when x 1))))]
      (is (seq? expanded))
      (is (= 'if (first expanded))))))

(h/deftest-when h/cljs-analyzer? test-an-exclusion-reaches-upstreams-macro-lookup
  ;; THE REASON &env CARRIES THE FACTS RATHER THAN THE ATOM. Upstream's excluded?
  ;; asks &env first and the compiler-state atom only as a fallback, so answering
  ;; truthfully there is what makes the atom a constant. Binding an atom and
  ;; stopping - not touching &env at all - also makes `go` compile, and then
  ;; `nothing is excluded` is the answer for every namespace: a core MACRO the ns
  ;; form excluded goes on expanding inside a go body, silently, over the top of
  ;; the var the program defined instead.
  ;;
  ;; `time` rather than a name picked at random: it is a cljs.core macro, so
  ;; excluding it is a question macro lookup actually has to answer. Run end to
  ;; end, the defeat of this prints `Elapsed time: 0.027292 msecs` where the
  ;; program said `mine:3`.
  (let [cenv (h/core-env 'app.excluder)]
    (h/analyze cenv '(ns app.excluder
                       (:refer-clojure :exclude [time])
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [upstream-expansion-of]])))
    (is (= '(time 1)
           (second (macroexpand/macroexpand-1
                    cenv (env/analysis-env cenv)
                    '(upstream-expansion-of (time 1))))))
    ;; and a core macro it did NOT exclude still expands, or the test above would
    ;; pass for a compiler that had simply stopped expanding anything
    (is (= 'if (first (second (macroexpand/macroexpand-1
                              cenv (env/analysis-env cenv)
                              '(upstream-expansion-of (when x 1)))))))))

(defmacro intern-and-return-a-var
  "sci.impl.cljs's (require-cljs-analyzer-api) in miniature.

  A macro called for what it does WHILE EXPANDING rather than for what it expands
  to: sci's interns two JVM vars holding cljs.analyzer.api functions, this one
  interns one var, and in both the last form of the body is a `def`. `def`
  evaluates to the var it interned, so the EXPANSION is that var - a
  clojure.lang.Var handed back to the analyzer as a form, by accident, because
  nobody chose what the macro should return. See doc/cljs-compiler.md 5.56."
  []
  (def interned-while-expanding :the-effect-the-macro-was-called-for))

(deftest test-a-macro-may-expand-to-a-var
  ;; 5.56. THE FORM IS A JVM OBJECT, and there is no other way to write one: #'foo
  ;; reads as (var foo), which is a list and a different form entirely.
  (let [cenv (h/fresh-env 'app.residue)]
    (h/analyze cenv '(ns app.residue
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [intern-and-return-a-var]])))
    (let [node (h/analyze cenv '(intern-and-return-a-var))]
      ;; a constant, which is what cljs.analyzer makes of one too - its
      ;; analyze-form has no Var case either, so a Var falls into the :else that
      ;; builds a :const node
      (is (= :const (:op node)))
      (is (instance? Var (:val node)))

      ;; the interning happened, which is the whole of what the macro was for
      (is (= :the-effect-the-macro-was-called-for
             @(resolve 'clojure.cljs.analyzer-test/interned-while-expanding)))

      ;; AND NOTHING IS EMITTED. The value is discarded at the top level, a
      ;; discarded constant is dropped rather than evaluated (see emitter/no-effect),
      ;; and emitter/unspellable is what lets it be dropped without first being
      ;; built. cljs.compiler arrives at the same empty output by a different road:
      ;; its emit* :const skips a :statement context before reaching emit-constant*,
      ;; which has no Var method and would throw if it did reach it.
      (is (= [] (emitter/emit-top-lines node)))

      ;; the same as a statement among others, where what follows still runs
      (is (= ["side();"]
             (emitter/emit-top-lines
              (h/analyze cenv '(do (intern-and-return-a-var) (js* "side()")))))))))

(deftest test-a-var-is-refused-where-its-value-is-wanted
  ;; The other half, and the half that keeps the first one honest: dropping it is
  ;; right only because nothing wanted it. Anywhere a program actually reads the
  ;; value, the refusal deferred by emitter/unspellable is thrown - by the `str`
  ;; that reads the expression, naming what it could not spell. cljs.compiler
  ;; refuses these three too: "clojure.lang.Var is not a valid ClojureScript
  ;; constant", out of emit-constant*.
  (let [cenv (h/fresh-env 'app.residue2)
        read-by (fn [form & [f]]
                  (h/message #(if f
                                (emitter/emit-top-lines (h/analyze cenv form) f)
                                (emitter/emit-top-lines (h/analyze cenv form)))))]
    (h/analyze cenv '(ns app.residue2
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [intern-and-return-a-var]])))
    (are [form] (re-find #"a Var constant" (or (read-by form) ""))
      '(js* "~{}" (intern-and-return-a-var))
      '(let* [x (intern-and-return-a-var)] (js* "~{}" x))
      '(js* "f(~{})" (do 1 (intern-and-return-a-var))))
    ;; and returned rather than discarded, which is the REPL's destination
    (is (re-find #"a Var constant"
                 (or (read-by '(intern-and-return-a-var) emitter/return-value) "")))))

(deftest test-a-source-position-does-not-force-a-var
  ;; The one subtlety in emitter/unspellable, and the reason it does not go through
  ;; ->result. ->result maps source-map/fill over both channels, fill stringifies
  ;; whatever it is given, and stringifying this IS the refusal - so a constant
  ;; that carried a position would be refused before anything asked whether its
  ;; value was wanted. Which is to say: with source maps on, every namespace sci
  ;; is required from.
  (let [cenv (h/fresh-env 'app.residue3)]
    (h/analyze cenv '(ns app.residue3
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [intern-and-return-a-var]])))
    (let [positioned (assoc (env/analysis-env cenv)
                            :file "residue3.cljs" :line 12 :column 3)]
      (is (= [] (emitter/emit-top-lines
                 (ana/analyze-top cenv positioned '(intern-and-return-a-var))))))))

(defmacro the-macro-time-ns
  "(ns-name *ns*), quoted - what a macro sees when it asks which namespace it is
  expanding inside. kitchen-async's fixup-alias asks exactly this, and uses the
  answer to key into the compiler-state atom. See doc/cljs-compiler.md 5.57."
  []
  (list 'quote (ns-name *ns*)))

(defmacro upstream-resolution-of
  "cljs.analyzer.api/resolve on `sym`, quoted, with the &env this compiler handed
  us - sci's copy-vars does precisely this to find out whether a name is a
  protocol. requiring-resolve for upstream-expansion-of's reason."
  [sym]
  (list 'quote (select-keys ((requiring-resolve 'cljs.analyzer.api/resolve) &env sym)
                            [:name :ns :protocol-symbol :protocol-info])))

(defmacro upstream-compiler-state-now
  "The compiler-state atom itself, so a test can look at what upstream would see."
  []
  (list 'quote @@(requiring-resolve 'cljs.env/*compiler*)))

(deftest test-a-macro-sees-the-clojurescript-namespace-as-ns
  ;; 5.57. *ns* is bound to the MACRO VIEW - a clojure.lang.Namespace named after
  ;; the ClojureScript namespace, living in a world of its own, which is the object
  ;; cljs.analyzer mints with (create-ns *cljs-ns*) and the collision
  ;; NamespaceWorld exists to avoid. Before this it was bound to nothing, so a
  ;; macro asking got whichever JVM namespace happened to be compiling.
  (let [cenv (h/fresh-env 'app.whereami)]
    (h/analyze cenv '(ns app.whereami
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [the-macro-time-ns]])))
    (is (= 'app.whereami
           (second (macroexpand/macroexpand-1
                    cenv (env/analysis-env cenv) '(the-macro-time-ns)))))

    (testing "and our own core.cljc is a reader of it"
      ;; goog-define builds the name Closure knows the define by out of *ns*, so
      ;; with nothing bound it named whichever JVM namespace was compiling - a
      ;; silent wrong answer that no test had, because nothing else in core.cljc
      ;; asks. app$SLASH$ is (str *ns* "/" sym) munged.
      (is (re-find #"app\.whereami\$SLASH\$MY\$US\$FLAG"
                   (pr-str (macroexpand/macroexpand-1
                            cenv (env/analysis-env cenv)
                            '(goog-define MY_FLAG "d"))))))))

(h/deftest-when h/cljs-analyzer? test-the-upstream-symbol-table-answers-a-resolve
  ;; THE QUESTION sci's protocol-vars ASKS, and the reason the compiler-state atom
  ;; could not stay the constant 5.55 left it as. cljs.analyzer.api is a facade
  ;; over that atom and does not consult &env at all, so there is no other road in:
  ;; with nothing under ::namespaces, resolving a protocol name falls through to a
  ;; synthesised {:name cljs.core/ICloneable} carrying neither :protocol-symbol nor
  ;; :protocol-info, and sci throws "Not a protocol: ICloneable".
  (let [cenv (h/core-env 'app.resolver)]
    (h/analyze cenv '(ns app.resolver
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [upstream-resolution-of]])))
    (h/analyze cenv '(defprotocol IShape (area [this])))
    (let [info (second (macroexpand/macroexpand-1
                        cenv (env/analysis-env cenv)
                        '(upstream-resolution-of IShape)))]
      (is (= 'app.resolver/IShape (:name info)))
      (is (true? (:protocol-symbol info)))
      ;; the methods, which is what protocol-vars walks to build its entry
      (is (contains? (:methods (:protocol-info info)) 'area)))

    ;; and a cljs.core protocol, which is the one sci actually asks about - it
    ;; reaches it through core-name?, a different branch of resolve-var and a
    ;; different entry of the map
    (let [info (second (macroexpand/macroexpand-1
                        cenv (env/analysis-env cenv)
                        '(upstream-resolution-of ICloneable)))]
      (is (= 'cljs.core/ICloneable (:name info)))
      (is (true? (:protocol-symbol info))))))

(h/deftest-when h/cljs-analyzer? test-the-upstream-symbol-table-is-a-view-not-a-copy
  ;; What the shape buys, stated three ways. It is answered from the world, so it
  ;; is never stale; it is a lookup and a seq, which is every way upstream reads
  ;; it; and a write through it is dropped, because nothing reaches our symbol
  ;; table that way - a def arrives by being analysed, which interns a Var.
  (let [cenv  (h/fresh-env 'app.viewed)
        state (fn [] (second (macroexpand/macroexpand-1
                              cenv (env/analysis-env cenv)
                              '(upstream-compiler-state-now))))]
    ;; something to refer out of - a :refer needs the namespace analysed
    (h/analyze cenv '(ns app.source))
    (h/analyze cenv '(def blank? 1))
    (h/analyze cenv '(def join 2))
    (h/analyze cenv '(ns app.viewed
                       (:require [clojure.string :as string]
                                 [app.source :refer [blank? join]
                                  :rename {join joined}])
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [upstream-compiler-state-now]])))
    (let [nss (:cljs.analyzer/namespaces (state))]
      (testing "outside a macroexpansion it answers nothing at all"
        ;; THE VIEW IS ONLY LIVE WHILE A MACRO RUNS, for *cenv*'s own reason: it
        ;; reads whatever compile environment is bound when the lookup happens, and
        ;; that is bound around the macro call and nowhere else. So the atom can be
        ;; a constant shared by the whole compiler, and nothing that is not a macro
        ;; can read a symbol table by accident.
        (is (nil? (get nss 'app.viewed)))
        (is (empty? (keys nss))))

      ;; and bound, which is what a macro would have. Every read below is one
      ;; upstream actually makes.
      (binding [env/*cenv* cenv]
        (testing "a lookup, which is how gets reads it"
          (is (= 'app.viewed (:name (get nss 'app.viewed))))
          (is (nil? (get nss 'no.such.namespace))))

        (testing "an alias, which is the whole of what kitchen-async's fixup-alias wants"
          (is (= 'clojure.string (get-in nss ['app.viewed :requires 'string]))))

        (testing "a :refer is a use and a :rename is a rename, not a def"
          ;; The one distinction this world does not draw for itself: both are a
          ;; .refer of somebody else's Var, and what tells them apart is whether
          ;; the name it went in under is the Var's own. :defs is what the
          ;; namespace INTERNED, so neither is in it - which is also the rule that
          ;; keeps cljs.core out of every namespace's defs.
          (is (= 'app.source (get-in nss ['app.viewed :uses 'blank?])))
          (is (= 'app.source/join (get-in nss ['app.viewed :renames 'joined])))
          (is (nil? (get-in nss ['app.viewed :defs 'blank?])))
          (is (nil? (get-in nss ['app.viewed :defs 'joined]))))

        (testing "seqable, which is how cljs.analyzer.api/all-ns reads it"
          (is (contains? (set (keys nss)) 'app.viewed)))

        (testing "not stale - a def made after the view was taken is in it"
          (is (nil? (get-in nss ['app.viewed :defs 'later])))
          (h/analyze cenv '(def later 1))
          (is (= 'app.viewed/later (get-in nss ['app.viewed :defs 'later :name])))
          ;; and :defs is seqable too, which is how cljs.analyzer.api/ns-publics
          ;; reads it - sci asks a namespace what it has in it that way
          (is (contains? (set (keys (get-in nss ['app.viewed :defs]))) 'later)))

        (testing "a write is dropped rather than refused"
          (is (identical? nss (assoc nss 'app.viewed {:defs {}})))
          (is (= 'app.viewed (:name (get nss 'app.viewed)))))

        (testing "not stale through a map that is BUILT, either"
          ;; :defs alone does not test this, which is why the defeat that caches an
          ;; entry came back inert the first time. :defs is a lookup over the
          ;; Namespace object, and a Namespace is mutable - so it answers a new def
          ;; whether or not the entry around it was rebuilt. :requires is a map
          ;; built when the entry is, so it is the one that goes stale if the entry
          ;; is cached, and a REPL re-reading an ns form is how that happens.
          (is (nil? (get-in nss ['app.viewed :requires 'str2])))
          (h/analyze cenv '(ns app.viewed (:require [clojure.string :as str2])))
          (is (= 'clojure.string (get-in nss ['app.viewed :requires 'str2]))))))))

;; --- 5.58, shadow-cljs's module map ------------------------------------------

(def ^:private two-build-config
  "A shadow-cljs.edn with the shape that matters: two builds splitting one source
  tree differently, and app.editor an entry of a module in each - under a
  different name, which is the whole reason a build has to be named rather than
  guessed at.

  #shadow/env is here on purpose. shadow reads its configuration with readers for
  that tag and for #env, both of which look up environment variables;
  nosco-gamma's :main build spells its :asset-path that way. We read one vector of
  symbols out of this file, so if the tag were not got past every assertion below
  would error rather than fail."
  (str "{:builds\n"
       " {:trial {:target :browser\n"
       "          :modules {:trial {:entries [app.editor app.trial]}}}\n"
       "  :main  {:target :browser\n"
       "          :asset-path #shadow/env [\"NO_SUCH_VAR\" :default \"/js\"]\n"
       "          :modules {:base   {:entries [app.base]}\n"
       "                    :editor {:entries [app.editor] :depends-on #{:base}}}}}}\n"))

(defn- config-file
  "A configuration file holding `text`, for *shadow-cljs-edn* to be pointed at."
  ^java.io.File [text]
  (doto (java.io.File/createTempFile "shadow-cljs" ".edn")
    (.deleteOnExit)
    (spit text)))

(defmacro module-upstream-would-load
  "What shadow.lazy/module-for-ns reads, quoted:

      (get-in @env/*compiler* [:shadow.build/ns->mod ns])

  copied rather than described, because the point of the test below is that the
  lookup upstream's macro makes is the lookup this compiler answers. shadow-cljs
  is not a dependency here - the vendored suite is the oracle - so the one line of
  it that matters is spelled out instead. requiring-resolve for
  upstream-expansion-of's reason."
  [ns-sym]
  (list 'quote (get-in @@(requiring-resolve 'cljs.env/*compiler*)
                       [:shadow.build/ns->mod ns-sym])))

(deftest test-a-module-entry-names-the-module-it-is-the-entry-of
  ;; 5.58. shadow.lazy/loadable asks which output module a namespace loads with,
  ;; and throws "Could not find module for ns: X" when nothing answers - which is
  ;; not a failure of analysis but a question about a build, asked of a compiler
  ;; that is not running one. The answer is in the configuration already: a module
  ;; is named by its :entries, and an entry is the kind of namespace loadable is
  ;; given, because naming a module by its entry point is what code-splitting is.
  (binding [macroexpand/*shadow-cljs-edn* (config-file two-build-config)]
    (let [mods (macroexpand/shadow-ns->mod)]
      (is (= :editor (get mods 'app.editor)))
      (is (= :base (get mods 'app.base)))

      (testing "the build read is the one named, not whichever the file holds first"
        ;; app.editor is an entry in :trial too, under the module name :trial.
        ;; Nothing in the world this compiler holds could settle which build it is
        ;; compiling for, so the name is written down instead - macroexpand/
        ;; shadow-build, and it reads :main.
        (is (not= :trial (get mods 'app.editor))))

      (testing "a namespace that is not an entry has no answer here"
        ;; AND MUST NOT GET ONE. Which module shadow puts a non-entry in is decided
        ;; by walking the dependency graph against the module tree, which is a
        ;; build's work. Absent, module-for-ns! throws exactly what it threw
        ;; before, and the refusal sits where the knowledge runs out rather than a
        ;; step past it.
        (is (nil? (get mods 'app.some.leaf)))
        (is (nil? (get mods 'app.trial)))))))

(deftest test-the-module-map-is-read-when-it-is-asked
  ;; A VIEW, for upstream-namespaces' reason: a REPL outlives an edit to
  ;; shadow-cljs.edn, and adding a module is how a component is made lazy in the
  ;; first place. A map built when the compiler-state atom was made would go on
  ;; answering what the file used to say, for the life of the process.
  (let [f    (config-file two-build-config)
        mods (binding [macroexpand/*shadow-cljs-edn* f]
               (macroexpand/shadow-ns->mod))]
    (binding [macroexpand/*shadow-cljs-edn* f]
      (is (= :editor (get mods 'app.editor)))
      (spit f (str "{:builds {:main {:modules"
                   " {:later {:entries [app.editor]}}}}}"))
      (is (= :later (get mods 'app.editor))))))

(deftest test-no-configuration-file-answers-nothing
  ;; The file is relative, which is shadow's own rule - its load-cljs-edn is
  ;; literally (io/file "shadow-cljs.edn"), so the project directory is the one the
  ;; JVM was started in. A REPL started somewhere else has no shadow build to speak
  ;; of, and saying nothing is the truth about it.
  (binding [macroexpand/*shadow-cljs-edn* (java.io.File. "no/such/shadow-cljs.edn")]
    (is (nil? (get (macroexpand/shadow-ns->mod) 'app.editor)))))

(h/deftest-when h/cljs-analyzer? test-a-macro-reads-the-module-map-through-upstreams-atom
  ;; THE PATH THAT MATTERS. shadow.lazy's macros do not take the map from us; they
  ;; read it through cljs.env/*compiler*, the same var 5.55 bound for core.async
  ;; and 5.57 filled for sci. So the entry has to be in that atom, and the atom has
  ;; to be bound while our macroexpansion runs.
  (let [cenv (h/fresh-env 'app.lazy)]
    (h/analyze cenv '(ns app.lazy
                       (:require-macros [clojure.cljs.analyzer-test
                                         :refer [module-upstream-would-load]])))
    (binding [macroexpand/*shadow-cljs-edn* (config-file two-build-config)]
      (let [asked (fn [sym] (second (macroexpand/macroexpand-1
                                     cenv (env/analysis-env cenv)
                                     (list 'module-upstream-would-load sym))))]
        (is (= :editor (asked 'app.editor)))
        (is (nil? (asked 'app.some.leaf)))))))

(deftest test-a-macro-alias-target-is-rewritten-like-any-other-name
  ;; §5.28. (:require-macros [clojure.core :as lang]) makes lang/for the CLJS.CORE
  ;; macro. The alias itself points at the JVM clojure.core - a :refer off the same
  ;; spec still reaches clojure.core/when - but the namespace part of a qualified
  ;; symbol goes through env/macro-ns-rewrites, and an alias is resolved to a name
  ;; before that happens. cljs.analyzer/get-expander-ns does exactly this, and
  ;; cljs/ns_test.cljs is the test: clojure.core/for expands to .nth calls, which a
  ;; ClojureScript collection does not have.
  (let [cenv (h/core-env 'app.lang)]
    (h/analyze cenv '(ns app.lang (:require-macros [clojure.core :as lang])))
    (let [expanded (macroexpand/macroexpand-1
                    cenv (env/analysis-env cenv) '(lang/for [x [1 2]] x))]
      (is (str/includes? (pr-str expanded) "cljs.core"))
      (is (not (str/includes? (pr-str expanded) "clojure.lang"))))))

(deftest test-refer-macros-on-a-require-reaches-the-same-jvm-namespace
  ;; (:require [foo :refer-macros [m]]) is how a .cljs file gets at the macros
  ;; defined beside it, without a second reference form
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core
                       (:require [clojure.cljs.analyzer-test :as t
                                  :refer-macros [twice]])))
    (is (= :js (:op (h/analyze cenv '(twice 21)))))
    (is (= :js (:op (h/analyze cenv '(t/twice 21)))))))

(defn- self-macro-ns
  "A cenv where a ClojureScript namespace named clojure.cljs.analyzer-test says its
  macros live in the JVM namespace of the same name - which is this file.

  A .cljc that is both a runtime namespace and a macro namespace declares itself
  that way, and cljs/test.cljc is the one that matters: three of ClojureScript's
  test namespaces :refer deftest and is out of it with no :refer-macros anywhere."
  []
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns clojure.cljs.analyzer-test
                       (:require-macros [clojure.cljs.analyzer-test])))
    (h/analyze cenv '(def a-var 41))
    (env/set-current-ns! 'cljs.user)
    cenv))

(deftest test-a-refer-may-name-a-macro-when-the-namespace-keeps-them-beside-it
  ;; §5.17. (:require [cljs.test :refer [deftest]]) with no :refer-macros: deftest
  ;; is a macro in cljs/test.cljc and nothing at all in cljs/test.cljs, and a
  ;; namespace that keeps its macros beside it is one namespace to whoever requires
  ;; it, whichever side a name lives on.
  (let [cenv (self-macro-ns)]
    (h/analyze cenv '(ns app.core
                       (:require [clojure.cljs.analyzer-test :as t
                                  :refer [twice a-var]])))
    ;; the macro came across, bare and through the alias - the alias too, which is
    ;; the half that :refer alone would not have bought
    (is (= :js (:op (h/analyze cenv '(twice 21)))))
    (is (= :js (:op (h/analyze cenv '(t/twice 21)))))
    ;; and a name that IS a var is still a var: the split is per name, not per spec
    (is (= 'clojure.cljs.analyzer-test/a-var (:name (h/analyze cenv 'a-var))))))

(deftest test-a-refer-names-only-a-var-when-the-namespace-said-nothing
  ;; The condition is the target's own declaration, not that a JVM namespace of
  ;; that name happens to be loaded - which for a name like clojure.string is
  ;; always true, and would let a typo resolve to something nobody required.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns clojure.cljs.analyzer-test))
    (env/set-current-ns! 'cljs.user)
    (is (re-find #"does not keep its macros in a JVM namespace of its own name"
                 (h/message #(h/analyze cenv '(ns app.core
                                                (:require [clojure.cljs.analyzer-test
                                                           :refer [twice]]))))))))

(deftest test-a-refer-that-is-neither-a-var-nor-a-macro-says-both
  (let [cenv (self-macro-ns)]
    (is (re-find #"no such var there, and no such macro in .* either"
                 (h/message #(h/analyze cenv '(ns app.core
                                                (:require [clojure.cljs.analyzer-test
                                                           :refer [nope]]))))))))

(deftest test-a-refer-macro-that-is-not-a-macro-says-so
  (let [cenv (h/fresh-env 'cljs.user)]
    (is (re-find #"does not exist"
                 (h/message #(h/analyze cenv '(ns app.core
                                                (:require-macros
                                                 [clojure.cljs.analyzer-test
                                                  :refer [nope]]))))))
    (is (re-find #"is not a macro"
                 (h/message #(h/analyze cenv '(ns app.core
                                                (:require-macros
                                                 [clojure.cljs.analyzer-test
                                                  :refer [macro-env]]))))))))

(deftest test-an-ns-form-replaces-rather-than-accumulates
  ;; An ns form DECLARES what a namespace depends on. Re-analysing one - which is
  ;; what recompiling an edited file is - has to replace what the last one left,
  ;; or deleting a :require from a file leaves the require in the environment and
  ;; the emitted module goes on importing a namespace its source no longer names.
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core
                       (:require [my-lib.core :as lib :refer [helper]])
                       (:require-macros [clojure.cljs.analyzer-test :as m
                                         :refer [twice]])
                       (:refer-clojure :exclude [inc])))
    (is (= #{'my-lib.core} (env/declared-requires cenv 'app.core)))
    (is (= 'my-lib.core/helper (:name (h/analyze cenv 'helper))))
    (is (env/excluded? cenv 'app.core 'inc))
    (is (= :js (:op (h/analyze cenv '(m/twice 1)))))

    ;; the same namespace, declared again with none of it
    (h/analyze cenv '(ns app.core))
    (is (empty? (env/declared-requires cenv 'app.core)))
    (is (nil? (.lookupAlias ^Namespace (env/cljs-ns cenv 'app.core) 'lib)))
    (is (re-find #"neither a local nor a var" (h/message #(h/analyze cenv 'helper))))
    (is (not (env/excluded? cenv 'app.core 'inc)))
    ;; the alias is gone, so m is no longer a namespace at all - which is now a
    ;; warning and a JavaScript global rather than an error (§5.8)
    (is (re-find #"undeclared-ns" (h/warnings #(h/analyze cenv 'm/twice))))
    ;; a def of this namespace's own is untouched: a refer maps a var from
    ;; elsewhere, a def interns one here, and only the first kind is cleared
    (h/analyze cenv '(def mine 1))
    (h/analyze cenv '(ns app.core))
    (is (= 'app.core/mine (:name (h/analyze cenv 'mine))))))

(deftest test-a-failed-redeclaration-keeps-the-declaration-it-failed-to-replace
  ;; clearing happens where applying happens, which is after every reference has
  ;; been checked - so a typo in a new ns form does not cost the old one
  (let [cenv (two-namespaces)]
    (h/analyze cenv '(ns app.core (:require [my-lib.core :as lib])))
    (is (some? (h/message #(h/analyze cenv '(ns app.core
                                              (:require [my-lib.core :refer [nope]]))))))
    (is (= #{'my-lib.core} (env/declared-requires cenv 'app.core)))
    (is (some? (.lookupAlias ^Namespace (env/cljs-ns cenv 'app.core) 'lib)))))

;; --- try -------------------------------------------------------------------

(deftest test-the-shape-of-a-try-is-enforced
  ;; JavaScript gives one catch parameter, so several clauses become a type-test
  ;; chain over one binding - which is why the grammar has to be pinned down here
  ;; rather than discovered as odd JavaScript later.
  (let [refuse #(h/message (fn [] (h/analyze (h/fresh-env 'try.core) %)))]
    (is (re-find #"only one finally" (refuse '(try 1 (finally 1) (finally 2)))))
    (is (re-find #"catch clauses come after the body"
                 (refuse '(try 1 (finally 1) (catch :default e 2)))))
    ;; :default is not a type test - it catches everything, so anything after it
    ;; could never run
    (is (re-find #"must come last"
                 (refuse '(try 1 (catch :default e 1) (catch js/Error x 2)))))
    (is (re-find #"only one \(catch :default"
                 (refuse '(try 1 (catch :default e 1) (catch :default x 2)))))
    (is (re-find #"\(catch type name body" (refuse '(try 1 (catch :default)))))
    (is (re-find #"unqualified symbol" (refuse '(try 1 (catch :default "nope" 2)))))
    ;; and the two words that are only ever part of a try say so, rather than
    ;; sending someone to look for a var they never meant to name
    (is (re-find #"only valid inside a try" (refuse '(catch :default e 1))))
    (is (re-find #"only valid inside a try" (refuse '(finally 1))))))

(deftest test-recur-may-not-cross-a-try
  ;; JavaScript's continue cannot leave a try block, and a finally would have to
  ;; run on the way out of a jump that has no way to run it. The message is its
  ;; own, because "recur outside of a loop*" would be false - there is a loop, and
  ;; the try is what stands between.
  (let [refuse #(h/message (fn [] (h/analyze (h/fresh-env 'try.core) %)))]
    (is (re-find #"Cannot recur across a try"
                 (refuse '(loop* [x 1] (try (recur 2) (catch :default e 1))))))
    (is (re-find #"Cannot recur across a try"
                 (refuse '(loop* [x 1] (try 1 (finally (recur 2)))))))
    ;; but a loop written INSIDE the try is a recur target like any other, and
    ;; analysing this is the claim - it refuses nothing
    (is (= :loop (:op (h/analyze (h/fresh-env 'try.core)
                                 '(loop* [x 1]
                                    (try (loop* [y 1] (if (js* "false") (recur 2) y))
                                         (catch :default e 1)))))))))

;; --- the collection literals -------------------------------------------------

(deftest test-a-collection-literal-has-its-elements-as-children
  ;; the split that decides which of the two kinds of node a form gets: a literal
  ;; holds EXPRESSIONS, so it has children and they are analysed
  (is (= :vector (:op (h/analyze '[1 2]))))
  (is (= :map    (:op (h/analyze '{:a 1}))))
  (is (= :set    (:op (h/analyze '#{1}))))
  (let [node (h/analyze '(let* [x 1] [x (if x 1 2)]))
        items (-> node :body :ret :items)]
    (is (= [:local :if] (mapv :op items)))
    (is (= [:items] (-> node :body :ret :children))))
  (let [node (h/analyze '(let* [x 1] {x x}))]
    (is (= [:keys :vals] (-> node :body :ret :children)))
    (is (= [:local] (mapv :op (-> node :body :ret :keys))))))

(deftest test-metadata-on-a-literal-is-part-of-the-value
  ;; doc/cljs-compiler.md §5.21. It used to be dropped: ^{:b :c} [1 2] and [1 2]
  ;; emitted byte-identical JavaScript, which is a WRONG ANSWER rather than a
  ;; missing feature - a program could write the metadata and read nil back.
  (let [node (h/analyze '^{:b :c} [1 2])]
    (is (= :with-meta (:op node)))
    (is (= [:expr :meta] (:children node)))
    (is (= :vector (-> node :expr :op)))
    ;; the metadata is a MAP LITERAL, analyzed like any other - so a value in it
    ;; is an expression and gets evaluated
    (is (= :map (-> node :meta :op))))

  (testing "the reader's own keys are not part of it"
    ;; every collection the reader reads carries :line and :column, so a naive
    ;; (meta form) would wrap EVERY literal in a map of line numbers
    (is (= :vector (:op (h/analyze '[1 2]))))
    (is (= :map (:op (h/analyze '{:a 1}))))
    (is (= :set (:op (h/analyze '#{1})))))

  (testing "maps and sets too"
    (is (= :with-meta (:op (h/analyze '^{:b :c} {:a 1}))))
    (is (= :with-meta (:op (h/analyze '^{:b :c} #{1})))))

  (testing "fn* too, which is a value like any other"
    ;; §5.30. A function is something a program hangs metadata on and reads back,
    ;; and cljs.analyzer wraps here as well (analyzer.cljc:2399)
    (is (= :fn (:op (h/analyze '(fn* ([] 1))))))
    (is (= :with-meta (:op (h/analyze '^:once (fn* ([] 1))))))
    (is (= :fn (:op (:expr (h/analyze '^:once (fn* ([] 1))))))))

  (testing "except the three keys dt->et puts on every protocol method"
    ;; ::type, ::protocol-impl and ::protocol-inline are the annotator's, not the
    ;; program's - cljs.analyzer drops them at the same point (analyzer.cljc:2359).
    ;; Without this every protocol method in cljs.core would be built by calling
    ;; with-meta, most of them before with-meta exists.
    (let [ann {:clojure.cljs.analyzer/type 'T
               :clojure.cljs.analyzer/protocol-impl true
               :clojure.cljs.analyzer/protocol-inline false}]
      (is (= :fn (:op (h/analyze (with-meta '(fn* ([] 1)) ann)))))
      ;; and only those three: a program key beside them still wraps
      (is (= :with-meta
             (:op (h/analyze (with-meta '(fn* ([] 1)) (assoc ann :b :c)))))))))

(deftest test-quoted-data-is-one-constant
  ;; and the other kind: nothing inside a quote evaluates, so there is nothing to
  ;; walk and the whole structure rides on one node
  (let [node (h/analyze '(quote [1 [2 {:a #{3}}]]))]
    (is (= :quote (:op node)))
    (is (= :const (-> node :expr :op)))
    (is (= '[1 [2 {:a #{3}}]] (-> node :expr :val)))
    (is (= [] (-> node :expr :children))))
  ;; () is a constant too, and the value it stands for is the empty list
  (let [node (h/analyze ())]
    (is (= :const (:op node)))
    (is (= () (:val node)))))

(deftest test-a-vouched-for-name-is-not-checked
  ;; ::ana/no-resolve is cljs.analyzer's metadata and cljs.analyzer's purpose for
  ;; it: a macro writing a reference to a var it can see from where it was
  ;; DEFINED, expanding somewhere that var is not visible yet. core.cljc tags two
  ;; sites with it - cljs.core/IndexedSeq in the variadic-defn shim and
  ;; cljs.core/str_ in the str macro - and honouring the tag is what closed nine
  ;; of core.cljs's last ten forms (doc/cljs-compiler.md §5.9).
  (let [cenv (h/fresh-env 'app.core)]
    ;; the namespace resolves (§5.9's naming half) and the var does not exist
    (is (re-find #"No such var: cljs.core/nope"
                 (h/message #(h/analyze cenv 'cljs.core/nope))))
    (let [node (h/analyze cenv (with-meta 'cljs.core/nope
                                 {:clojure.cljs.analyzer/no-resolve true}))]
      (is (= :var (:op node)))
      (is (= 'cljs.core/nope (:name node)))
      (is (= 'cljs.core (:ns node)))))

  (testing "narrow on purpose - an unknown NAMESPACE is a different question"
    ;; a ClojureScript namespace that EXISTS in the world and that this one has not
    ;; required cannot fall through to the host - a var of ours is a property of a
    ;; namespace object nobody bound until the require puts it in the imports - and
    ;; a tag on the var does not change that. What is missing is the require.
    (let [cenv (h/fresh-env 'app.other)]
      (h/analyze cenv '(def x 1))
      (env/set-current-ns! 'app.core)
      (is (re-find #"No such namespace: app.other"
                   (h/message #(h/analyze cenv (with-meta 'app.other/x
                                                 {:clojure.cljs.analyzer/no-resolve true}))))))))

(deftest test-a-js-value-keeps-its-keys-unanalysed
  ;; The one literal the AST oracle cannot ask about: #js arrives wrapped in
  ;; clojure.cljs.reader/JSValue, a class cljs.analyzer has never heard of, so it
  ;; sees an unknown record and answers :const. The shapes below are copied from
  ;; cljs.analyzer/analyze-js-value, and this is where they are pinned.
  (let [array (h/analyze (clojure.cljs.reader/->JSValue [1 2]))]
    (is (= :js-array (:op array)))
    (is (= [:items] (:children array)))
    (is (= [:const :const] (mapv :op (:items array)))))
  (let [object (h/analyze (clojure.cljs.reader/->JSValue {:a 1 :b 2}))]
    (is (= :js-object (:op object)))
    ;; only the values are code: a key is a JavaScript property name, so it is
    ;; carried across as it was written and never analysed
    (is (= [:vals] (:children object)))
    (is (= [:a :b] (:keys object)))
    (is (= [:const :const] (mapv :op (:vals object))))))

(deftest test-a-qualified-method-is-a-host-member-as-a-value
  ;; Clojure 1.12's syntax, adopted by ClojureScript 1.12: String/.toUpperCase is
  ;; the instance method as a VALUE, and Object/new is the constructor as one.
  ;; That is what they add over (.toUpperCase s) and (new Object), which are calls
  ;; and cannot be passed to map.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core (:refer-global :only [Object String])))
    (let [node (h/analyze cenv 'String/.toUpperCase)]
      (is (= :qualified-method (:op node)))
      (is (= :method (:kind node)))
      (is (= 'toUpperCase (:method node)))
      ;; the class is analysed as an ordinary value, so :refer-global names one
      (is (= :js-var (:op (:class node))))
      (is (= 'js/String (:name (:class node)))))
    (let [node (h/analyze cenv 'Object/new)]
      (is (= :qualified-method (:op node)))
      (is (= :new (:kind node)))
      (is (nil? (:method node)))
      (is (= 'js/Object (:name (:class node)))))

    (testing "ONE reading in every position - a call is a call of that closure"
      ;; not rewritten to a host call, which stock ClojureScript also declines to
      ;; do: the whole point of the form is that it means the same thing wherever
      ;; it appears
      (let [node (h/analyze cenv '(String/.toUpperCase "foo"))]
        (is (= :invoke (:op node)))
        (is (= :qualified-method (:op (:fn node)))))))

  (testing "only the two spellings - a static method needs nothing new"
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core (:refer-global :only [String])))
      ;; String/fromCharCode is already a name in an object (§5.8)
      (is (= :js-var (:op (h/analyze cenv 'String/fromCharCode))))))

  (testing "a required namespace is a namespace, not a class"
    (let [cenv (h/fresh-env 'app.other)]
      (h/analyze cenv '(def new 1))
      (env/set-current-ns! 'cljs.user)
      (h/analyze cenv '(ns app.core (:require [app.other])))
      ;; app.other resolves, so app.other/new is the var and not a constructor
      (is (= :var (:op (h/analyze cenv 'app.other/new))))))

  (testing "a goog prefix is a class, and stays one on the second mention"
    ;; require-goog! makes a provide resolvable the moment it is named, so without
    ;; the goog case in analyze-qualified-symbol the second occurrence in a file
    ;; would take a different branch from the first. Neither reading is lost: a
    ;; goog var called `new` or `.append` is unreachable anyway.
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.core))
      (is (= :new (:kind (h/analyze cenv 'goog.string.StringBuffer/new))))
      (is (= :method (:kind (h/analyze cenv 'goog.string.StringBuffer/.append))))
      (is (= :goog-ns (:op (:class (h/analyze cenv 'goog.string.StringBuffer/new)))))
      ;; and naming it was the require
      (is (contains? (env/requires cenv 'app.core) 'goog.string.StringBuffer))))

  (testing "the class has to be a type this namespace can name"
    ;; where the fork is stricter than ClojureScript, which warns and emits
    ;; `Object` anyway. The message hands back the line to write.
    (let [cenv (h/fresh-env 'app.core)
          msg  (h/message #(h/analyze cenv 'Object/new))]
      (is (re-find #"Object/new names a member of Object" msg))
      (is (re-find #":refer-global :only \[Object\]" msg)))))

(deftest test-as-alias-requires-nothing
  ;; [made.up.lib :as-alias lib] registers an alias and REQUIRES NOTHING: the
  ;; namespace need not exist, is not compiled, and gets no import. The alias is
  ;; there so ::lib/foo and `lib/foo have a name to expand to.
  (let [cenv (h/fresh-env 'cljs.user)]
    (h/analyze cenv '(ns app.core (:require [made.up.lib :as-alias lib])))
    (is (not (contains? (env/requires cenv 'app.core) 'made.up.lib)))
    ;; the alias resolves - which is the whole point
    (is (= 'made.up.lib (.getName ^clojure.lang.Namespace
                                 (.lookupAlias ^clojure.lang.Namespace
                                               (env/cljs-ns cenv 'app.core) 'lib)))))

  (testing "and a driver does not go looking for a file for it"
    (is (= '[] (ana/ns-form-deps '(ns app.core (:require [made.up.lib :as-alias lib])))))
    ;; anything else beside it and the namespace IS used, so it is a dependency
    (is (= '[made.up.lib]
           (ana/ns-form-deps '(ns app.core (:require [made.up.lib :as-alias lib
                                                      :refer [x]]))))))

  (testing ":as-alias must be a simple symbol, and :use has no such option"
    (is (re-find #"must be a simple symbol"
                 (h/message #(h/analyze (h/fresh-env 'cljs.user)
                                        '(ns app.core (:require [a.b :as-alias "x"]))))))
    (is (re-find #"Unsupported option :as-alias"
                 (h/message #(h/analyze (h/fresh-env 'cljs.user)
                                        '(ns app.core (:use [a.b :as-alias c :only [d]]))))))))

(deftest test-a-compiled-namespace-is-its-own-require
  ;; require-goog!'s rule (doc/cljs-compiler.md §5.18) reaching the other half of
  ;; the world. What needs it is a MACRO: cljs/pprint.cljc expands to
  ;; clojure.string/split-lines and lands in whichever namespace called cl-format.
  (let [cenv (h/fresh-env 'app.other)]
    (h/analyze cenv '(ns app.other))
    (h/analyze cenv '(def x 1))
    (env/set-current-ns! 'cljs.user)
    (h/analyze cenv '(ns app.core))
    (let [node (h/analyze cenv 'app.other/x)]
      (is (= :var (:op node)))
      (is (= 'app.other/x (:name node))))
    ;; and the require is RECORDED, which is what binds it: driver/module-text
    ;; reads env/requires after the whole body is analysed
    (is (contains? (env/requires cenv 'app.core) 'app.other)))

  (testing "a name nothing at all knows is still a JavaScript global (§5.8)"
    ;; unchanged, and worth pinning beside the new rule: the two branches are
    ;; adjacent, and this one is what an actual typo hits
    (let [cenv (h/fresh-env 'app.typo)
          node (atom nil)]
      (h/analyze cenv '(ns app.typo))
      ;; through h/warnings, which is also how the undeclared-ns warning is kept
      ;; off the console
      (is (re-find #"undeclared-ns"
                   (h/warnings #(reset! node (h/analyze cenv 'app.nope/x)))))
      (is (= :js-var (:op @node)))
      (is (= 'js/app.nope.x (:name @node)))))

  (testing "and the var is still checked"
    (let [cenv (h/fresh-env 'app.other2)]
      (h/analyze cenv '(ns app.other2))
      (env/set-current-ns! 'cljs.user)
      (h/analyze cenv '(ns app.core2))
      (is (re-find #"No such var" (h/message #(h/analyze cenv 'app.other2/nope))))))

  (testing "Math/floor is untouched - asking must not create a namespace"
    ;; env/declared? used cljs-ns, which CREATES, so asking about Math left a
    ;; ClojureScript namespace called Math behind and the next branch refused it
    (let [cenv (h/fresh-env 'app.core3)]
      (h/analyze cenv '(ns app.core3))
      (is (= :js-var (:op (h/analyze cenv 'Math/floor))))
      (is (nil? (env/find-cljs-ns cenv 'Math))))))

(deftest test-a-var-may-be-the-namespace-part-of-a-qualified-symbol
  ;; §5.29. PersistentVector/EMPTY is the VAR PersistentVector and its EMPTY
  ;; property - the namespace part names a value, not a namespace.
  ;;
  ;; cljs.analyzer asks this first among the things a qualified symbol can be
  ;; (resolve-var: not an alias, no dot in the namespace part, and the namespace
  ;; part resolves as a var - then read the whole thing as the dotted symbol), and
  ;; gets the JavaScript for nothing, because a var there IS a global path.
  (let [cenv (h/core-env 'app.stat)]
    (are [form] (= :host-field (:op (h/analyze cenv form)))
      'PersistentVector/EMPTY
      'PersistentVector.EMPTY
      'cljs.core/PersistentVector.EMPTY))

  (testing "a namespace of the same name wins, because it is asked first"
    (let [cenv (h/core-env 'app.stat2)]
      (h/analyze cenv '(ns app.stat2 (:require [clojure.string :as PersistentVector])))
      ;; the alias resolves as a namespace, so this is a missing var there rather
      ;; than a property of the cljs.core type
      (is (re-find #"No such var" (h/message #(h/analyze cenv 'PersistentVector/EMPTY))))))

  (testing "a local wins over both"
    ;; read off the emitted text, which is where the difference shows: the
    ;; property comes off the PARAMETER rather than off cljs.core's type
    (let [js (h/js (h/core-env 'app.stat3)
                   "(fn* ([PersistentVector] PersistentVector/EMPTY))")]
      (is (re-find #"return PersistentVector__\d+\.EMPTY;" js) js)
      (is (not (str/includes? js "cljs$core$ns.PersistentVector")) js))))

(deftest test-a-var-carries-the-shape-of-the-function-it-holds
  ;; §5.33. :top-fn is what cljs.core's defn records about a multi-arity or
  ;; variadic function - which arities it has, and whether the last one is a rest
  ;; arity. It is already on the var, because parse-def merges the def name's
  ;; metadata onto it; what this pins is that a call site can SEE it, which is the
  ;; whole input to static arity dispatch.
  (let [cenv (h/core-env 'app.tf)]
    (h/analyze cenv '(defn two ([x] x) ([x y] y)))
    (h/analyze cenv '(defn rest-arg [a & xs] xs))
    (h/analyze cenv '(defn one [x] x))

    (testing "a multi-arity var says so, at the reference and not only in the table"
      (let [tf (:top-fn (h/analyze cenv 'two))]
        (is (false? (:variadic? tf)))
        (is (= 2 (:max-fixed-arity tf)))
        (is (= [1 2] (mapv count (:method-params tf))))))

    (testing "a variadic one says which arities are fixed and where the rest starts"
      (let [tf (:top-fn (h/analyze cenv 'rest-arg))]
        (is (true? (:variadic? tf)))
        (is (= 1 (:max-fixed-arity tf)))))

    (testing "a single-method fn has no shape - there is no arity property to name"
      (is (nil? (:top-fn (h/analyze cenv 'one)))))

    (testing "a redefinition REPLACES the shape"
      ;; the metadata is merged, so without a rule of its own the two-arity entry
      ;; would outlive the definition that set it, and every later call site would
      ;; name an arity that is no longer there
      (h/analyze cenv '(def two (fn* ([x] x))))
      (is (nil? (:top-fn (h/analyze cenv 'two)))))

    (testing "but a forward declaration does not - it is not a new shape"
      (h/analyze cenv '(defn three ([x] x) ([x y] y)))
      (h/analyze cenv '(declare three))
      (is (some? (:top-fn (h/analyze cenv 'three)))))))

(deftest test-a-compiler-flag-is-not-a-runtime-variable
  ;; §5.37. cljs.core defines *unchecked-if*, *unchecked-arrays* and
  ;; *warn-on-infer* as ordinary vars, but a set! of one is a message to the
  ;; COMPILER, answered when it is read and never emitted. ClojureScript returns
  ;; {:op :no-op} for exactly these three outside the REPL
  ;; (cljs.analyzer 1.12.145:2769), which is why their own array_access_test
  ;; asserts that cljs.core/*unchecked-arrays* is still false after a file set it.
  ;;
  ;; cljs/core.cljs:35 sets *unchecked-arrays* at the top of cljs.core itself, so
  ;; before this the var was true at runtime in every program we compiled.
  (let [node #(h/analyze (h/core-env) %)]
    (testing "setting one of the three analyses to its value, not to a set!"
      (are [form] (= :const (:op (node form)))
        '(set! *unchecked-arrays* true)
        '(set! *unchecked-if* false)
        '(set! *warn-on-infer* true)))

    (testing "and the value is the one set!, because that is what set! returns"
      (is (= true  (:form (node '(set! *unchecked-arrays* true)))))
      (is (= false (:form (node '(set! *unchecked-if* false))))))

    (testing "only for a boolean literal - anything else is an ordinary set!"
      (is (= :set! (:op (node '(set! *unchecked-arrays* (identity true)))))))))
