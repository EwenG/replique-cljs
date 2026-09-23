;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "M6's first slice: cljs.test compiles and runs here.

  ClojureScript's own test suite is the oracle M6 wants, and cljs.test is what it
  is written in - so before a single test of theirs can run, three things have to
  exist that did not: the `var` special form, which deftest emits; the ^{:test ...}
  property, which test-var reads back; and cljs.analyzer.api, which cljs/test.cljc
  asks six questions of.

  What is NOT here is their suite. It is 744K of files with dependencies we have
  not vendored - clojure.test.check, cljs.spec.alpha, clojure.test - and vendoring
  it is its own decision. doc/cljs-compiler.md §5.14 has the first count taken
  against a checkout.

  Skipped when node is not on PATH."}
  clojure.cljs.cljs-test-test
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.analyzer-api :as api]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

;; --- the vendoring is honest -------------------------------------------------

(defn- jar-copy
  "The ClojureScript jar's own `path` - core-test's helper, needed here for the
  same reason: our copy shadows theirs on the classpath."
  [path]
  (some (fn [^java.net.URL u]
          (when (= "jar" (.getProtocol u)) (slurp u)))
        (enumeration-seq
         (.getResources (.getContextClassLoader (Thread/currentThread)) path))))

(def ^:private cljs-jar? (some? (jar-copy "cljs/test.cljc")))

(def ^:private declared-adaptations
  "Every line of the ClojureScript files we vendor that our copies no longer have.
  Each is marked ADAPTED (M6) at its site.

  Small enough to sit inline, unlike core.cljc's 183 - which is the measurement
  worth having: adapting cljs.test to this compiler costs an ns form and one
  optional reporter, and cljs.reader costs one macro body.

  cljs/reader.cljs is here with an EMPTY set on purpose. It is vendored and it is
  unmodified, and saying so is what keeps it that way: without the entry, editing
  it later would be undeclared rather than a test failure."
  {"cljs/test.cljc"
   #{"  (:require [cljs.env :as env]"
     "            [cljs.analyzer :as ana]"
     "            [cljs.analyzer.api :as ana-api]"}
   "cljs/test.cljs"
   #{"  (:require [clojure.string :as string]"
     "            [cljs.pprint :as pprint]))"
     "     (= ::pprint reporter) (assoc :reporter ::default"
     "                             :formatter pprint/pprint))))"}
   ;; add-data-readers, rewritten body (M6 5.30). Same expansion - a tag symbol
   ;; and a call to the reader the classpath registered for it - built from
   ;; clojure.cljs.reader/user-data-readers instead of from a compiler-environment
   ;; key, which is why the require of cljs.env goes with it.
   "cljs/reader.clj"
   #{"  (:require [cljs.env :as env]))"
     "(defmacro add-data-readers [default-readers]"
     "  (let [data-readers"
     "        (->> (get @env/*compiler* :cljs.analyzer/data-readers)"
     "          (map (fn [[k v]]"
     "                 `['~k (fn [x#] (~(vary-meta (-> v meta :sym) assoc :cljs.analyzer/no-resolve true) x#))]))"
     "          (into {}))]"
     "    `(do (merge ~default-readers ~data-readers))))"}
   ;; vendored and UNMODIFIED - see the docstring above for why they are listed.
   ;; cljs/instant.clj is ClojureScript's answer to a java.util.Date being Julian
   ;; before 1582 where a JavaScript Date is not (CLJS-3291); we read #inst
   ;; through it for the same reason and had to change nothing.
   "cljs/reader.cljs"  #{}
   "cljs/instant.clj"  #{}
   ;; cljs/tagged_literals.cljc is vendored too and is NOT in this map, because
   ;; it is not on this classpath: it lives in src/compat, where a second copy of
   ;; its JSValue cannot exist beside the jar's (doc/cljs-compiler.md 5.68).
   ;; clojure.cljs.compat-test byte-compares it from disk instead.

   ;; --- cljs.spec.alpha and its two companions (M6) ---------------------------
   ;;
   ;; Only the MACRO halves are vendored, plus one runtime file. cljs/spec/alpha.cljs
   ;; is 54KB and needs nothing: it is ordinary ClojureScript and comes off the jar
   ;; unchanged, as clojure.string and clojure.set do. What had to be adapted is the
   ;; part that runs on the JVM and asks this compiler questions - see
   ;; clojure.cljs.analyzer-api, which is where the answers now come from.
   "cljs/spec/alpha.cljc"
   #{"            [cljs.analyzer :as ana]"
     "            [cljs.analyzer.api :refer [resolve]]"
     "            [cljs.env :as env]"
     ;; res, whose :cljs branch strips a $macros suffix this fork never makes
     "    (symbol? form) #?(:clj  (clojure.core/or (->> form (resolve env) ->sym) form)"
     "                      :cljs (let [resolved (clojure.core/or (->> form (resolve env) ->sym) form)"
     "                                  ns-name (namespace resolved)]"
     "                              (symbol"
     "                                (if (clojure.core/and ns-name (str/ends-with? ns-name \"$macros\"))"
     "                                  (subs ns-name 0 (- (count ns-name) 7))"
     "                                  ns-name)"
     "                                (name resolved))))"
     ;; ns-qualify
     "    (->sym (binding [ana/*private-var-access-nowarn* true]"
     "             (ana/resolve-var env s)))"
     "    (symbol (str ana/*cljs-ns*) (str s))))"
     ;; init-compile-asserts: :elide-asserts is a compiler option this fork has no
     ;; map to read
     "  (let [compile-asserts (not (-> env/*compiler* deref :options :elide-asserts))]"
     "    compile-asserts))"}

   ;; one line: dynaload's reference to the var exists? just found
   "cljs/spec/gen/alpha.cljc"
   #{"         ~(vary-meta s assoc :cljs.analyzer/no-resolve true)"}

   "cljs/spec/test/alpha.cljc"
   #{"    [cljs.analyzer :as ana]"
     "    [cljs.analyzer.api :as ana-api]"
     ;; with-instrument-disabled read the namespace as a JavaScript GLOBAL. Their
     ;; note about why goes with it - the adapted site quotes it back.
     "  ;; Note: In order to read the value of this private var, we employ interop"
     "  ;; rather than derefing a var special. This eases specing core functions"
     "  ;; (and infinite recursion) by avoiding code generated by the var special,"
     "  ;; and also produces more compact / efficient code."
     "  `(let [orig# (.-*instrument-enabled* js/cljs.spec.test.alpha)]"}

   ;; the one RUNTIME file that needed anything, and it needed one branch:
   ;; goog.userAgent.product is 11 files of user-agent sniffing for four booleans,
   ;; and under :target :nodejs the branch that reads them is unreachable
   ;; --- cljs.repl, the RUNTIME half only (M6) ---------------------------------
   ;;
   ;; One line. cljs/repl.cljc is the whole JVM-side REPL and is not vendored;
   ;; nothing in repl.cljs calls a macro of its own, so the require of it goes.
   "cljs/repl.cljs"
   #{"  (:require-macros cljs.repl)"}

   "cljs/spec/test/alpha.cljs"
   #{"    [goog.userAgent.product :as product]"
     "      product/SAFARI :safari"
     "      product/CHROME :chrome"
     "      product/FIREFOX :firefox"
     "      product/IE :ie)))"}})

(h/deftest-when cljs-jar? test-vendored-files-are-adapted-only-where-declared
  ;; core-test's property, for the second file we had to edit: what is missing from
  ;; our copy is exactly what we said would be missing, and no more.
  (doseq [[path declared] declared-adaptations]
    (testing path
      (let [theirs (set (str/split-lines (jar-copy path)))
            ours   (set (str/split-lines (slurp (io/resource path))))
            gone   (into (sorted-set) (remove ours) theirs)]
        (is (= declared gone)
            (str path ": the adaptation and the declaration disagree"))))))

(h/deftest-when cljs-jar? test-the-ones-declared-verbatim-are-byte-for-byte
  ;; THE SET DIFFERENCE ABOVE ONLY SEES LINES THAT WENT. An entry declared #{} is
  ;; a claim that the file is untouched, and adding a line to it - a comment, a
  ;; def, a whole function - satisfies that test without being true. Byte equality
  ;; is the assertion those entries were always making, so it is the one they get,
  ;; and the list stays derived from the map rather than written twice.
  (doseq [[path declared] declared-adaptations
          :when (empty? declared)]
    (testing path
      (is (= (jar-copy path) (slurp (io/resource path)))))))

(h/deftest-when cljs-jar? test-clojure-string-and-set-are-vendored-unmodified
  ;; cljs.test's runtime requires clojure.string, and half of ClojureScript's test
  ;; suite requires both. Neither needed a line changed - unlike core.cljc and
  ;; unlike cljs.test itself - so byte equality is the right assertion here, as it
  ;; is for the nine goog files.
  (doseq [path ["clojure/string.cljs" "clojure/set.cljs"]]
    (testing path
      (is (= (jar-copy path) (slurp (io/resource path)))))))

(h/deftest-when cljs-jar? test-our-cljs-test-is-the-one-that-loads
  (is (not= "jar" (.getProtocol (io/resource "cljs/test.cljc")))))

;; --- what deftest needs: the var special form --------------------------------

(h/deftest-when h/node? test-a-var-is-a-value
  ;; (var foo) is cljs.core/Var, built from a thunk, a symbol and a metadata map -
  ;; and every one of those three is something M5 delivered, which is why §4.1
  ;; could list `var` as outstanding and §5.6 could find it unblocked without
  ;; anyone writing it.
  (is (= (str/join "\n" ["#'app.vt/foo" "42" "foo" "app.vt" "\"d\"" "([x])"])
         (h/output-with-core
          (h/core-env 'app.vt)
          "(defn foo \"d\" [x] x)
           (js/console.log (pr-str (var foo)))
           (js/console.log ((var foo) 42))
           (js/console.log (pr-str (:name (meta (var foo)))))
           (js/console.log (pr-str (:ns (meta #'foo))))
           (js/console.log (pr-str (:doc (meta #'foo))))
           (pr-str (:arglists (meta #'foo)))"))))

(h/deftest-when h/node? test-a-var-reads-the-var-not-the-value
  ;; the thunk, which is the whole reason the first argument is a function: a Var
  ;; taken before a redefinition still answers with what the var holds NOW.
  (is (= "1\n2"
         (h/output-with-core
          (h/core-env 'app.vt2)
          "(def x 1)
           (def v (var x))
           (js/console.log (deref v))
           (def x 2)
           (deref v)"))))

(deftest test-what-var-refuses
  (let [cenv (h/core-env 'app.vt3)]
    (is (str/includes? (h/message #(h/js cenv "(var)")) "Wrong number of args"))
    (is (str/includes? (h/message #(h/js cenv "(var \"x\")")) "must be a symbol"))
    (testing "and a local is not a var, even where one of that name exists"
      ;; :locals is dropped before the symbol is resolved, so this is the VAR x -
      ;; which does not exist here, and says so rather than answering about the let
      (is (str/includes? (h/message #(h/js cenv "(let* [x 1] (var x))"))
                         "neither a local nor a var")))))

;; --- what test-var reads back: the :test property ----------------------------

(h/deftest-when h/node? test-a-def-carries-its-test
  ;; ^{:test ...} is the one piece of def metadata that reaches the OUTPUT, as a
  ;; property of the value. cljs.compiler emits it from the same key.
  ;;
  ;; The value is a FUNCTION here, and it has to be: JavaScript will not take a
  ;; property on a primitive, so (def ^{:test ...} foo 1) throws at run time. That
  ;; is ClojureScript's behaviour too and not worth guarding against, because
  ;; deftest - the only thing that writes this key - always defs a function.
  (is (= "7"
         (h/output-with-core
          (h/core-env 'app.tm)
          "(def ^{:test (fn [] 7)} foo (fn [] 1))
           ((.-cljs$lang$test foo))"))))

(h/deftest-when h/node? test-a-var-finds-the-test-through-its-metadata
  ;; the join between the two halves above, and the one cljs.test walks: deftest
  ;; puts the test on the value, and (meta (var foo)) reads it back off it.
  (is (= "7"
         (h/output-with-core
          (h/core-env 'app.tm2)
          "(def ^{:test (fn [] 7)} foo (fn [] 1))
           ((:test (meta (var foo))))"))))

(deftest test-load-tests-turns-it-off
  ;; and the analyzer and cljs.test have to agree, or a var would carry a test
  ;; nothing generated
  (let [cenv (h/core-env 'app.tm3)
        src  "(def ^{:test (fn [] 7)} foo (fn [] 1))"]
    (is (str/includes? (h/js cenv src) "cljs$lang$test"))
    (is (not (str/includes? (binding [ana/*load-tests* false] (h/js cenv src))
                            "cljs$lang$test")))))

;; --- the six questions cljs/test.cljc asks -----------------------------------

(deftest test-the-analyzer-api-answers-cljs-test
  (let [cenv (h/core-env 'app.api)]
    (h/js cenv "(def ^{:test (fn [] 1)} a 1) (def b 2)")
    (binding [env/*cenv* cenv]
      (testing "ns-interns is how cljs.test finds the tests"
        (let [m (api/ns-interns 'app.api)]
          (is (= #{'a 'b} (set (keys m))))
          (is (= ['a] (keys (filter (comp :test val) m))))
          (is (every? :line (vals m)) "and :line is how it orders them")))
      (testing "find-ns and all-ns"
        (is (some? (api/find-ns 'app.api)))
        (is (nil? (api/find-ns 'no.such.ns)))
        (is (contains? (set (api/all-ns)) 'cljs.core)))
      (testing "ns-resolve is interned-only"
        (is (= 'app.api/a (:name (api/ns-resolve 'app.api 'a))))
        (is (nil? (api/ns-resolve 'app.api 'no-such))))
      (testing "resolve ANSWERS NIL for a name that is not there"
        ;; and clojure.cljs.analyzer/resolve-var does not, deliberately. cljs.test
        ;; asks `(when (ana-api/resolve &env 'cljs-test-once-fixtures) ...)` to
        ;; decide whether a namespace has fixtures, and a synthesised name makes
        ;; every namespace look as though it does - which then emits a reference
        ;; to a var nobody defined.
        (is (some? (api/resolve nil 'a)))
        (is (nil? (api/resolve nil 'cljs-test-once-fixtures)))
        (is (some? (ana/resolve-var nil 'cljs-test-once-fixtures))
            "the analyzer's own answer, which is the one that differs"))
      (testing "get-options is empty and cljs.test defaults around it"
        (is (= {} (api/get-options)))))))

;; --- and the one sci asks ----------------------------------------------------

(deftest test-ns-publics-is-the-interns-a-sandbox-may-copy
  ;; cljs.analyzer.api's eighth name, and not one cljs.test asks for.
  ;; sci.core/copy-ns lifts a namespace into a sandbox wholesale, and the branch of
  ;; that macro which runs inside the ClojureScript compiler reads its list through
  ;; this name. nosco-gamma is the caller that found it missing:
  ;; (sci/copy-ns cljs.math (sci/create-ns 'clojure.math)), so that sandboxed
  ;; surface code can call clojure.math/round without reaching js/Math.
  (let [cenv (h/core-env 'app.pub)]
    (h/js cenv "(def a 1) (def ^:private hidden 2) (defn- f [] 3) (defn g [] 4)")
    (binding [env/*cenv* cenv]
      (is (= #{'a 'hidden 'f 'g} (set (keys (api/ns-interns 'app.pub))))
          "ns-interns is everything the namespace holds")
      (is (= #{'a 'g} (set (keys (api/ns-publics 'app.pub))))
          "and ns-publics is what another namespace may name")
      ;; BOTH SPELLINGS OF PRIVATE, because they are two macros and only one of
      ;; them is the one anybody writes by hand
      (is (nil? (get (api/ns-publics 'app.pub) 'hidden)) "^:private on a def")
      (is (nil? (get (api/ns-publics 'app.pub) 'f)) "defn-")
      ;; the var maps are the SAME maps ns-interns gives, which is what copy-ns
      ;; needs: it reads :arglists and :doc off them to rebuild the var in the
      ;; sandbox
      (is (= (select-keys (api/ns-interns 'app.pub) '[a g])
             (api/ns-publics 'app.pub)))
      ;; a namespace that is not there is empty rather than an error, as
      ;; ClojureScript's is - it merges two absent maps and gets one
      (is (= {} (api/ns-publics 'no.such.ns))))))

(deftest test-a-var-map-carries-its-metadata-twice
  ;; ClojureScript's parse-def merges sym-meta into the var map AND puts it under
  ;; :meta beside it (analyzer.cljc:2050). Both spellings therefore have readers,
  ;; and the second one is not decoration: sci.core/copy-ns walks the publics with
  ;;
  ;;     (if-let [m (:meta var)] (assoc ns-map ...) ns-map)
  ;;
  ;; so a var map with no :meta is DROPPED rather than mis-copied. Without this key
  ;; (sci/copy-ns cljs.math ...) compiled to (-copy-ns {} the-ns) - an empty
  ;; sandbox namespace, no warning, no error, and forty-five functions missing at
  ;; run time. The flat keys alone pass every other test in this file.
  (let [cenv (h/core-env 'app.twice)]
    (h/js cenv "(defn ^{:doc \"d\" :arglists '([x])} f [x] x)")
    (binding [env/*cenv* cenv]
      (let [v (get (api/ns-publics 'app.twice) 'f)]
        (is (some? (:meta v)) "the key copy-ns looks for")
        (is (= "d" (:doc v) (:doc (:meta v))) "and it holds the same metadata")
        (is (= (:line v) (:line (:meta v))))
        ;; THE NESTED COPY IS READABLE, because copy-ns quotes it into emitted
        ;; code. (meta v) holds a clojure.lang.Namespace under :ns - a real Var
        ;; always does, and upstream's :meta is a symbol's metadata and never
        ;; did - so it is spelled as a symbol here, as the flat map spells it
        (is (symbol? (:ns (:meta v))) "not a clojure.lang.Namespace")
        (is (= (:ns v) (:ns (:meta v))))
        (is (= (:meta v) (read-string (pr-str (:meta v))))
            "quotable, which is what copy-ns does with it"))))
  (testing ":test is in the flat map and not in the nested one"
    ;; cljs.test reads the flat one; the nested one is quoted into emitted code,
    ;; and a function value is not a constant anything can emit
    (let [cenv (h/core-env 'app.tested)]
      (h/js cenv "(def ^{:test (fn [] 1)} a 1)")
      (binding [env/*cenv* cenv]
        (let [v (get (api/ns-interns 'app.tested) 'a)]
          (is (some? (:test v)))
          (is (nil? (:test (:meta v)))))))))

(deftest test-the-namespace-a-macro-sees-is-the-one-being-compiled
  ;; ana/*cljs-ns*, which cljs.test's run-tests reads as a VALUE to default to the
  ;; current namespace. Bound per top-level form, because an ns form moves the
  ;; cursor during its own analysis.
  (let [cenv (env/compile-env {:ns 'cljs.user})
        seen (atom [])]
    (h/js cenv "(ns a.one)")
    (h/js cenv (do (swap! seen conj ana/*cljs-ns*) "1"))
    (is (= 'cljs.user ana/*cljs-ns*) "and unbound outside a form")))

;; --- cljs.test compiles and runs ---------------------------------------------

(h/deftest-when h/node? test-a-clojurescript-test-namespace-runs
  ;; The whole of M6's first slice in one program: cljs.test compiled from the
  ;; vendored source, a deftest expanded, its var found through ns-interns, its
  ;; test read back off the value, and the reporter printing the count. Written
  ;; here rather than taken from ClojureScript's suite because that suite is not
  ;; in this repo - see the ns docstring.
  (let [source (h/write-sources!
                (h/temp-dir)
                '{demo.core "(ns demo.core (:require [cljs.test :refer-macros [deftest is run-tests]]))
                             (deftest test-arithmetic (is (= 4 (+ 2 2))) (is (= 6 (* 2 3))))
                             (deftest test-a-failure (is (= 1 2)))
                             (run-tests 'demo.core)"})
        target (h/temp-dir)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'demo.core
                                 {:out-dir target :source-paths [source]})
      (let [{:keys [out exit]} (sh/sh "node" (.getPath (io/file target "ns/demo/core.js")))]
        (is (zero? exit) out)
        (is (str/includes? out "Ran 2 tests containing 3 assertions.") out)
        (is (str/includes? out "1 failures, 0 errors.") out)
        ;; and the failure says which assertion, which is the reporter reading
        ;; :expected and :actual out of the map `is` built
        (is (str/includes? out "expected: (= 1 2)") out))
      (finally (h/delete-tree! source) (h/delete-tree! target)))))

;; --- cljs.repl, the runtime half ---------------------------------------------

(h/deftest-when h/node? test-the-vendored-cljs-repl-runs
  ;; §5.29. cljs/repl.cljs is 206 lines vendored with one line removed - the
  ;; require of its own macro namespace, which is the whole 1,584-line JVM REPL
  ;; and which nothing in this file calls. What it needs instead is
  ;; goog.string.format, which error->str uses fifteen times.
  ;;
  ;; Through the driver, because a goog require's IMPORT is the driver's job:
  ;; without it $ns("goog.string.format") is an empty object.
  (let [source (h/write-sources!
                (h/temp-dir)
                '{demo.core "(ns demo.core (:require [cljs.repl]))
                             (js/console.log (get-in (cljs.repl/Error->map (js/TypeError.))
                                                     [:via 0 :type]))
                             (js/console.log (get-in (cljs.repl/Error->map (ex-info \"\" {}))
                                                     [:via 0 :type]))
                             (js/console.log (cljs.repl/error->str (ex-info \"boom\" {})))"})
        target (h/temp-dir)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'demo.core
                                 {:out-dir target :source-paths [source]})
      (let [{:keys [out exit]} (sh/sh "node" (.getPath (io/file target "ns/demo/core.js")))]
        (is (zero? exit) out)
        ;; the two assertions cljs/repl_test.cljs makes
        (is (str/includes? out "js/TypeError") out)
        (is (str/includes? out "cljs.core/ExceptionInfo") out)
        ;; and the half that needs goog.string.format
        (is (str/includes? out "Execution error (ExceptionInfo)") out)
        (is (str/includes? out "boom") out))
      (finally (h/delete-tree! source) (h/delete-tree! target)))))
