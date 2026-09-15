;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "A JavaScript stack trace read back as ClojureScript.

  NO COMPILER AND NO RUNTIME HERE, which is the point of the layer: the input is a
  stack string written out by hand in the shape V8 produces, and the output
  directory is two files put there with spit - a .js that is never read and a
  .js.map built with clojure.cljs.source-map/encode. So a failure here is this
  namespace's, not a compile's.

  The end to end version - a real node stack, from a real compile, through a real
  REPL - is clojure.cljs.repl-test/test-a-stack-trace-is-read-back-as-clojurescript.
  It needs node; nothing in this file does.

  doc/cljs-compiler.md §5.45."}
  clojure.cljs.stacktrace-test
  (:require [clojure.cljs.source-map :as sm]
            [clojure.cljs.stacktrace :as st]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]))

;; --- an output directory, made by hand --------------------------------------

(def ^:private cljs-src
  "(ns demo.core)\n\n(defn boom [x]\n  (throw (js/Error. x)))\n")

(def ^:private out
  "A directory holding ns/demo/core.js and a map for it, whose generated lines 7
  and 9 come from source lines 3 and 4. Built once: nothing here writes to it."
  (delay
    (let [d (h/temp-dir)
          js (io/file d "ns" "demo" "core.js")]
      (.mkdirs (.getParentFile js))
      (spit js (str/join "\n" (repeat 10 "// a line of JavaScript")))
      (spit (io/file d "ns" "demo" "core.js.map")
            (sm/encode {:file     "core.js"
                        :positions (assoc (vec (repeat 10 nil))
                                          6 {:file "demo/core.cljs" :line 3 :column 1}
                                          8 {:file "demo/core.cljs" :line 4 :column 3})
                        :content  {"demo/core.cljs" cljs-src}}))
      d)))

(defn- at [url line col] (str "    at demo$core$boom (" url ":" line ":" col ")"))

(defn- file-url [rel] (str (.toURI (io/file @out rel))))

;; --- the frames -------------------------------------------------------------

(deftest test-the-shapes-v8-writes
  (let [fs (st/frames (str "Error: boom\n"
                           "    at foo (file:///a/b.js:9:10)\n"
                           "    at file:///a/b.js:3:4\n"
                           "    at async evaluate (file:///a/r.js:1:2)\n"
                           "    at new Thing (file:///a/b.js:5:6)\n"
                           "    at async file:///a/r.js:7:8\n"
                           "  something else entirely"))]
    (testing "the first line of a V8 stack is the message, not a frame"
      (is (= {:raw "Error: boom"} (first fs))))
    (is (= [{:name "foo"      :prefix ""       :url "file:///a/b.js" :line 9 :column 10}
            {:name nil        :prefix ""       :url "file:///a/b.js" :line 3 :column 4}
            {:name "evaluate" :prefix "async " :url "file:///a/r.js" :line 1 :column 2}
            {:name "Thing"    :prefix "new "   :url "file:///a/b.js" :line 5 :column 6}
            {:name nil        :prefix "async " :url "file:///a/r.js" :line 7 :column 8}]
           (mapv #(select-keys (merge {:name nil} %) [:name :prefix :url :line :column])
                 (subvec fs 1 6))))
    (testing "and a line that is not a frame keeps itself"
      (is (= {:raw "  something else entirely"} (peek fs))))
    (testing "the indent survives, because the shape of a stack is part of reading it"
      (is (= "    " (:indent (nth fs 1)))))))

;; --- where a frame points ---------------------------------------------------

(deftest test-the-three-spellings-of-one-file
  ;; node gives a file: URL for a module it imported, a browser gives an http: URL
  ;; for the same file served over the wire, and a //# sourceURL gives a bare
  ;; relative path (§5.42). All three are one file under the output directory.
  (let [rel  "ns/demo/core.js"
        of   (fn [url] (-> (st/symbolicate @out (at url 7 1)) first))]
    (doseq [url [(file-url rel)
                 (str "http://localhost:9000/" rel)
                 (str "https://example.test/" rel)
                 rel]]
      (is (= rel (:file (of url))) url)
      (is (= {:file "demo/core.cljs" :line 3 :column 1} (:source (of url))) url))))

(deftest test-what-is-not-ours-is-left-alone
  (doseq [url ["node:internal/process/task_queues"
               "data:application/json;base64,AAAA"
               (str (.toURI (io/file (System/getProperty "java.io.tmpdir")
                                     "somewhere-else.js")))]]
    (let [f (first (st/symbolicate @out (at url 7 1)))]
      (is (nil? (:file f)) url)
      (is (nil? (:source f)) url)))
  (testing "and neither is a path with a space in it, which is V8's `async` left on"
    (is (nil? (:file (first (st/symbolicate @out (at "async ns/demo/core.js" 7 1))))))))

(deftest test-a-file-with-no-map-still-gets-its-name-back
  ;; what a REPL input is, until doc/cljs-repl.md R2's other half: the frame names
  ;; the script, and the script has no map because the REPL does not keep the text
  ;; it read
  (let [f (first (st/symbolicate @out (at "repl/demo.core/6.js" 5 30)))]
    (is (= "repl/demo.core/6.js" (:file f)))
    (is (nil? (:source f)))))

(deftest test-a-line-the-map-does-not-reach-keeps-the-file-and-loses-the-line
  (let [f (first (st/symbolicate @out (at (file-url "ns/demo/core.js") 2 1)))]
    (is (= "ns/demo/core.js" (:file f)))
    (is (nil? (:source f)))))

;; --- how it reads ------------------------------------------------------------

(deftest test-a-stack-becomes-clojurescript
  (let [js (file-url "ns/demo/core.js")]
    (is (= (str "    at demo.core/boom (demo/core.cljs:4:3)\n"
                "    at demo.core/boom (demo/core.cljs:3:1)\n"
                "    at eval (repl/demo.core/2.js:5:30)")
           (st/trace @out
                     (str "Error: boom\n"
                          (at js 9 4) "\n"
                          (at js 7 1) "\n"
                          "    at eval (repl/demo.core/2.js:5:30)\n"
                          "    at process.processTicksAndRejections (node:internal/x:1:1)\n"
                          "    at async evaluate (" (file-url "runtime.js") ":296:39)"))))))

(deftest test-the-message-line-goes-because-the-repl-already-printed-it
  (is (not (str/includes? (st/trace @out (str "Error: boom\n" (at (file-url "ns/demo/core.js") 7 1)))
                          "Error: boom"))))

(deftest test-only-trailing-machinery-is-dropped
  ;; the word is load-bearing: a runtime frame BETWEEN two of yours is something
  ;; your code called through, and dropping it would hide the call
  (let [js (file-url "ns/demo/core.js")
        rt (str "    at Object.nativeImpl (" (file-url "runtime.js") ":81:11)")
        t  (st/trace @out (str "Error: boom\n" (at js 7 1) "\n" rt "\n" (at js 9 4)
                               "\n" rt "\n" rt))]
    (is (= ["at demo.core/boom (demo/core.cljs:3:1)"
            "at Object.nativeImpl (runtime.js:81:11)"
            "at demo.core/boom (demo/core.cljs:4:3)"]
           (mapv str/trim (str/split-lines t))))))

(deftest test-a-name-is-demunged-only-when-it-reads-as-one
  (let [js   (file-url "ns/demo/core.js")
        name (fn [nm] (-> (st/trace @out (str "Error: x\n    at " nm " (" js ":7:1)"))
                          (str/replace #" \(.*" "")
                          str/trim
                          (subs 3)))]
    (testing "the rule cljs.spec.alpha uses on the same names (§5.34)"
      (is (= "demo.core/boom" (name "demo$core$boom")))
      (is (= "my-lib.core/boom?" (name "my_lib$core$boom_QMARK_")))
      (is (= "new cljs.core/ExceptionInfo" (name "new cljs$core$ExceptionInfo"))))
    (testing "and anything that does not read as a var name is left exactly as it came"
      (doseq [nm ["eval" "process.processTicksAndRejections" "Object.nativeImpl"
                  "cljs$core$assoc.cljs$core$IFn$_invoke$arity$3"]]
        (is (= nm (name nm)))))))

(deftest test-with-no-output-directory-a-stack-is-what-it-was
  ;; a REPL with no :out-dir is a real configuration - clojure.cljs.repl/need-out-dir!
  ;; - and it has no maps to read, not a reason to fail
  (let [s (str "Error: boom\n" (at "file:///a/b.js" 1 2))]
    (is (= s (st/trace nil s)))))
