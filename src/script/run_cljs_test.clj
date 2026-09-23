;; Runs this project's tests (test-cljs/).
;;
;; They want two things a build does not - node on PATH, and the ClojureScript jar
;; for cljs.analyzer as an AST oracle. Either one missing skips the tests that need
;; it (h/deftest-when), so neither is a build dependency.
;;
;; Run with: mvn -o test
;;
;; ONE NAMESPACE, for an edit that cannot have touched the rest:
;;
;;   mvn -o test -Dtest.ns=clojure.cljs.compat-test
;;   mvn -o test -Dtest.ns=clojure.cljs.compat-test,clojure.cljs.analyzer-test
;;
;; which is five seconds against four and a half minutes, and the difference
;; between a check that gets run and one that gets skipped. THE FULL SUITE IS THE
;; ONE THAT COUNTS - a narrow run proves only that the namespaces named still pass,
;; so it belongs in the middle of an edit and never at the end of one.
;;
;; The same names can be passed as plain arguments after this file, which is how a
;; script driving the suite directly - without Maven, which adds phases and nothing
;; else - asks for part of it.
(require
 '[clojure.string :as str]
 '[clojure.test :as test]
 '[clojure.tools.namespace.find :as ns])

(def ^:private every-namespace
  (filter #(.endsWith (name %) "-test")
          (ns/find-namespaces-in-dir (java.io.File. "test-cljs"))))

(def ^:private asked-for
  "The namespaces named on the way in, as symbols, or nil for all of them."
  (let [prop (System/getProperty "test.ns")
        named (if (str/blank? prop)
                *command-line-args*
                (str/split (str/trim prop) #"[,\s]+"))]
    (seq (map symbol (remove str/blank? named)))))

(def ^:private namespaces
  (if asked-for
    ;; A NAME THAT IS NOT THERE IS A FAILURE AND NOT AN EMPTY RUN. clojure.test
    ;; reports zero tests as a success, so a typo in a selector would otherwise
    ;; print `0 failures' and exit 0 - the one output that must never be
    ;; reachable without running anything.
    (let [known (set every-namespace)
          missing (remove known asked-for)]
      (when (seq missing)
        (binding [*out* *err*]
          (println "No such test namespace:" (str/join ", " missing))
          (println "There are" (count every-namespace) "of them, all under test-cljs/."))
        (System/exit 2))
      asked-for)
    every-namespace))

(doseq [n namespaces] (require n))

(require '[clojure.cljs.test-harness :as h])
(println)
(println "ClojureScript front end tests")
(println "  node          " (if h/node? "yes" "NO - emitter tests skipped"))
(println "  cljs.analyzer " (if h/cljs-analyzer? "yes" "NO - AST oracle skipped"))
(when asked-for
  (println "  namespaces    " (count namespaces) "of" (count every-namespace)
           "- A PARTIAL RUN"))
(println)

(let [summary (apply test/run-tests namespaces)]
  (System/exit (if (test/successful? summary) 0 -1)))
