;; Runs this project's tests (test-cljs/).
;;
;; They want two things a build does not - node on PATH, and the ClojureScript jar
;; for cljs.analyzer as an AST oracle. Either one missing skips the tests that need
;; it (h/deftest-when), so neither is a build dependency.
;;
;; Run with: mvn -o test
(require
 '[clojure.test :as test]
 '[clojure.tools.namespace.find :as ns])

(def namespaces
  (filter #(.endsWith (name %) "-test")
          (ns/find-namespaces-in-dir (java.io.File. "test-cljs"))))

(doseq [n namespaces] (require n))

(require '[clojure.cljs.test-harness :as h])
(println)
(println "ClojureScript front end tests")
(println "  node          " (if h/node? "yes" "NO - emitter tests skipped"))
(println "  cljs.analyzer " (if h/cljs-analyzer? "yes" "NO - AST oracle skipped"))
(println)

(let [summary (apply test/run-tests namespaces)]
  (System/exit (if (test/successful? summary) 0 -1)))
