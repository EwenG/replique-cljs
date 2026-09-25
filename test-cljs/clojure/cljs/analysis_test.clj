;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The ClojureScript analysis model: var definitions and usages, filed per
  top-level form and per file, fed by the driver as it compiles."}
  clojure.cljs.analysis-test
  (:require [clojure.cljs.analysis :as an]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor (fn [f] (an/reset-model!) (f) (an/reset-model!)))

(defmacro calls-double
  "Writes a reference the source does not: the expansion names deep.util/double,
  and nothing the reader read carries that name."
  [x]
  (list 'deep.util/double x))

(def ^:private program
  ;; every position asserted below is 1-based, line and column, as the reader counts
  '{deep.util "(ns deep.util)
(def double (fn* ([x] (js* \"~{} * 2\" x))))
(deftype Box [v])"

    app.core "(ns app.core
  (:require [deep.util :as u :refer [Box]])
  (:require-macros [clojure.cljs.analysis-test :refer [calls-double]]))
(def a (u/double 1))
(def b (fn* ([] (u/double (u/double a)))))
(def c (calls-double 2))
(def d (identity (Box. 1)))"})

(defn- compile!
  "A fresh environment and output directory, with `program` compiled into them
  under the sink. Returns what a later load-file! needs."
  [sources]
  (let [src  (h/write-sources! sources)
        out  (h/temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        opts {:out-dir out :source-paths [src]}]
    (an/run-analysis #(driver/compile-namespace! cenv 'app.core opts))
    {:cenv cenv :opts opts :src src}))

(defn- lines [spans] (into #{} (map (juxt :source :line :column)) spans))

(deftest test-usages-across-files-and-definitions
  (compile! program)
  (testing "every place u/double is WRITTEN, and nowhere a macro wrote it"
    (is (= #{["app/core.cljs" 4 9] ["app/core.cljs" 5 18] ["app/core.cljs" 5 28]}
           (lines (an/find-usages 'deep.util/double))))
    (is (every? #(= 'app.core (:from-ns %)) (an/find-usages 'deep.util/double))))
  (testing "a span covers the symbol as written"
    (is (some #(= {:source "app/core.cljs" :line 4 :column 9 :end-line 4 :end-column 17
                   :from-ns 'app.core} %)
              (an/find-usages 'deep.util/double))))
  (testing "the definition is the name in the def"
    (is (= ["deep/util.cljs" 2 6] ((juxt :source :line :column)
                                   (an/definition 'deep.util/double)))))
  (testing "a deftype defines its type, and a use of it is a usage"
    (is (= ["deep/util.cljs" 3 10] ((juxt :source :line :column)
                                   (an/definition 'deep.util/Box))))
    (is (= #{["app/core.cljs" 7 19]} (lines (an/find-usages 'deep.util/Box)))))
  (testing "a local var used in its own file"
    (is (= #{["app/core.cljs" 5 37]} (lines (an/find-usages 'app.core/a)))))
  (testing "Var or symbol"
    (let [v (.findInternedVar (env/find-cljs-ns (:cenv (compile! program)) 'deep.util)
                              'double)]
      (is (= (an/find-usages 'deep.util/double) (an/find-usages v))))))

(deftest test-files-and-namespaces
  (compile! program)
  (is (= #{'app.core} (an/file-namespaces "app/core.cljs")))
  (is (= #{'deep.util} (an/file-namespaces "deep/util.cljs")))
  (is (= (an/file-forms "app/core.cljs") (an/ns-forms 'app.core)))
  (testing "cljs.core is compiled and not analysed - but a use of it is recorded"
    (is (empty? (an/file-forms "cljs/core.cljs")))
    (is (nil? (an/definition 'cljs.core/identity)))
    (is (= #{["app/core.cljs" 7 9]} (lines (an/find-usages 'cljs.core/identity))))))

(deftest test-no-sink-no-model
  (let [src (h/write-sources! program)]
    (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'app.core
                               {:out-dir (h/temp-dir) :source-paths [src]})
    (is (empty? (:forms (an/snapshot))))))

(deftest test-reloading-a-file-replaces-its-forms-and-only-its
  (let [{:keys [cenv opts src]} (compile! program)
        f (io/file src "app/core.cljs")]
    (spit f "(ns app.core (:require [deep.util :as u]))\n(def a (u/double 1))\n")
    (an/load-file! cenv (str f) opts)
    (is (= #{["app/core.cljs" 2 9]} (lines (an/find-usages 'deep.util/double))))
    (testing "a def deleted from the file is no longer defined in the model"
      (is (nil? (an/definition 'app.core/b)))
      (is (empty? (an/find-usages 'app.core/a))))
    (testing "the other file's forms are untouched"
      (is (some? (an/definition 'deep.util/double))))))

(deftest test-a-file-that-fails-keeps-what-it-had
  (let [{:keys [cenv opts src]} (compile! program)
        before (an/snapshot)
        f (io/file src "app/core.cljs")]
    (spit f "(ns app.core (:require [deep.util :as u]))\n(def a (u/double 1))\n(def z nope)\n")
    (is (thrown? Exception (an/load-file! cenv (str f) opts)))
    (is (= (:forms before) (:forms (an/snapshot))))
    (testing "and the next run starts clean"
      (spit f "(ns app.core (:require [deep.util :as u]))\n(def a (u/double 1))\n")
      (an/load-file! cenv (str f) opts)
      (is (= #{["app/core.cljs" 2 9]} (lines (an/find-usages 'deep.util/double)))))))

(deftest test-retract-file
  (compile! program)
  (an/retract-file! "app/core.cljs")
  (is (empty? (an/file-forms "app/core.cljs")))
  (is (empty? (an/find-usages 'deep.util/double)))
  (is (some? (an/definition 'deep.util/double))))
