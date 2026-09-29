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
  (:require [clojure.analysis :as clj-analysis]
            [clojure.cljs.analysis :as an]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.repl :as repl]
            [clojure.string :as str]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor (fn [f] (an/reset-model!) (f) (an/reset-model!)))

(defmacro calls-double
  "Writes a reference the source does not: the expansion names deep.util/double,
  and nothing the reader read carries that name."
  [x]
  (list 'deep.util/double x))

(defmacro twice-double
  "Calls calls-double from its expansion - a call nobody wrote."
  [x]
  (list 'clojure.cljs.analysis-test/calls-double
        (list 'clojure.cljs.analysis-test/calls-double x)))

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

(defn- calls
  "`spans' without the ones an ns form's clause wrote - the call sites alone. What
  a :refer names is in find-usages beside them, and a test about where a name is
  CALLED has to say which of the two it means."
  [spans]
  (remove :declaration spans))

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
    (is (= #{["app/core.cljs" 7 19]} (lines (calls (an/find-usages 'deep.util/Box))))))
  (testing "a local var used in its own file"
    (is (= #{["app/core.cljs" 5 37]} (lines (an/find-usages 'app.core/a)))))
  (testing "Var or symbol"
    (let [v (.findInternedVar (env/find-cljs-ns (:cenv (compile! program)) 'deep.util)
                              'double)]
      (is (= (an/find-usages 'deep.util/double) (an/find-usages v))))))

(def ^:private declares-program
  '{deep.util "(ns deep.util)
(def twice (fn* ([x] x)))
(def thrice (fn* ([x] x)))
(def renamed (fn* ([x] x)))
(def double (fn* ([x] x)))"

    app.core "(ns app.core
  (:require [deep.util :as u :refer [twice thrice renamed]
                       :rename {renamed local-name}])
  (:require-macros [clojure.cljs.analysis-test :refer [calls-double]]))
(def a (twice 1))
(def b (calls-double 2))"})

(deftest test-what-the-ns-form-writes-is-a-place
  (let [{:keys [cenv]} (compile! declares-program)
        declared (fn [spans]
                   (into #{} (comp (filter :declaration)
                                   (map (juxt :line :column :declaration)))
                         spans))]
    (testing "a :refer is where the name is written without being used - what
    makes the short name mean that var, and what a rename has to rewrite along
    with the call sites - so it is in the list, marked"
      (is (= #{[2 38 :refer]} (declared (an/find-usages 'deep.util/twice))))
      (is (= #{["app/core.cljs" 5 9]}
             (lines (calls (an/find-usages 'deep.util/twice))))))
    (testing "a name referred and never called has the one place and no other"
      (is (= #{[2 44 :refer]} (declared (an/find-usages 'deep.util/thrice))))
      (is (empty? (calls (an/find-usages 'deep.util/thrice)))))
    (testing "a :rename writes the name twice - in the :refer and as the key it
    replaces - and both have to be rewritten together"
      (is (= #{[2 51 :refer] [3 33 :refer]}
             (declared (an/find-usages 'deep.util/renamed)))))
    (testing "a macro's :refer is the same fact about a macro, and goes where its
    calls go"
      (is (= #{[4 56 :refer]}
             (declared (an/find-macro-usages 'clojure.cljs.analysis-test/calls-double))))
      (is (= #{["app/core.cljs" 6 9]}
             (lines (calls (an/find-macro-usages
                            'clojure.cljs.analysis-test/calls-double))))))
    (testing "and none of them is a USE, so the lints that ask what a namespace
    does not need still answer - a refer kept alive by its own :refer would be a
    refer nothing could ever report"
      (is (= '{thrice deep.util/thrice local-name deep.util/renamed}
             (an/unused-refers cenv 'app.core)))
      (is (= {} (an/unused-macro-refers cenv 'app.core))))))

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

;; --- locals ------------------------------------------------------------------

(def ^:private locals-program
  '{app.core "(ns app.core)
(def f (fn* ([x y] (let* [z x unused 1] z))))
(defn g [p & more] p)
(deftype P [a b] Object (toString [this] a))
(defn h [m] (let [{:keys [k]} m] k))
(defn t [] (try 1 (catch :default e 2)))
(def s (fn self [] (self)))
(defn h2 [m] (let [{:keys [k2]} m [v2] m] 1))"})

(defn- unused-names [] (into #{} (map (juxt :name :line)) (an/unused-locals)))

(deftest test-unused-locals
  (compile! locals-program)
  (is (= '#{[y 2] [unused 2] [more 3] [b 4] [this 4] [e 6] [k2 8] [v2 8]}
         (unused-names)))
  (testing "a destructured name is a binding the source wrote"
    (is (some #(= '[k2 8 28] ((juxt :name :line :column) %)) (an/unused-locals))))
  (testing "a site carries its name, namespace and span"
    (is (some #(= '{:source "app/core.cljs" :line 2 :column 31 :end-line 2 :end-column 37
                    :ns app.core :name unused} %)
              (an/unused-locals 'app.core))))
  (testing "restricted to a namespace"
    (is (empty? (an/unused-locals 'deep.util)))))

(deftest test-local-uses
  (compile! locals-program)
  (let [locals (vals (:locals (an/snapshot)))
        by     (fn [nm line] (filter #(and (= nm (:name %)) (= line (:line %))) locals))]
    (testing "a use points at the symbol that used it"
      (is (= #{{:source "app/core.cljs" :line 2 :column 29 :end-line 2 :end-column 30
                :ns 'app.core}}
             (:uses (first (by 'x 2))))))
    (testing "a deftype field read in a method is a use of the field"
      ;; two bindings are written at a's site - the field, and the parameter of
      ;; the ->P factory the macro generates - and only the field is read
      (is (= #{["app/core.cljs" 4 42]} (lines (mapcat :uses (by 'a 4))))))
    (testing "the def's own name is not a local"
      (is (empty? (by 'f 2))))))

(deftest test-reloading-replaces-locals
  (let [{:keys [cenv opts src]} (compile! locals-program)
        f (io/file src "app/core.cljs")]
    (spit f "(ns app.core)\n(def f (fn* ([q] 1)))\n")
    (an/load-file! cenv (str f) opts)
    (is (= '#{[q 2]} (unused-names)))))

;; --- keywords ----------------------------------------------------------------

(def ^:private keywords-program
  '{deep.util "(ns deep.util)"
    app.core  "(ns app.core (:require [deep.util :as u]))
(def k1 :plain)
(def k2 ::mine)
(def k3 ::u/theirs)
(def k4 {:plain [:app.core/mine]})
#_(def k5 :discarded [#_:nested])
(def k6 #?(:clj :jvm-only :cljs :cljs-only))"})

(deftest test-keyword-usages
  (compile! keywords-program)
  (is (= #{["app/core.cljs" 2 9] ["app/core.cljs" 5 10]}
         (lines (an/find-keyword-usages :plain))))
  (testing "an auto-resolved keyword is found by its full name, and so is it written out"
    (is (= #{["app/core.cljs" 3 9] ["app/core.cljs" 5 18]}
           (lines (an/find-keyword-usages :app.core/mine))))
    (is (= #{["app/core.cljs" 4 9]} (lines (an/find-keyword-usages :deep.util/theirs)))))
  (testing "a span covers the keyword as written, attributed to the namespace it is in"
    (is (= #{{:source "app/core.cljs" :line 4 :column 9 :end-line 4 :end-column 19
              :from-ns 'app.core}}
           (an/find-keyword-usages :deep.util/theirs))))
  (testing "the branch of a reader conditional ClojureScript does not take is not recorded"
    (is (= #{["app/core.cljs" 7 33]} (lines (an/find-keyword-usages :cljs-only))))
    (is (empty? (an/find-keyword-usages :jvm-only))))
  (testing "a #_ discard is: it is still written in the file, top level or nested"
    (is (= #{["app/core.cljs" 6 11]} (lines (an/find-keyword-usages :discarded))))
    (is (= #{["app/core.cljs" 6 25]} (lines (an/find-keyword-usages :nested))))))

(deftest test-reloading-replaces-keywords
  (let [{:keys [cenv opts src]} (compile! keywords-program)
        f (io/file src "app/core.cljs")]
    (spit f "(ns app.core)\n(def k1 :other)\n")
    (an/load-file! cenv (str f) opts)
    (is (empty? (an/find-keyword-usages :plain)))
    (is (= #{["app/core.cljs" 2 9]} (lines (an/find-keyword-usages :other))))))

(deftest test-a-clojure-sink-hears-no-clojurescript-keywords
  ;; Clojure's analysis binds Compiler/ANALYSIS_SINK around a whole load, and the
  ;; reader reports keywords to it - a ClojureScript compile inside one must not
  (let [heard (atom [])
        sink  (reify clojure.lang.IAnalysisSink
                (beginFile [_ _]) (endFile [_ _]) (beginForm [_ _ _ _])
                (formStart [_ _ _]) (endForm [_])
                (varUsage [_ _ _ _ _ _ _ _]) (varDef [_ _ _ _ _ _ _])
                (localDef [_ _ _ _ _ _ _ _ _]) (localUsage [_ _ _ _ _ _ _ _])
                (classUsage [_ _ _ _ _ _ _ _]) (macroExpansion [_ _ _ _ _ _ _ _ _])
                (keywordUsage [_ kw _ _ _ _ _ _] (swap! heard conj kw)))]
    (with-bindings {clojure.lang.Compiler/ANALYSIS_SINK sink}
      (compile! keywords-program))
    (is (not-any? #{:plain :app.core/mine} @heard))
    (testing "and the ClojureScript model still hears them"
      (is (seq (an/find-keyword-usages :plain))))))

;; --- macros --------------------------------------------------------------------

(def ^:private macros-program
  '{deep.util "(ns deep.util)
(def double (fn* ([x] (js* \"~{} * 2\" x))))"
    app.core  "(ns app.core
  (:require [deep.util])
  (:require-macros [clojure.cljs.analysis-test :refer [calls-double twice-double]]))
(def a (calls-double 1))
(def b (twice-double 2))
(def c (str 1))
(def d (map str [1]))"})

(deftest test-macro-usages
  (compile! macros-program)
  (testing "a call the source wrote"
    (is (= #{{:source "app/core.cljs" :line 4 :column 9 :end-line 4 :end-column 21
              :from-ns 'app.core}}
           (set (calls (an/find-macro-usages 'clojure.cljs.analysis-test/calls-double)))))
    (is (= #{["app/core.cljs" 5 9]}
           (lines (calls (an/find-macro-usages #'twice-double))))))
  (testing "a macro and a function of one name are two things"
    (is (= #{["app/core.cljs" 6 9]} (lines (an/find-macro-usages 'cljs.core/str))))
    (is (= #{["app/core.cljs" 7 13]} (lines (an/find-usages 'cljs.core/str))))))

(deftest test-macro-deps
  (compile! macros-program)
  (testing "every macro expanded, including the ones another macro called"
    (is (every? (an/macro-deps 'app.core)
                '[clojure.cljs.analysis-test/calls-double
                  clojure.cljs.analysis-test/twice-double
                  cljs.core/str]))
    (is (contains? (an/macro-deps) 'app.core)))
  (testing "not a use, where nobody wrote the call"
    (is (= 1 (count (calls (an/find-macro-usages 'clojure.cljs.analysis-test/calls-double)))))))

(deftest test-reloading-replaces-macro-facts
  (let [{:keys [cenv opts src]} (compile! macros-program)
        f (io/file src "app/core.cljs")]
    (spit f "(ns app.core)\n(def a 1)\n")
    (an/load-file! cenv (str f) opts)
    (is (empty? (an/find-macro-usages 'clojure.cljs.analysis-test/calls-double)))
    (is (not (contains? (an/macro-deps 'app.core)
                        'clojure.cljs.analysis-test/calls-double)))))

;; --- namespace lints -----------------------------------------------------------

(def ^:private lints-program
  '{deep.util  "(ns deep.util)
(def x 1)
(def y 2)
(def double (fn* ([n] n)))"
    other.lib  "(ns other.lib)
(def z 3)"
    app.core   "(ns app.core
  (:require [deep.util :as du :refer [x y]]
            [other.lib :as ol]
            [goog.string :as gstring :refer [trimLeft trimRight]]
            [\"react\" :as React :refer [useState useEffect]]
            [\"react-dom\" :as ReactDOM])
  (:import [goog.string StringBuffer])
  (:require-macros [clojure.cljs.analysis-test :as t :refer [calls-double twice-double]]))
(def a x)
(def b (gstring/trim \" a \"))
(def c (trimRight \" a \"))
(def d (React/createElement \"div\"))
(def e (useState 1))
(def f (calls-double 1))
(def g ::du/k)"})

(defn- compile-lints! []
  (let [src  (h/write-sources! lints-program)
        cenv (env/compile-env {:ns 'cljs.user})]
    (an/run-analysis #(driver/compile-namespace! cenv 'app.core
                                                 {:out-dir (h/temp-dir) :source-paths [src]
                                                  :npm {:build false}}))
    cenv))

(deftest test-namespace-lints
  (let [cenv (compile-lints!)]
    (testing "an alias whose namespace nothing is used from; a JS alias never written"
      (is (= '{ol other.lib ReactDOM "react-dom"} (an/unused-aliases cenv 'app.core))))
    (testing "a referred var, Closure name or JS export the source never uses"
      (is (= '{y deep.util/y trimLeft goog.string/trimLeft useEffect ["react" "useEffect"]}
             (an/unused-refers cenv 'app.core))))
    (testing "an :import never named"
      (is (= '{StringBuffer goog.string.StringBuffer} (an/unused-imports cenv 'app.core))))
    (testing "macros: an alias nothing is called through counts as used when its
              namespace is called by any name, as for a ClojureScript alias"
      (is (= {} (an/unused-macro-aliases cenv 'app.core)))
      (is (= '{twice-double clojure.cljs.analysis-test/twice-double}
             (an/unused-macro-refers cenv 'app.core))))
    (testing "what the namespace refers to"
      (is (every? (an/ns-referenced-namespaces 'app.core)
                  '[deep.util goog.string clojure.cljs.analysis-test])))
    (testing "host references"
      (is (= #{["app/core.cljs" 12 9]}
             (lines (an/find-host-usages {:kind :js-module :specifier "react" :export "createElement"}))))
      (is (= 2 (count (calls (an/find-host-usages {:kind :js-module :specifier "react"})))))
      (is (= #{["app/core.cljs" 11 9]}
             (lines (calls (an/find-host-usages {:kind :goog-var :name 'goog.string/trimRight}))))))
    (testing "and what the ns form writes of the host's, which is a place a rename
              has to rewrite and is not a use: a :refer of a module's export and of
              a Closure var, and the class an :import names"
      (is (= #{["app/core.cljs" 5 40 :refer] ["app/core.cljs" 5 49 :refer]}
             (into #{} (map (juxt :source :line :column :declaration))
                   (filter :declaration (an/find-host-usages {:kind :js-module
                                                              :specifier "react"})))))
      (is (= #{["app/core.cljs" 4 55 :refer] ["app/core.cljs" 11 9 nil]}
             (into #{} (map (juxt :source :line :column :declaration))
                   (an/find-host-usages {:kind :goog-var :name 'goog.string/trimRight}))))
      (is (= #{["app/core.cljs" 7 25 :import]}
             (into #{} (map (juxt :source :line :column :declaration))
                   (an/find-host-usages {:kind :goog-ns :name 'goog.string.StringBuffer})))))
    (testing "host references by ref, for what a partial match cannot ask: every
              var of one Closure namespace, each under the ref it is filed as"
      (let [found (an/find-host-usages-where
                   #(and (= :goog-var (:kind %)) (= "goog.string" (namespace (:name %)))))]
        ;; the model is the whole process's, so other programs' uses are in it
        (is (every? #(= "goog.string" (namespace (:name %))) (keys found)))
        (is (= #{["app/core.cljs" 11 9]}
               (lines (calls (mapcat (fn [[k spans]]
                                       (when (= 'goog.string/trimRight (:name k)) spans))
                                     found)))))))))

;; --- staleness -------------------------------------------------------------------

(def ^:private clock (atom 0))

(defn- touch!
  "Write `text` to `f` with an mtime no earlier write in this run can share - an
  edit within the filesystem's mtime resolution would otherwise go unnoticed."
  [^java.io.File f text]
  (spit f text)
  (.setLastModified f (+ (System/currentTimeMillis) (* 10000 (swap! clock inc)))))

(defn- with-classpath-dir
  "(f) with `dir` on the classpath: the thread's context loader is where
  io/resource looks, so a macro file written there can be loaded, and
  edited, and loaded again."
  [^java.io.File dir f]
  (let [t   (Thread/currentThread)
        old (.getContextClassLoader t)
        cl  (doto (clojure.lang.DynamicClassLoader. old) (.addURL (.toURL (.toURI dir))))]
    (.setContextClassLoader t cl)
    ;; and Compiler/LOADER, which is what RT.load asks first while it is bound -
    ;; and it is, inside any load, this test namespace's included
    (try (with-bindings {clojure.lang.Compiler/LOADER cl} (f))
         (finally (.setContextClassLoader t old)))))

(deftest test-what-has-been-compiled-is-a-question-of-its-own
  (testing "a model with nothing in it has compiled nothing, which is not the
            same fact as nothing having changed - one answer apart, and
            opposite meanings"
    (is (empty? (an/analysed-files)))
    (is (empty? (an/changed-files))))
  (compile! program)
  (is (= #{"app/core.cljs" "deep/util.cljs"} (an/analysed-files)))
  (testing "cljs.core is compiled and not analysed, so it is not in here either"
    (is (not (contains? (an/analysed-files) "cljs/core.cljs"))))
  (testing "and a file retracted is one it has not compiled"
    (an/retract-file! "app/core.cljs")
    (is (= #{"deep/util.cljs"} (an/analysed-files)))))

(deftest test-an-edited-file-is-stale-and-reloads
  (let [{:keys [cenv opts src]} (compile! program)
        f (io/file src "deep/util.cljs")]
    (is (empty? (an/stale-files)))
    (touch! f "(ns deep.util)\n(def double (fn* ([x] x)))\n(deftype Box [v])\n(def extra double)\n")
    (is (= #{"deep/util.cljs"} (an/changed-files) (an/stale-files)))
    (testing "not app.core, which uses it: a var is looked up at run time"
      (is (not (contains? (an/stale-files) "app/core.cljs"))))
    (let [r (an/stale-reload! cenv opts)]
      (is (= ["deep/util.cljs"] (:reloaded r)))
      (is (= '[deep.util] (mapv first (:scripts r)))))
    (is (empty? (an/stale-files)))
    (testing "the file's facts are its new ones; app.core's are its own and stay"
      (is (= #{["deep/util.cljs" 4 12] ["app/core.cljs" 4 9] ["app/core.cljs" 5 18]
               ["app/core.cljs" 5 28]}
             (lines (an/find-usages 'deep.util/double)))))))

(deftest test-a-changed-macro-makes-its-expanders-stale
  (let [cp  (h/temp-dir)
        mf  (io/file cp "stale" "macros.clj")
        _   (.mkdirs (.getParentFile mf))
        _   (touch! mf "(ns stale.macros)\n(defmacro answer [] 1)\n")]
    (with-classpath-dir cp
      (fn []
        (let [{:keys [cenv opts]}
              (compile! '{other.lib "(ns other.lib)\n(def z 3)"
                          app.core  "(ns app.core
  (:require [other.lib])
  (:require-macros [stale.macros :refer [answer]]))
(def a (answer))"})]
          (is (empty? (an/stale-files)))
          (touch! mf "(ns stale.macros)\n(defmacro answer [] 42)\n")
          (is (= #{"stale/macros.clj"} (an/stale-macro-files)))
          (testing "the file that expanded it, and only that one"
            (is (= #{"app/core.cljs"} (an/stale-files)))
            (is (empty? (an/changed-files))))
          (testing "and the macro file is the one that was EDITED, which nothing
  else here answers: changed-files is about the files this compiles, and a .clj
  is not one - so a client with only those two lists sees a stale file and no
  cause for it anywhere"
            (is (= #{"stale/macros.clj"} (an/changed-macro-files)))
            (is (= (an/changed-macro-files) (an/stale-macro-files))
                "nothing expands this one's macros in turn, so the two agree here"))
          (let [r (an/stale-reload! cenv opts)]
            (is (= ["stale/macros.clj"] (:macro-files r)))
            (is (= ["app/core.cljs"] (:reloaded r)))
            (testing "recompiled against the macro as it is now"
              (is (str/includes? (second (last (:scripts r))) "42"))))
          (is (empty? (an/stale-files)))
          (is (empty? (an/stale-macro-files))))))))

(deftest test-a-compile-against-an-unloaded-macro-edit-stays-stale
  ;; a branch switch changes the macro file; a file is recompiled (a require
  ;; :reload) before anything loads the macro file again, so it expands the old
  ;; macro - its baseline must be the version the JVM has, not the one on disk
  (let [cp  (h/temp-dir)
        mf  (io/file cp "unloaded" "macros.clj")
        _   (.mkdirs (.getParentFile mf))
        _   (touch! mf "(ns unloaded.macros)\n(defmacro answer [] 1)\n")]
    (with-classpath-dir cp
      (fn []
        (let [{:keys [cenv opts src]}
              (compile! '{app.core "(ns app.core
  (:require-macros [unloaded.macros :refer [answer]]))
(def a (answer))"})
              core (str (io/file src "app/core.cljs"))]
          (touch! mf "(ns unloaded.macros)\n(defmacro answer [] 42)\n")
          (let [r (an/load-file! cenv core opts)]
            (is (not (str/includes? (second (last (:scripts r))) "42"))
                "the JVM still has the old macro"))
          (is (= #{"unloaded/macros.clj"} (an/stale-macro-files)))
          (is (= #{"app/core.cljs"} (an/stale-files)))
          (let [r (an/stale-reload! cenv opts)]
            (is (= ["unloaded/macros.clj"] (:macro-files r)))
            (is (str/includes? (second (last (:scripts r))) "42")))
          (is (empty? (an/stale-files)))
          (is (empty? (an/stale-macro-files))))))))

(defn- clj-macro-files!
  "Write the Clojure macro files `files` ({\"res/path.clj\" text}) under `cp` and
  load them under the Clojure model, as a session running both analyses would."
  [cp files]
  (doseq [[res text] files]
    (let [f (io/file cp res)]
      (.mkdirs (.getParentFile f))
      (touch! f text)))
  (clj-analysis/run-analysis
   #(doseq [res (sort (keys files))]
      (load (str "/" (subs res 0 (- (count res) 4)))))))

(deftest test-a-clojure-edit-reloads-the-macro-files-built-on-it
  ;; hub.macros's helper expands base.macros's m1 when hub/macros.clj loads; app.core
  ;; expands only hub.macros's m2. Editing base/macros.clj alone must reload both, in
  ;; that order, and recompile app.core - which only the Clojure model can tell.
  (let [cp   (h/temp-dir)
        base "(ns base.macros)\n(defmacro m1 [] %s)\n"
        hub  "(ns hub.macros (:require [base.macros :refer [m1]]))
(defn helper [] (m1))
(defmacro m2 [] (helper))
"]
    (with-classpath-dir cp
      (fn []
        (try
          (clj-macro-files! cp {"base/macros.clj" (format base 1) "hub/macros.clj" hub})
          (let [{:keys [cenv opts]}
                (compile! '{app.core "(ns app.core
  (:require-macros [hub.macros :refer [m2]]))
(def a (m2))"})]
            (is (empty? (an/stale-files)))
            (touch! (io/file cp "base/macros.clj") (format base 42))
            (is (= #{"base/macros.clj" "hub/macros.clj"} (an/stale-macro-files)))
            (is (= #{"app/core.cljs"} (an/stale-files)))
            (let [r (an/stale-reload! cenv opts)]
              (is (= ["base/macros.clj" "hub/macros.clj"] (:macro-files r)))
              (is (str/includes? (second (last (:scripts r))) "42")))
            (is (empty? (an/stale-files)))
            (is (empty? (an/stale-macro-files))))
          (finally (clj-analysis/reset-model!)))))))

(deftest test-macro-files-reload-in-the-clojure-models-order
  ;; both edited; alphabetical order would load a.macros (which expands z.macros's
  ;; m1 at load time) first, against the old m1
  (let [cp  (h/temp-dir)
        z   "(ns z.macros)\n(defmacro m1 [] %s)\n"
        a   "(ns a.macros (:require [z.macros :refer [m1]]))
(defn helper [] (m1))
(defmacro m2 [] (helper))
;; %s
"]
    (with-classpath-dir cp
      (fn []
        (try
          (clj-macro-files! cp {"z/macros.clj" (format z 1) "a/macros.clj" (format a 1)})
          (let [{:keys [cenv opts]}
                (compile! '{app.core "(ns app.core
  (:require-macros [a.macros :refer [m2]] [z.macros :refer [m1]]))
(def a (m2))
(def b (m1))"})]
            (touch! (io/file cp "z/macros.clj") (format z 7))
            (touch! (io/file cp "a/macros.clj") (format a 2))
            (let [r (an/stale-reload! cenv opts)]
              (is (= ["z/macros.clj" "a/macros.clj"] (:macro-files r)))
              (is (str/includes? (second (last (:scripts r))) "a = (7)"))))
          (finally (clj-analysis/reset-model!)))))))

(deftest test-a-reload-that-throws-keeps-what-it-found-stale
  (let [cp   (h/temp-dir)
        base "(ns base2.macros)\n(defmacro m1 [] %s)\n"
        hub  "(ns hub2.macros (:require [base2.macros :refer [m1]]))
(defn helper [] (m1))
(defmacro m2 [] (helper))
"]
    (with-classpath-dir cp
      (fn []
        (try
          (clj-macro-files! cp {"base2/macros.clj" (format base 1) "hub2/macros.clj" hub})
          (let [{:keys [cenv opts]}
                (compile! '{app.core "(ns app.core
  (:require-macros [hub2.macros :refer [m2]]))
(def a (m2))"})]
            (touch! (io/file cp "base2/macros.clj") (format base 42))
            (touch! (io/file cp "hub2/macros.clj") (str hub "(oops\n"))
            (is (thrown? Exception (an/stale-reload! cenv opts)))
            (testing "base2 loaded and hub2 not, and nothing lost: both still to load
              - base2 once more, since the Clojure side's reload threw as a whole -
              and app.core still stale"
              (is (= #{"base2/macros.clj" "hub2/macros.clj"} (an/stale-macro-files)))
              (is (= #{"app/core.cljs"} (an/stale-files))))
            (touch! (io/file cp "hub2/macros.clj") hub)
            (let [r (an/stale-reload! cenv opts)]
              (is (= ["base2/macros.clj" "hub2/macros.clj"] (:macro-files r)))
              (is (str/includes? (second (last (:scripts r))) "42")))
            (is (empty? (an/stale-files))))
          (finally (clj-analysis/reset-model!)))))))

;; --- prune and metadata dependencies ---------------------------------------------

(defn- has-var? [cenv qsym]
  (some? (some-> (env/find-cljs-ns cenv (symbol (namespace qsym)))
                 (.findInternedVar (symbol (name qsym))))))

(def ^:private prune-program
  '{deep.util "(ns deep.util)
(def keep 1)
(def gone 2)
(def ^boolean flag? true)"
    app.core "(ns app.core
  (:require [deep.util :as u :refer [gone]]))
(def a u/keep)
(def b (if u/flag? 1 2))
(def c gone)"})

(deftest test-a-deleted-def-is-pruned-from-the-compile-env
  (let [{:keys [cenv opts src]} (compile! prune-program)
        f (io/file src "deep/util.cljs")]
    (is (has-var? cenv 'deep.util/gone))
    (touch! f "(ns deep.util)\n(def keep 1)\n(def ^boolean flag? true)\n")
    (let [err (java.io.StringWriter.)
          r   (binding [*err* err] (an/stale-reload! cenv opts :prune true))]
      (testing "a var deleted from the source is not deleted by recompiling; prune does"
        (is (= '[deep.util/gone] (:pruned r)))
        (is (not (has-var? cenv 'deep.util/gone)))
        (is (has-var? cenv 'deep.util/keep)))
      (testing "and from the namespace that referred it"
        (is (nil? (get (.getMappings (env/find-cljs-ns cenv 'app.core)) 'gone))))
      (testing "a use of it is warned about"
        (is (str/includes? (str err) "deep.util/gone")))
      (testing "the runtime is not told: no delete in what is shipped"
        (is (not-any? #(str/includes? (second %) "delete ") (:scripts r)))))))

(deftest test-no-prune-unless-asked
  (let [{:keys [cenv opts src]} (compile! prune-program)]
    (touch! (io/file src "deep/util.cljs")
            "(ns deep.util)\n(def keep 1)\n(def ^boolean flag? true)\n")
    (is (= [] (:pruned (an/stale-reload! cenv opts))))
    (is (has-var? cenv 'deep.util/gone))))

(deftest test-a-deleted-macro-is-unmapped-when-its-file-reloads
  ;; the jvm half of pruning: a macro deleted from a Clojure file the Clojure model
  ;; knows is unmapped as that file loads again, so a cljs file expanding it fails
  ;; rather than expanding a body no longer written anywhere. Not in :pruned, which
  ;; is the compile environment's - this is clojure.analysis doing its own.
  (let [cp   (h/temp-dir)
        base "(ns pruned.macros)\n(defmacro kept [] 1)\n%s"]
    (with-classpath-dir cp
      (fn []
        (try
          (clj-macro-files! cp {"pruned/macros.clj"
                                (format base "(defmacro dropped [] 2)\n")})
          (let [{:keys [cenv opts]}
                (compile! '{app.core "(ns app.core
  (:require-macros [pruned.macros :refer [kept]]))
(def a (kept))"})]
            (is (some? (resolve 'pruned.macros/dropped)))
            (touch! (io/file cp "pruned/macros.clj") (format base ""))
            (is (= #{"pruned/macros.clj"} (an/stale-macro-files)))
            (let [r (an/stale-reload! cenv opts :prune true)]
              (is (= ["pruned/macros.clj"] (:macro-files r)))
              (testing "the macro the file stopped defining is gone from the namespace"
                (is (nil? (resolve 'pruned.macros/dropped))))
              (testing "and the one it still defines is not"
                (is (some? (resolve 'pruned.macros/kept))))
              (testing "and what went is not in :pruned - the compile environment
                lost nothing, the jvm did"
                (is (= [] (:pruned r))))))
          (finally (clj-analysis/reset-model!)
                   (remove-ns 'pruned.macros)))))))

(deftest test-a-macro-file-outside-the-clojure-model-keeps-its-deleted-macro
  ;; the limit of the above, and it is the model's rather than a choice: unmapping
  ;; what a file stopped defining needs a record of what it defined, and a macro file
  ;; nothing analysed has none - it is loaded again with a plain load (see
  ;; reload-macro-files!), which re-defs what is there and removes nothing.
  (let [cp   (h/temp-dir)
        mf   (io/file cp "unanalysed" "macros.clj")
        base "(ns unanalysed.macros)\n(defmacro kept [] 1)\n%s"
        _    (.mkdirs (.getParentFile mf))
        _    (touch! mf (format base "(defmacro dropped [] 2)\n"))]
    (with-classpath-dir cp
      (fn []
        (try
          (let [{:keys [cenv opts]}
                (compile! '{app.core "(ns app.core
  (:require-macros [unanalysed.macros :refer [kept]]))
(def a (kept))"})]
            (is (empty? (clj-analysis/file-forms "unanalysed/macros.clj")))
            (touch! mf (format base ""))
            (let [r (an/stale-reload! cenv opts :prune true)]
              (is (= ["unanalysed/macros.clj"] (:macro-files r)))
              (is (some? (resolve 'unanalysed.macros/dropped)))
              (is (some? (resolve 'unanalysed.macros/kept)))))
          (finally (clj-analysis/reset-model!)
                   (remove-ns 'unanalysed.macros)))))))

(deftest test-a-deleted-file-is-retracted-and-pruned
  (let [{:keys [cenv opts src]}
        (compile! '{deep.util "(ns deep.util)\n(def x 1)"
                    other.lib "(ns other.lib)\n(def y 2)"
                    app.core  "(ns app.core (:require [deep.util] [other.lib]))"})]
    (.delete (io/file src "other/lib.cljs"))
    (is (= #{"other/lib.cljs"} (an/deleted-files)))
    (is (empty? (an/stale-files)))
    (let [r (an/stale-reload! cenv opts :prune true)]
      (is (= ["other/lib.cljs"] (:deleted r)))
      (is (= '[other.lib/y] (:pruned r))))
    (is (empty? (an/file-forms "other/lib.cljs")))
    (is (empty? (an/deleted-files)))
    (is (not (has-var? cenv 'other.lib/y)))
    (is (has-var? cenv 'deep.util/x))))

(deftest test-a-deleted-namespace-is-compiled-again-when-its-file-comes-back
  ;; A BRANCH SWITCHED AWAY FROM AND BACK, which is what makes this worth a test:
  ;; retracting the file and pruning its vars is not the whole of dropping it. The
  ;; namespace stayed in the compile environment marked compiled, and the driver
  ;; reads that mark to decide it has nothing to do (driver/held?) - so the file
  ;; coming back was compiled by nobody, and app.core's use of a definition it had
  ;; grown while it was away failed on a var that did not exist.
  (let [{:keys [cenv opts src]}
        (compile! '{other.lib "(ns other.lib)\n(def y 2)"
                    app.core  "(ns app.core (:require [other.lib :as o]))\n(def a o/y)"})
        lib  (io/file src "other/lib.cljs")
        core (io/file src "app/core.cljs")]
    (.delete lib)
    (touch! core "(ns app.core)\n(def a 1)")
    (an/stale-reload! cenv opts :prune true)
    (testing "the environment stops holding it as a namespace it compiled"
      (is (not (env/compiled? cenv 'other.lib)))
      (is (not (env/declared? cenv 'other.lib))))
    (touch! lib "(ns other.lib)\n(def y 2)\n(def z 3)")
    (touch! core "(ns app.core (:require [other.lib :as o]))\n(def a o/z)")
    (let [r (an/stale-reload! cenv opts :prune true)]
      (testing "the returning file is compiled as the dependency it is, which is
        why it is not in :reloaded - nothing found it stale, app.core required it"
        (is (= ["app/core.cljs"] (:reloaded r)))))
    (is (has-var? cenv 'other.lib/z))
    (is (contains? (an/analysed-files) "other/lib.cljs"))))

(deftest test-a-deleted-file-whose-macro-file-changed-is-not-stale
  ;; The two are ONE EVENT - a checkout that takes a .cljs away and changes a .clj
  ;; it expands a macro from - and the macro paths of stale-files name files the
  ;; model holds rather than asking the disk. So the gone file arrived in the set
  ;; to recompile, and was handed to the driver as the empty path its retracted
  ;; location spells: "No such file: ", naming nothing.
  (let [cp   (h/temp-dir)
        mf   (io/file cp "switched" "macros.clj")
        base "(ns switched.macros)\n(defmacro two [] %s)\n"
        _    (.mkdirs (.getParentFile mf))
        _    (touch! mf (format base "2"))]
    (with-classpath-dir cp
      (fn []
        (try
          (let [{:keys [cenv opts src]}
                (compile! '{other.lib "(ns other.lib
  (:require-macros [switched.macros :refer [two]]))
(def y (two))"
                            app.core  "(ns app.core (:require [other.lib :as o]))
(def a o/y)"})]
            (.delete (io/file src "other/lib.cljs"))
            (touch! mf (format base "3"))
            (is (= #{"other/lib.cljs"} (an/deleted-files)))
            (is (empty? (an/stale-files))
                "it expands a macro of a file that changed, and there is nothing
                to recompile it from")
            (let [r (an/stale-reload! cenv opts :prune true)]
              (is (= ["other/lib.cljs"] (:deleted r)))
              (is (= [] (:reloaded r)))))
          (finally (clj-analysis/reset-model!)
                   (remove-ns 'switched.macros)))))))

(deftest test-a-require-an-edit-adds-orders-the-recompile
  ;; The ClojureScript side of clojure.analysis's
  ;; a-require-an-edit-adds-orders-the-reload. env/requires answers what the ns
  ;; form said the LAST time a namespace compiled, so a require the edit has just
  ;; introduced is in neither the compile environment nor the model - and it is
  ;; the one whose order matters, because the var it has come for is a var that
  ;; was not there before. The names are chosen so that the alphabet gives the
  ;; WRONG answer: without the disk graph, a/top.cljs sorts first and the
  ;; analyzer throws "No such var: z/added" on it.
  (let [src  (h/write-sources! '{z.base "(ns z.base)\n(def v 1)"
                                 a.top  "(ns a.top)\n(def w 0)"})
        out  (h/temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        opts {:out-dir out :source-paths [src]}]
    (an/run-analysis #(do (driver/compile-namespace! cenv 'z.base opts)
                          (driver/compile-namespace! cenv 'a.top opts)))
    (is (empty? (an/stale-files)))
    (touch! (io/file src "z/base.cljs") "(ns z.base)\n(def v 1)\n(def added 7)\n")
    (touch! (io/file src "a/top.cljs")
            "(ns a.top (:require [z.base :as z]))\n(def w z/added)\n")
    (is (= #{"z/base.cljs" "a/top.cljs"} (an/stale-files)))
    (let [r (an/stale-reload! cenv opts)]
      (is (= ["z/base.cljs" "a/top.cljs"] (:reloaded r))
          "the file that grew the require comes after the file it now requires")
      (is (= '[z.base a.top] (mapv first (:scripts r)))
          "and the runtime is given them in that order too"))
    (is (empty? (an/stale-files)))
    (testing "the new var is what the recompiled file was compiled against"
      (is (= #{["a/top.cljs" 2 8]} (lines (an/find-usages 'z.base/added)))))))

(deftest test-a-require-already-there-still-orders-the-recompile
  ;; the control: the compile environment's own edge, which the disk graph is
  ;; added to rather than substituted for. Same names, same wrong alphabet.
  (let [src  (h/write-sources! '{z.base "(ns z.base)\n(def v 1)"
                                 a.top  "(ns a.top (:require [z.base :as z]))\n(def w z/v)"})
        out  (h/temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        opts {:out-dir out :source-paths [src]}]
    (an/run-analysis #(driver/compile-namespace! cenv 'a.top opts))
    (touch! (io/file src "z/base.cljs") "(ns z.base)\n(def v 2)\n")
    (touch! (io/file src "a/top.cljs")
            "(ns a.top (:require [z.base :as z]))\n(def w (inc z/v))\n")
    (is (= ["z/base.cljs" "a/top.cljs"] (:reloaded (an/stale-reload! cenv opts))))))

(deftest test-a-dropped-tag-makes-its-users-stale
  (let [{:keys [cenv opts src]} (compile! prune-program)]
    (is (empty? (an/meta-stale-files cenv)))
    (touch! (io/file src "deep/util.cljs")
            "(ns deep.util)\n(def keep 1)\n(def gone 2)\n(def flag? true)\n")
    (testing "the edit alone does not tell: the var has its old tag until recompiled"
      (is (= #{"deep/util.cljs"} (an/stale-files cenv))))
    (let [r (an/stale-reload! cenv opts)]
      (testing "recompiling it drops the tag, and app.core was compiled against it"
        (is (= ["deep/util.cljs" "app/core.cljs"] (:reloaded r)))
        (is (str/includes? (second (last (:scripts r))) "truth_"))))
    (is (empty? (an/stale-files cenv)))))

(deftest test-a-def-at-the-repl-changes-what-is-meta-stale
  (let [{:keys [cenv]} (compile! prune-program)
        v (.findInternedVar (env/find-cljs-ns cenv 'deep.util) 'flag?)]
    (alter-meta! v dissoc :tag)
    (is (= #{"app/core.cljs"} (an/meta-stale-files cenv)))
    (is (not (contains? (an/stale-files) "app/core.cljs")) "the disk-only arity")))

(deftest test-arity-dependencies-only-under-static-dispatch
  (let [src  (h/write-sources!
              '{deep.util "(ns deep.util)\n(defn f ([a] a) ([a b] b))"
                app.core  "(ns app.core (:require [deep.util :as u]))\n(def a (u/f 1 2))"})
        edit "(ns deep.util)\n(defn f ([a] a))"
        run  (fn [static?]
               (an/reset-model!)
               (let [cenv (env/compile-env {:ns 'cljs.user})
                     opts {:out-dir (h/temp-dir) :source-paths [src]
                           :static-dispatch static?}]
                 (an/run-analysis #(driver/compile-namespace! cenv 'app.core opts))
                 (let [before (slurp (io/file src "deep/util.cljs"))]
                   (touch! (io/file src "deep/util.cljs") edit)
                   (let [r (:reloaded (an/stale-reload! cenv opts))]
                     (touch! (io/file src "deep/util.cljs") before)
                     r))))]
    (is (= ["deep/util.cljs" "app/core.cljs"] (run true)))
    (is (= ["deep/util.cljs"] (run false)))))

(deftest test-stale-reload-at-the-repl
  (let [{:keys [cenv opts src]} (compile! program)
        shipped (atom [])
        rt      (reify repl/IJsRuntime
                  (-evaluate [_ js] (swap! shipped conj js) {:status :success :value "nil"}))]
    (touch! (io/file src "deep/util.cljs")
            "(ns deep.util)\n(def double (fn* ([x] x)))\n(deftype Box [v])\n")
    (testing "the bound is read before anything is compiled, so a caller that
             got it wrong is told before it has cost anything"
      (is (= :error (:status (repl/eval-form cenv rt '(stale-reload "soon") opts))))
      (is (= :error (:status (repl/eval-form cenv rt '(stale-reload 0) opts))))
      (is (empty? @shipped)))
    (is (= {:status :success :value (pr-str ["deep/util.cljs"])}
           (repl/eval-form cenv rt '(stale-reload) opts)))
    (is (= 1 (count @shipped)))
    (testing "a bound asks the runtime to give up, and a runtime that cannot be
             asked says so rather than taking the bound and ignoring it"
      (touch! (io/file src "deep/util.cljs")
              "(ns deep.util)\n(def double (fn* ([x] (* 2 x))))\n(deftype Box [v])\n")
      (let [r (repl/eval-form cenv rt '(stale-reload 1000) opts)]
        (is (= :error (:status r)))
        (is (str/includes? (:value r) "IJsDeadline"))))
    (testing "and a REPL started with :analysis keeps the model as it loads files"
      (an/reset-model!)
      (repl/eval-form cenv rt (list 'load-file (str (io/file src "app/core.cljs")))
                      (assoc opts :analysis true))
      (is (seq (an/file-forms "app/core.cljs")))
      (repl/eval-form cenv rt (list 'load-file (str (io/file src "deep/util.cljs"))) opts)
      (is (empty? (an/file-forms "deep/util.cljs"))))))

;; --- code the program does not run: #_ and (comment ...) ------------------------

(def ^:private dead-program
  '{deep.util "(ns deep.util)
(def dbl (fn* ([x] (js* \"~{} * 2\" x))))"
    other.lib "(ns other.lib)
(def z 3)"
    app.core  "(ns app.core
  (:require [deep.util :as u :refer [dbl]] [other.lib :as ol])
  (:require-macros [clojure.cljs.analysis-test :refer [calls-double]]))
#_(u/dbl 1)
(defn f [dbl] #_(dbl 2) dbl)
(comment
  (u/dbl 3)
  (let [dbl 4] (dbl))
  (calls-double (later))
  (str 1)
  (map str [1])
  (defn ghost [] 1)
  (quote (later))
  #_(ol/z)
  :in-comment)
#_::ol/k
(defn later [] 1)"})

(deftest test-dead-code-is-resolved-for-find-usages
  (let [{:keys [cenv]} (compile! dead-program)
        dead (fn [spans] (into #{} (keep #(when (:dead %) [(:line %) (:dead %)])) spans))]
    (testing "a use in a #_ and in a comment is found, marked as dead"
      (is (= #{[4 :discard] [7 :comment]} (dead (an/find-usages 'deep.util/dbl))))
      (is (= #{["app/core.cljs" 4 4] ["app/core.cljs" 7 4]}
             (lines (calls (an/find-usages 'deep.util/dbl))))
          "and not the #_ in f, nor the let in the comment: their dbl is a local")
      (is (every? #(= 'app.core (:from-ns %)) (an/find-usages 'deep.util/dbl))))
    (testing "resolved at the end of the file: a def after the comment is found"
      (is (= #{[9 :comment]} (dead (an/find-usages 'app.core/later)))))
    (testing "a macro in a head, a var anywhere else - the analyzer's order"
      (is (= #{[9 :comment]}
             (dead (an/find-macro-usages 'clojure.cljs.analysis-test/calls-double))))
      (is (= #{[10 :comment]} (dead (an/find-macro-usages 'cljs.core/str))))
      (is (= #{[11 :comment]} (dead (an/find-usages 'cljs.core/str)))))
    (testing "nothing in it is defined"
      (is (nil? (an/definition 'app.core/ghost))))
    (testing "the comment call itself is live"
      (is (= #{} (dead (an/find-macro-usages 'cljs.core/comment))))
      (is (= 1 (count (an/find-macro-usages 'cljs.core/comment)))))
    (testing "a keyword in a #_ or a comment is dead too"
      (is (= #{[16 :discard]} (dead (an/find-keyword-usages :other.lib/k))))
      (is (= #{[15 :comment]} (dead (an/find-keyword-usages :in-comment)))))
    (testing "a use in a comment keeps a require; one in a #_ does not"
      (is (= '{ol other.lib} (an/unused-aliases cenv 'app.core)))
      (is (= {} (an/unused-macro-refers cenv 'app.core))))))

(deftest test-asking-one-index-does-not-build-the-others
  ;; What having a cache EACH is for. The derived indexes are all pure functions of
  ;; the same form log, but they are not wanted at the same moments - a reload reads
  ;; `:defs` while it prunes and reads nothing else, while `:usages` and `:locals`
  ;; are the large ones and answer an editor's questions. Held as one index they were
  ;; all rebuilt whenever any of them was, and every file compiled is a new form log,
  ;; so recompiling K files replayed the whole model K times.
  ;;
  ;; Read off the caches and not off a clock: what is being tested is that work did
  ;; NOT happen, and a fast answer is not a claim that it did not.
  (compile! program)
  (let [m     @@#'an/model
        built (fn [] (set (for [[k c] @#'an/index-caches
                                :when (identical? (:forms m) (:forms @c))]
                            k)))]
    (is (empty? (built)) "a fresh log, so nothing is built for it yet")
    (#'an/index m :defs)
    (is (= #{:defs} (built)))
    (#'an/index m :usages)
    (is (= #{:defs :usages} (built)))
    (testing "and `derived` is all of them, which is why a reload does not ask for it"
      (#'an/derived m)
      (is (= (set @#'an/index-keys) (built))))
    (testing "asking twice does not build twice"
      (doseq [k @#'an/index-keys]
        (is (identical? (#'an/index m k) (#'an/index m k))
            (str "second ask for " k " rebuilt it"))))))

(deftest test-file-def-vars-answers-what-a-walk-of-the-defs-answered
  ;; `file-def-vars` reads the file's own forms rather than walking every def in the
  ;; model. Same answer, per file, and the files are the model's own.
  (compile! program)
  (let [m      @@#'an/model
        walked (fn [source]
                 (set (for [[k e] (#'an/index m :defs)
                            :when (= source (:source (:span e)))]
                       k)))]
    (is (= '#{deep.util/double deep.util/Box deep.util/->Box}
           (an/file-def-vars "deep/util.cljs")))
    (doseq [source (keys (:source->forms m))]
      (is (= (walked source) (an/file-def-vars source)) source))
    (is (= #{} (an/file-def-vars "nobody/here.cljs")))))

;; --- what the compiler says it has defined ---------------------------------

(defn- defining!
  "Run `thunk` with clojure.analysis/*defined* collecting, and answer the events
  it reported, in order."
  [thunk]
  (let [seen (atom [])]
    (binding [clj-analysis/*defined* #(swap! seen conj %)] (thunk))
    @seen))

(defn- defined-nss
  "The namespaces `events` say were recompiled, cljs.core left out - it is compiled
  once on the way up and is nobody's project."
  [events]
  (into [] (comp (filter #(and (= :define (:op %)) (nil? (:var %))))
                 (map :ns)
                 (remove #{'cljs.core}))
        events))

(deftest test-a-compiled-file-says-its-namespace-was-replaced
  (let [src    (h/write-sources! program)
        out    (h/temp-dir)
        cenv   (env/compile-env {:ns 'cljs.user})
        opts   {:out-dir out :source-paths [src]}
        events (defining! #(an/run-analysis
                            (fn [] (driver/compile-namespace! cenv 'app.core opts))))]
    (testing "one event per namespace compiled, in the order they compiled -
              a dependency before what requires it"
      (is (= '[deep.util app.core] (defined-nss events))))
    (testing "the unit is the namespace and the event says which file it was"
      (is (= [{:dialect :cljs :op :define :ns 'app.core :source "app/core.cljs"}]
             (filter #(= 'app.core (:ns %)) events))))
    (testing "and nothing is said about a namespace that was already held"
      (is (empty? (defined-nss
                    (defining! #(an/run-analysis
                                 (fn [] (driver/compile-namespace! cenv 'app.core opts))))))))))

(deftest test-a-def-typed-at-a-prompt-is-reported
  (let [{:keys [cenv]} (compile! program)
        events (defining! #(repl/compile-form cenv '(def typed 1)))]
    (testing "the case no file and no model can answer: a form typed at a prompt is
              compiled inside no file, and it defines a var all the same"
      (is (= [{:dialect :cljs :op :define :ns 'cljs.user :var 'cljs.user/typed}]
             events)))
    (testing "every def of the input, however deep - one input can be a do"
      (is (= '[cljs.user/x cljs.user/y]
             (mapv :var (defining! #(repl/compile-form cenv '(do (def x 1) (def y 2))))))))
    (testing "and an input that defines nothing says nothing"
      (is (empty? (defining! #(repl/compile-form cenv '(+ 1 1))))))
    (testing "the model holds none of it, which is what makes it a model of the
              code rather than of the session"
      (is (not (contains? (an/analysed-files) "cljs/user.cljs"))))))

(deftest test-a-reload-says-what-it-took-away
  (let [{:keys [cenv opts src]} (compile! prune-program)]
    (touch! (io/file src "deep/util.cljs")
            "(ns deep.util)\n(def keep 1)\n(def ^boolean flag? true)\n")
    (let [err    (java.io.StringWriter.)
          events (defining! #(binding [*err* err]
                               (an/stale-reload! cenv opts :prune true)))]
      (testing "the file that was recompiled is said to have been"
        (is (= '[deep.util] (defined-nss events))))
      (testing "and the def it no longer has is said to have gone - a definition
                taken away by something nobody typed"
        (is (= [{:dialect :cljs :op :remove :ns 'deep.util :var 'deep.util/gone}]
               (filterv #(= :remove (:op %)) events))))
      (testing "and it is said after it has gone, not before"
        (is (not (has-var? cenv 'deep.util/gone)))))))

(deftest test-nothing-is-reported-where-nothing-is-listening
  (is (nil? clj-analysis/*defined*) "and the default is to be listening nowhere")
  (let [{:keys [cenv]} (compile! program)]
    (is (some? (repl/compile-form cenv '(def quiet 1))))
    (is (= #{"app/core.cljs" "deep/util.cljs"} (an/analysed-files)))))
