;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "src/compat: cljs.analyzer.api under ClojureScript's own name.

  A macro namespace of somebody else's is ordinary Clojure, loaded by `require'
  off the classpath, and it asks for the names ClojureScript uses. This compiler
  renamed them to clojure.cljs.*, so hx's useSmartEffect - which resolves every
  symbol in its body to build React's dependency vector - did not half-work, it
  did not load at all.

  ONE NAMESPACE AND NOT TWO, which is the shape of the problem rather than a
  choice about scope. cljs.analyzer.api declares no vars, so every name in it
  forwards; cljs.analyzer is mostly dynamic vars, and a var cannot be forwarded
  by anything. test-the-documented-door-is-the-forwardable-one is that fact,
  asserted against ClojureScript's own file so that it is checked rather than
  believed.

  TESTED FROM OUTSIDE, because the file is deliberately not on this classpath.
  src/compat is a source root of its own so that the AST oracle keeps working: a
  .clj shadows a jar's .cljc, and clojure.cljs.analyzer-test reaches for
  cljs.analyzer.api/resolve out of ClojureScript 1.12.145. Shipping this file
  beside the compiler would leave that test comparing this compiler with itself.

  So the tests here are of two kinds. The ones that read files as TEXT can run in
  this process, and they check what would rot silently: that every name forwarded
  is still a name this compiler has, and that nothing here is a var. The one that
  checks a library actually loads forks a jvm with src/compat added, which is the
  only place this namespace can be loaded.

  See doc/cljs-compiler.md 5.66."}
  clojure.cljs.compat-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [clojure.tools.reader :as tr]
            [clojure.tools.reader.reader-types :as rt]
            [clojure.cljs.test-harness :as h])
  (:import [java.io File]))

(def ^:private compat-root (io/file "src/compat"))

(def ^:private compat-file (io/file compat-root "cljs" "analyzer" "api.clj"))

(defn- forms
  "Every top level form of SRC, read but not evaluated. Reader conditionals are
  taken the way this jvm would take them, so that a .cljc reads as its :clj half.

  TOOLS.READER RATHER THAN clojure.core/read, for one reason: a source file uses
  its own aliases in auto-resolved keywords - cljs/analyzer/api.cljc writes
  ::ana/namespaces - and core's reader resolves those against the namespace doing
  the reading, which is this one, so it throws `Invalid token'. tools.reader takes
  an *alias-map*, and since nothing here looks at the keywords themselves, any
  answer will do so long as it is an answer."
  [src]
  (let [rdr (rt/indexing-push-back-reader (slurp src))
        opts {:eof ::eof :read-cond :allow :features #{:clj}}]
    (binding [tr/*read-eval* false
              tr/*alias-map* (constantly 'unresolved-alias)]
      (doall (take-while #(not= ::eof %) (repeatedly #(tr/read opts rdr)))))))

(defn- defs
  "Every def form anywhere in FS, as [what-kind name]. Anywhere and not just at
  the top, because a .cljc keeps half its namespace inside a reader conditional."
  [fs]
  (->> (tree-seq coll? seq fs)
       (filter #(and (seq? %) (symbol? (first %))
                     (str/starts-with? (name (first %)) "def")
                     (symbol? (second %))))
       (map (juxt #(name (first %)) #(second %)))))

(defn- aliases
  "The alias to namespace map of a file's ns form."
  [fs]
  (let [ns-form (first (filter #(and (seq? %) (= 'ns (first %))) fs))
        requires (->> ns-form
                      (filter #(and (seq? %) (= :require (first %))))
                      first
                      rest)]
    (into {} (for [spec requires
                   :when (vector? spec)
                   :let [m (apply hash-map (rest spec))]
                   :when (:as m)]
               [(:as m) (first spec)]))))

(defn- forwarded
  "Every qualified symbol in FS written through one of the file's own aliases,
  as the fully qualified name it stands for."
  [fs]
  (let [alias->ns (aliases fs)]
    (->> (tree-seq coll? seq fs)
         (filter symbol?)
         (keep (fn [s]
                 (when-let [target (alias->ns (some-> (namespace s) symbol))]
                   (symbol (str target) (name s)))))
         distinct
         sort)))

;;; Why there is one file and not two

(h/deftest-when h/cljs-analyzer? test-the-documented-door-is-the-forwardable-one
  ;; THE REASON src/compat CAN EXIST AT ALL, checked against ClojureScript's own
  ;; source rather than remembered. A Var belongs to exactly one namespace and a
  ;; qualified read finds only an interned one - Compiler.resolveIn goes to
  ;; Namespace.findInternedVar, which refuses a var whose ns is not this one - so
  ;; a namespace published under someone else's name can forward functions and
  ;; can forward nothing else. cljs.analyzer.api happens to be all functions and
  ;; macros: it surfaces *cljs-file*, *cljs-ns* and *compiler* through zero
  ;; argument readers. That is what makes it copyable, and it is also why there
  ;; is no cljs/analyzer.clj here - that one is mostly vars, so a copy of it
  ;; would be a second set of vars bound by nothing, reading nil forever.
  (let [api (io/resource "cljs/analyzer/api.cljc")]
    (is (some? api) "the oracle jar should carry cljs/analyzer/api.cljc")
    (let [named (defs (forms api))
          by-name (into {} (map (fn [[kind n]] [n kind])) named)]
      (is (empty? (filter #(str/starts-with? (name (second %)) "*") named))
          (str "cljs.analyzer.api is forwardable because it declares no DYNAMIC "
               "var; one has appeared: "
               (pr-str (map second (filter #(str/starts-with? (name (second %)) "*")
                                           named)))))
      (testing "it reads the analyzer's own vars through functions instead"
        ;; The three a caller actually wants, and the whole reason this door can
        ;; be opened: (defn current-file [] ana/*cljs-file*) forwards, the var
        ;; itself does not.
        (doseq [n '[current-file current-ns current-state]]
          (is (= "defn" (by-name n))
              (str n " should be a function reading a var, not the var"))))
      (testing "and what is not a function is not dynamic either"
        ;; default-passes is a plain value copied off ana/default-passes.
        ;; Nothing rebinds it - with-passes binds ana/*passes* - so it would
        ;; forward by value if anything ever asked for it. Nothing does.
        (is (= ["default-passes"] (mapv #(name (second %))
                                        (filter #(= "def" (first %)) named)))
            "a second plain def here is worth a look before it is copied"))))
  (testing "which is why the internal door is not copied"
    (is (not (.exists (io/file compat-root "cljs" "analyzer.clj")))
        (str "cljs.analyzer is dynamic vars; a copy of it cannot forward them "
             "and would read nil forever. Callers come through the api."))))

;;; What must not be on this classpath

(deftest test-the-compat-is-not-beside-the-compiler
  ;; THE INVARIANT THE DIRECTORY EXISTS FOR, and the one that would be undone by
  ;; somebody tidying src/compat into src/clj. The file is named the way
  ;; ClojureScript names it, RT.load tries .clj before .cljc, and this suite
  ;; carries ClojureScript as an oracle - so the day this is on this classpath is
  ;; the day the oracle starts comparing this compiler with itself.
  (is (nil? (io/resource "cljs/analyzer/api.clj"))
      "src/compat must not be on the test classpath")
  (testing "and the oracle still reaches ClojureScript's own"
    (when h/cljs-analyzer?
      (is (str/includes? (str (io/resource "cljs/analyzer.cljc")) ".jar!"))
      (is (str/includes? (str (io/resource "cljs/analyzer/api.cljc")) ".jar!"))))
  (testing "but the file is there to be shipped"
    (is (.isFile compat-file) "cljs.analyzer.api is missing from src/compat"))
  (testing "and a consumer does get it"
    ;; The other half of the same invariant, and the half that is one line of
    ;; edn: off this classpath and on everybody else's. A src/compat that no
    ;; :paths names is a directory nothing reads, which is the same as not
    ;; having written it.
    (let [paths (:paths (read-string (slurp "deps.edn")))]
      (is (some #{"src/compat"} paths)
          (str "deps.edn :paths must carry src/compat: " (pr-str paths)))))
  (testing "and so does a consumer who only has the jar"
    ;; THE OTHER HALF, and the one this file cannot check directly: there is no
    ;; jar during `mvn test'. src/compat is not a <resource>, because those are
    ;; copied at process-resources into target/classes, which is on the classpath
    ;; the assertions above are about. It is copied at prepare-package instead -
    ;; after test, before jar - which is the only window. So what is asserted here
    ;; is the wiring, and the absence assertions above are what would catch it
    ;; being moved back to a phase that runs too early.
    (let [pom (slurp "pom.xml")]
      (is (str/includes? pom "<id>compat-into-jar</id>")
          "pom.xml must copy src/compat into the jar")
      (is (re-find #"(?s)<id>compat-into-jar</id>.{0,200}<phase>prepare-package</phase>"
                   pom)
          (str "the copy must run at prepare-package: earlier than that is before"
               " `test' and would put it on the test classpath")))))

;;; What would rot without being noticed

(deftest test-every-name-the-compat-forwards-is-still-here
  ;; A forwarding namespace nothing loads is a namespace nothing type-checks. It
  ;; cannot be on this classpath, so the compiler renaming one of its own vars
  ;; would leave this file naming something that is gone, and the first to find
  ;; out would be somebody else's macro namespace failing to compile.
  (let [targets (forwarded (forms compat-file))]
    (is (seq targets) "a forwarding namespace that forwards nothing is a mistake")
    (doseq [target targets]
      (require (symbol (namespace target)))
      (is (some? (ns-resolve (symbol (namespace target)) (symbol (name target))))
          (str target " is named by src/compat and does not exist here")))))

(deftest test-the-compat-copies-no-dynamic-var
  ;; Ours is functions for the same reason ClojureScript's is - see
  ;; test-the-documented-door-is-the-forwardable-one - and this is the guard on
  ;; the day somebody adds *cljs-file* here because a library asked for it. It
  ;; would load, it would run, and it would record nil.
  (let [named (map second (defs (forms compat-file)))]
    (is (seq named) "the compat defines nothing at all")
    (is (empty? (filter #(str/starts-with? (name %) "*") named))
        "a dynamic var cannot be forwarded, only named in the docstring"))
  (testing "and it says where the vars went"
    (let [ns-form (first (filter #(and (seq? %) (= 'ns (first %)))
                                 (forms compat-file)))
          doc (str (:doc (meta (second ns-form))))]
      (is (str/includes? doc "clojure.cljs")
          "the docstring is the map, so it has to name where things are now")
      (is (str/includes? doc "findInternedVar")
          "and why a var could not come along"))))

;;; What a library sees

(h/deftest-when h/cljs-analyzer? test-a-library-loads-through-the-clojurescript-name
  ;; The whole point, and it can only be asked in another process. A jvm with
  ;; src/compat added is what a project using this compiler has; the require is
  ;; what hx.hooks.alpha's ns form does, and the resolve is what its resolve-vars
  ;; does to every symbol in a body - (map (partial cljs.analyzer.api/resolve env)
  ;; syms), keep the ones that are there, take :name.
  (let [java (str (io/file (System/getProperty "java.home") "bin" "java"))
        cp (str (System/getProperty "java.class.path")
                File/pathSeparator (.getPath compat-root))
        program (str "(require 'cljs.analyzer.api '[clojure.cljs.env :as env]"
                     " '[clojure.cljs.driver :as driver])"
                     "(println :publics (sort (keys (ns-publics 'cljs.analyzer.api))))"
                     "(println :repl-file (pr-str (cljs.analyzer.api/current-file)))"
                     "(env/with-current-ns 'cljs.user"
                     "  (let [cenv (env/compile-env {:ns 'cljs.user :core-macros 'cljs.core})"
                     "        out (str (java.nio.file.Files/createTempDirectory \"compat\""
                     "                   (make-array java.nio.file.attribute.FileAttribute 0)))]"
                     "    (binding [env/*cenv* cenv]"
                     "      (driver/compile-namespace! cenv 'cljs.core {:out-dir (java.io.File. out)})"
                     "      (let [e (env/analysis-env cenv)"
                     "            r #(cljs.analyzer.api/resolve e %)]"
                     "        (println :deps (->> '[map no-such-name-at-all inc]"
                     "                            (map r) (filter some?) (map :name) vec))))))")
        {:keys [out err exit]} (sh/sh java "-classpath" cp "clojure.main" "-e" program)]
    (is (zero? exit) (str out err))
    (is (str/includes? out "(all-ns current-file find-ns get-options ns-interns ns-resolve resolve)")
        (str "the seven of cljs.analyzer.api and no more: " out))
    (is (str/includes? out ":repl-file nil")
        (str "current-file is nil outside a file, where ClojureScript says"
             " NO_SOURCE_PATH: " out))
    (is (str/includes? out "[cljs.core/map cljs.core/inc]")
        (str "a name that is there resolves, one that is not is dropped: " out))))
