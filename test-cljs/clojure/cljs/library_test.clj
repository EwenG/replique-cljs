;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The rest of the ClojureScript standard library, vendored.

  cljs.core is the language and it arrived first; clojure.string and clojure.set
  came with cljs.test because cljs.test requires them. Everything else a
  ClojureScript program reaches for by name was simply absent, and absent in a way
  that only showed at the far end of somebody else's dependency graph: hx.hiccup
  requires clojure.walk, so a project using hx compiled nothing at all, and what it
  was told was `Could not locate clojure/walk.cljs'.

  FIFTEEN FILES, ALL VERBATIM, and verbatim is why this file is short. Not one of
  them needed a line changed - unlike cljs/core.cljc (183 declared adaptations) and
  unlike cljs/test.cljs (four) - so what there is to check is byte equality and
  that the thing runs. The reason they cost nothing is the same reason the goog
  subset's fourteen did (clojure.cljs.goog): a dependency chain that terminates
  cheaply. clojure.walk requires nothing. clojure.data requires clojure.set.
  cljs.pprint requires clojure.string and three goog files that were already here.

  THE TWO HALVES OF spec WERE THE OMISSION THIS FOUND. cljs/spec/alpha.cljc,
  cljs/spec/gen/alpha.cljc and cljs/spec/test/alpha.cljc were vendored and adapted
  (see clojure.cljs.cljs-test-test), and so was cljs/spec/test/alpha.cljs - but the
  RUNTIME halves of the first two were not, so the one .cljs that was here required
  two namespaces that did not exist and could not load. cljs/stacktrace.cljc is the
  third thing it wanted, and is here for that reason alone: its :cljs branch is
  goog.string and clojure.string, and its :clj branch is ClojureScript's compiler,
  which nothing here reads.

  THE FOURTEENTH AND FIFTEENTH ARRIVED LATER, and the list below used to carry the
  reason they never would. cljs/core/specs/alpha.cljc was NOT VENDORED because its
  macro half requires clojure.spec.alpha, which is a JVM artifact rather than a
  ClojureScript file - `a second dependency for a namespace no program requires to
  run'. That reason was right that nothing asked and wrong about the cost.

  Nothing asked until better-cond, which opens

      (ns better-cond.core
        (:require [clojure.core.specs.alpha]
                  [clojure.spec.alpha :as spec]))

  with the first of those OUTSIDE any reader conditional, so the ClojureScript
  analyzer has to resolve it before the file compiles a line - and a program with
  better-cond anywhere under it stops there. The keywords better-cond then writes
  (:clojure.core.specs.alpha/local-name, among others) are lazy references inside
  an s/or that nothing conforms at run time; the namespace has to EXIST, not to
  hold anything. phrase looks like a second caller and is not one: its :cljs branch
  omits the require and replaces every one of those keys with any? and
  simple-symbol?.

  And the cost is not a dependency. org.clojure/spec.alpha is declared by the
  CLOJURE THIS COMPILER RUNS ON - replique-clj/clojure names it exactly as
  org.clojure/clojure does, which is why clojure.spec.alpha is already on this
  suite's classpath - so the two files add no coordinate to anybody's deps.edn.

  WHAT THE MACRO HALF DOES HERE IS NOTHING, and vendoring it anyway is the point.
  Its twelve s/fdef forms - core/let, core/defn, core/ns-special-form and the rest
  - exist to be read by do-macroexpand-check, and this compiler sets
  :spec-skip-macros true and never reads them (clojure.cljs.macroexpand, a decision
  rather than a default). So a stub would have served: (ns cljs.core.specs.alpha)
  and nothing else compiles better-cond just as well, and the emitted module is the
  same 314 bytes either way, because the .cljs half defines no var in either case.
  It would also be the first ADAPTED file in this list, a divergence to re-justify
  the day :spec-skip-macros changes, in exchange for not loading a file that costs
  a require of clojure.spec.alpha on the JVM. 5.65's rule decides it and decides it
  the same way it decided the other thirteen: the chain terminates cheaply, so ship
  what everyone else has. test-the-macro-half-is-what-registers-the-specs is where
  that stops being a preference and becomes something a test can lose.

  NOT VENDORED, AND EACH FOR ITS OWN REASON:

      cljs/nodejs.cljs   It IS (def require (js* \"require\")) and this compiler
                         emits ES modules, where there is no such name. It was
                         vendored, it loaded, and node answered `require is not
                         defined in ES module scope'. A file that cannot work is
                         worse absent than present.
      clojure/reflect.cljs  Upstream marks it DEPRECATED, and it requires
                         clojure.browser.net and clojure.browser.event - the old
                         browser-REPL transport, which this fork replaced.
      cljs/loader.cljs   The :modules loader. There are no modules here.
      cljs/js.cljs       The self-hosted compiler.

  See doc/cljs-compiler.md 5.65."}
  clojure.cljs.library-test
  (:require [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.repl :as repl]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]])
  (:import [java.io StringWriter]))

(use-fixtures :each h/cursor)

;; --- the vendoring is honest -------------------------------------------------

(defn- jar-copy
  "The ClojureScript jar's own `path` - core-test's helper, needed here for the
  third time and for the same reason: our copy shadows theirs on the classpath, so
  io/resource would answer with the file under test."
  [path]
  (some (fn [^java.net.URL u]
          (when (= "jar" (.getProtocol u)) (slurp u)))
        (enumeration-seq
         (.getResources (.getContextClassLoader (Thread/currentThread)) path))))

(def ^:private cljs-jar? (some? (jar-copy "cljs/core.cljc")))

(def ^:private vendored
  "Every file this milestone added, and the list is the whole of what it did.

  Kept as paths rather than namespaces because that is what the claim is about: a
  path is what gets diffed and what the classpath answers for. clojure/edn.cljs
  names cljs.reader, which was already vendored and until now could not load.

  THE LAST TWO ARE NOT THIS MILESTONE'S. cljs/core/specs/alpha.cljc and .cljs came
  later, when better-cond asked for a name this file had written down as one it
  would not carry. They are in the same list because they make the same claim -
  verbatim, and the copy that loads is ours - and a second list would only be a
  place for one of them to be forgotten."
  ["clojure/walk.cljs"
   "clojure/data.cljs"
   "clojure/zip.cljs"
   "clojure/edn.cljs"
   "clojure/datafy.cljs"
   "clojure/core/protocols.cljs"
   "clojure/core/reducers.cljs"
   "cljs/math.cljs"
   "cljs/pprint.cljs"
   "cljs/pprint.cljc"
   "cljs/stacktrace.cljc"
   "cljs/spec/alpha.cljs"
   "cljs/spec/gen/alpha.cljs"
   "cljs/core/specs/alpha.cljc"
   "cljs/core/specs/alpha.cljs"])

(h/deftest-when cljs-jar? test-the-library-is-vendored-unmodified
  ;; The property that makes "vendored" an honest word, and the one that decays
  ;; silently: a file nobody re-reads is a file anybody can edit. Byte equality
  ;; rather than a declared-adaptations set, because there are no adaptations -
  ;; which is itself the claim worth pinning, since the day one of these needs a
  ;; line changed is the day it should stop being checked this way.
  (doseq [path vendored]
    (testing path
      (is (some? (jar-copy path)) "not in the jar at all - is the path right?")
      (is (= (jar-copy path) (slurp (io/resource path)))))))

(h/deftest-when cljs-jar? test-our-copies-are-the-ones-that-load
  ;; src/clj comes before the jar, and everything above depends on it: a classpath
  ;; that put the jar first would compile a program against ClojureScript's
  ;; cljs.core rather than ours, and the diff test above would still pass because
  ;; it reaches for the jar by name.
  ;;
  ;; WHAT ANSWERS HERE IS target/classes, not src/clj: Maven's test classpath is the
  ;; build output, and the resources copy is additive - it never removes what is no
  ;; longer in src/clj. So a defeat that deletes one of these files leaves a stale
  ;; copy behind and reads as INERT. Delete both, or mvn clean first.
  (doseq [path vendored]
    (testing path
      (is (not= "jar" (.getProtocol (io/resource path)))))))

;; --- it compiles and runs ----------------------------------------------------

(defn- runs
  "Compile `src` as demo.core against the real source path and run it on node: what
  it printed.

  The library namespaces are found the way any dependency is - through the
  classpath, since src/clj is where they live - so the only source this writes is
  the program that requires them."
  [src]
  (let [source (h/write-sources! (h/temp-dir) {'demo.core src})
        target (h/temp-dir)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'demo.core
                                 {:out-dir target :source-paths [source]})
      (let [{:keys [out err exit]} (sh/sh "node" (.getPath (io/file target "ns/demo/core.js")))]
        (is (zero? exit) (str out err))
        out)
      (finally (h/delete-tree! source) (h/delete-tree! target)))))

(h/deftest-when h/node? test-the-data-namespaces-run
  ;; walk, data and zip in one program: three files whose dependency chains are
  ;; nothing, clojure.set and nothing. clojure.walk is first because it is the one
  ;; that was in the way - hx.hiccup requires it, and hx is in the ns form of most
  ;; of a real application.
  (let [out (runs "(ns demo.core
                     (:require [clojure.walk :as walk]
                               [clojure.data :as data]
                               [clojure.zip :as zip]))
                   (js/console.log (pr-str (walk/postwalk-replace {:a 1} [:a :b {:a :a}])))
                   (js/console.log (pr-str (data/diff {:a 1 :b 2} {:a 1 :c 3})))
                   (js/console.log (pr-str (-> (zip/vector-zip [1 [2 3]])
                                               zip/down zip/right zip/node)))")]
    (is (str/includes? out "[1 :b {1 1}]"))
    (is (str/includes? out "({:b 2} {:c 3} {:a 1})"))
    (is (str/includes? out "[2 3]"))))

(h/deftest-when h/node? test-the-two-namespaces-written-as-cljs-run-under-their-clojure-names
  ;; cljs/math.cljs and cljs/pprint.cljs are named cljs.math and cljs.pprint, and
  ;; a program requiring clojure.math gets them through the alias rule
  ;; (analyzer/aliased-clj-ns) - the same rule clojure.test has always ridden on.
  ;; So the assertion is not that they work but that they work UNDER THE OTHER
  ;; NAME, which is the name a reader of Clojure writes.
  (let [out (runs "(ns demo.core
                     (:require [clojure.math :as m]
                               [clojure.pprint :as pp]))
                   (js/console.log (pr-str [(m/sqrt 16) (m/floor 2.7)]))
                   (js/console.log (pr-str (with-out-str (pp/pprint {:a (range 3)}))))")]
    (is (str/includes? out "[4 2]"))
    (is (str/includes? out "{:a (0 1 2)}"))))

(h/deftest-when h/node? test-datafy-and-reducers-run
  ;; clojure.datafy is the one file here with a dependency inside this milestone:
  ;; clojure.core.protocols, vendored beside it and useless alone.
  (let [out (runs "(ns demo.core
                     (:require [clojure.datafy :as d]
                               [clojure.core.reducers :as r]))
                   (js/console.log (pr-str (d/datafy 42)))
                   (js/console.log (pr-str (r/fold + (vec (range 100)))))")]
    (is (str/includes? out "42"))
    (is (str/includes? out "4950"))))

(h/deftest-when h/node? test-reading-edn-runs
  ;; The one that needed a DEPENDENCY rather than a file. cljs/reader.cljs was
  ;; already vendored and already unloadable: it requires cljs.tools.reader and
  ;; cljs.tools.reader.edn, which are seven .cljs files in org.clojure/tools.reader
  ;; and were on nobody's classpath. clojure.edn is three functions over it.
  (let [out (runs "(ns demo.core
                     (:require [clojure.edn :as edn]
                               [cljs.reader :as reader]))
                   (js/console.log (pr-str (edn/read-string \"{:a 1 :b [2 3]}\")))
                   (js/console.log (pr-str (reader/read-string \"#{1 2}\")))")]
    (is (str/includes? out "{:a 1, :b [2 3]}"))
    (is (str/includes? out "#{1 2}"))))

(h/deftest-when h/node? test-spec-runs
  ;; Both halves of it, which is what was missing: the macros were here and the
  ;; runtime was not, so cljs.spec.alpha was a namespace whose every var was
  ;; declared by a macro and defined nowhere.
  (let [out (runs "(ns demo.core (:require [cljs.spec.alpha :as s]))
                   (js/console.log (pr-str (s/valid? (s/and int? pos?) 3)))
                   (js/console.log (pr-str (s/conform (s/cat :n int? :s string?) [1 \"x\"])))
                   (js/console.log (s/explain-str (s/coll-of int?) [1 :a]))")]
    (is (str/includes? out "true"))
    (is (str/includes? out "{:n 1, :s \"x\"}"))
    (is (str/includes? out "failed: int?"))))

(h/deftest-when h/node? test-the-spec-test-namespace-loads
  ;; cljs/spec/test/alpha.cljs was vendored before its three dependencies were -
  ;; cljs.spec.alpha, cljs.spec.gen.alpha and cljs.stacktrace - so the assertion
  ;; is only that it is reachable now. Instrumenting is not exercised here: it
  ;; rewrites vars in a running program, which is a test of spec and not of
  ;; whether this file is on the classpath.
  ;;
  ;; summarize-results rather than instrument, which is a MACRO and so is not a
  ;; name the runtime half has at all - it lives in the .cljc that was here before
  ;; this milestone, which is exactly the half that was never the problem.
  (let [out (runs "(ns demo.core (:require [cljs.spec.test.alpha :as st]))
                   (js/console.log (pr-str (st/summarize-results [])))")]
    (is (str/includes? out "{:total 0}"))))

;; --- the specs of core macro forms ------------------------------------------

(h/deftest-when h/node? test-a-namespace-may-require-the-specs-of-core-macro-forms
  ;; SPELLED THE CLOJURE WAY, because that is the spelling that broke. better-cond
  ;; writes (:require [clojure.core.specs.alpha]) and there is no
  ;; clojure/core/specs/alpha.cljs anywhere - upstream ships the cljs.* name only -
  ;; so what carries it is the alias rule the two tests above ride on
  ;; (analyzer/aliased-clj-ns): a clojure.* name with no file of its own means the
  ;; cljs.* one. The error before this pair was vendored named both halves of that
  ;; rule and neither of the reasons:
  ;;
  ;;     Could not locate clojure/core/specs/alpha.cljs or cljs/core/specs/alpha.cljs
  ;;
  ;; THERE IS NOTHING TO CALL, and that is not a gap in the test. The .cljs half is
  ;; an ns form and a :require-macros and no var at all; every spec it is named for
  ;; is registered on the JVM by the .cljc, for a macroexpansion check this
  ;; compiler skips. So what a program can observe is that the name resolves, the
  ;; module is emitted and node loads it, and this asserts exactly that much.
  (let [out (runs "(ns demo.core
                     (:require [clojure.core.specs.alpha]))
                   (js/console.log \"the specs namespace loaded\")")]
    (is (str/includes? out "the specs namespace loaded"))))

(deftest test-the-macro-half-is-what-registers-the-specs
  ;; THE TEST A STUB LOSES. (ns cljs.core.specs.alpha) on its own compiles
  ;; better-cond and emits the same 314 bytes, so the test above cannot tell the
  ;; two apart. This one can: the :require-macros in the vendored .cljs is what
  ;; loads the .cljc on the JVM, and the .cljc is 7,469 bytes of s/def whose whole
  ;; visible effect is these keys being in clojure.spec's registry.
  ;;
  ;; requiring-resolve rather than a require in the ns form: clojure.spec.alpha
  ;; arrives here transitively, as a dependency of the Clojure this compiler runs
  ;; on, and nothing else in this compiler names it. Reaching for it by name in one
  ;; place says that, where an ns form would say it is ours.
  ;;
  ;; THE REGISTRY IS PROCESS-WIDE, so what this pins is that a compile CAN load the
  ;; macro half - not that this particular compile was the one that did. The defeat
  ;; that matters is the same either way: stub the .cljs and nothing loads it at all.
  (let [source   (h/write-sources! {'demo.core "(ns demo.core
                                                  (:require [cljs.core.specs.alpha]))"})
        target   (h/temp-dir)
        get-spec (requiring-resolve 'clojure.spec.alpha/get-spec)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'demo.core
                                 {:out-dir target :source-paths [source]})
      (is (some? (get-spec :cljs.core.specs.alpha/binding-form))
          "the destructuring spec - what better-cond's own ::binding-form is an s/or over")
      (is (some? (get-spec :cljs.core.specs.alpha/defn-args))
          "the defn spec")
      (is (some? (get-spec :cljs.core.specs.alpha/ns-form))
          "the ns spec, which is the one do-macroexpand-check would reach for first")
      (finally (h/delete-tree! source) (h/delete-tree! target)))))

;; --- fetching what it compiled to --------------------------------------------

(h/deftest-when h/node? test-a-require-fetches-the-namespace-that-was-compiled
  ;; THE BUG THE TWO ALIASED FILES FOUND, and it was older than they are.
  ;;
  ;; (require 'clojure.math) at a REPL compiles cljs/math.cljs, because a clojure.*
  ;; name with no file of its own means the cljs.* one - so what lands on disk is
  ;; ns/cljs/math.js. do-require then told the runtime to fetch the name as TYPED,
  ;; and ns/clojure/math.js is a file nothing ever wrote: the require compiled, the
  ;; vars were there to complete against, and the form came back `Cannot find
  ;; module'. An ns form never had it - the analyzer resolves the same alias while
  ;; it plans the spec - which is why it survived: clojure.test has been reachable
  ;; from a file since the rule existed and from a REPL never.
  (let [src (h/write-sources! {'demo.core "(ns demo.core)"})
        out (h/temp-dir)]
    (try
      (with-open [rt (repl/node-runtime {:dir out :out (StringWriter.)})]
        (let [cenv (env/compile-env {:ns 'cljs.user})
              opts {:out-dir out :source-paths [src]}
              vals #(mapv :value (repl/eval-src cenv rt % opts))]
          (is (= ["nil" "4"] (vals "(require '[clojure.math :as m]) (m/sqrt 16)"))
              "clojure.math")
          ;; and the two halves a fix could have broken by aliasing too much:
          ;; the cljs.* name still means itself, and so does a clojure.* name
          ;; that HAS a file - the rule fires only where nothing does, which is
          ;; what keeps clojure.string out of it (analyzer/aliased-clj-ns).
          (is (= ["nil" "3"] (vals "(require '[cljs.math :as cm]) (cm/floor 3.5)"))
              "cljs.math")
          (is (= ["nil" "\"AB\""] (vals "(require '[clojure.string :as s]) (s/upper-case \"ab\")"))
              "clojure.string")))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))
