;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The vendored cljs/core.cljc and cljs/core.cljs.

  Three things are checked, and they are three different kinds of claim.

  THAT THE VENDORING IS HONEST. core.cljs and support.cljc are byte-for-byte
  ClojureScript's, diffed against the jar. core.cljc is not - it is the one file
  we adapt (doc/cljs-compiler.md §4.4) - so what is checked instead is that every
  line of it we changed is a line we MEANT to change: the jar's copy, put through
  the one mechanical rewrite (the cljs.analyzer alias), differs from ours only in
  the lines listed below. A hunk that appears without being added to that list
  fails, which is the whole point: 3,504 lines of someone else's macros are not a
  file anyone re-reads.

  THAT IT LOADS AND EXPANDS. cljs.core is a JVM namespace of 300-odd macros, and
  every one of them had to resolve at load time before any of them could run - so
  loading is most of the milestone. Then a sample of the macros core.cljs leans on
  hardest are run through the compiler, because a macro that expands into
  something we refuse is no better than one that does not load.

  AND HOW FAR core.cljs GETS. A number, pinned as a floor. It is the honest
  measure of M5 and the only one that cannot be argued with: 946 top-level forms,
  and the test says how many of them compile today. Raising it is the milestone;
  lowering it is a regression.

  See doc/cljs-compiler.md M5."}
  clojure.cljs.core-test
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.cljs.names :as names]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.test-harness :as h]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

;; --- reaching PAST our own copy ----------------------------------------------

(defn- jar-copy
  "The ClojureScript jar's own `path`, as text.

  io/resource would find OURS: src/clj is ahead of the jar on the classpath, and
  our vendored files sit at exactly the paths ClojureScript's occupy. That
  shadowing is deliberate - cljs.core is what a ClojureScript namespace requires,
  and renaming it would only move the collision - but it does mean the oracle has
  to ask for the jar by name."
  [path]
  (some (fn [^java.net.URL u]
          (when (= "jar" (.getProtocol u)) (slurp u)))
        (enumeration-seq
         (.getResources (.getContextClassLoader (Thread/currentThread)) path))))

(def ^:private cljs-jar? (some? (jar-copy "cljs/core.cljc")))

;; --- the vendoring is honest -------------------------------------------------

(defn- declared-in
  "The set of lines an EDN removals file declares, read lazily."
  [resource]
  (delay
    (with-open [r (java.io.PushbackReader. (io/reader (io/resource resource)))]
      (into #{}
            (take-while (complement #{::eof}))
            (repeatedly #(edn/read {:eof ::eof} r))))))

(def ^:private declared-cljs-removals
  "Every line of ClojureScript's core.cljs our copy no longer has.

  79 of them. It was 98 until find-ns came back (§5.48): the \"Bootstrap helpers\"
  block answered for no namespace at all while it addressed goog.global - (find-ns
  'cljs.user) was nil for a namespace that certainly exists - and 19 of its lines
  answer correctly now that find-ns-obj asks the registry cljs-repl.md §3.1 put
  namespaces in.

  What stays gone is what the registry does not make right: the walk and its cache,
  the $macros half there is none of, the three functions that spell a var name with
  cljs.compiler's munge rather than ours, and self-hosting's eval. The removals
  file names each and says why."
  (declared-in "clojure/cljs/core_cljs_removals.edn"))

(def ^:private declared-cljs-additions
  "Every line our core.cljs has that ClojureScript's does not.

  28, of which four are code: the body of find-ns-obj, which is one Map lookup
  where upstream walked goog.global, and the body of find-ns, which is the same
  function minus the cache that walk needed. The other 24 are the comment saying
  so."
  (declared-in "clojure/cljs/core_cljs_additions.edn"))

(h/deftest-when cljs-jar? test-every-difference-from-core-cljs-is-declared
  ;; THIS USED TO BE BYTE EQUALITY. Starting from an unmodified copy was worth a
  ;; great deal while M5 was being built - it made "does core.cljs compile" a
  ;; question about the compiler and nothing else - but it was a scaffold, not a
  ;; requirement, and holding a file that is wrong here because upstream is right
  ;; there is not a property worth keeping. What replaces it is core.cljc's test,
  ;; which is the same property weakened by exactly what is declared and no more:
  ;; every line we dropped is named in a file, and every name in that file is a
  ;; line we really dropped.
  ;;
  ;; THE ADDED HALF USED TO BE EMPTY, and was asserted so. It stopped being empty
  ;; when find-ns came back (§5.48): the namespace registry can answer what
  ;; goog.global could not, but only if something reads it, and the something is
  ;; two function bodies in a file that is otherwise upstream's. So this half is
  ;; now declared rather than forbidden, in the same shape as the other three - and
  ;; the declaration file is where the argument for each added line lives.
  ;;
  ;; §4.4's finding is still why the file can be a near-subset at all:
  ;; core.cljs contains zero literal cljs$lang$ / cljs$core$ names, so the calling
  ;; convention it compiles into is decided entirely by core.cljc.
  (let [theirs (set (str/split-lines (jar-copy "cljs/core.cljs")))
        ours   (set (str/split-lines (slurp (io/resource "cljs/core.cljs"))))]
    ;; One difference is a line PRESENT IN one copy and ABSENT FROM the other, so
    ;; both halves are the same two questions with the two sets swapped.
    (doseq [[label file declared present-in absent-from]
            [["removed" "core_cljs_removals.edn"  @declared-cljs-removals  theirs ours]
             ["added"   "core_cljs_additions.edn" @declared-cljs-additions ours   theirs]]]
      ;; every difference is declared
      (doseq [line (into (sorted-set) (remove absent-from) present-in)]
        (is (contains? declared line)
            (str "core.cljs line " label " but not declared in " file ": "
                 (pr-str line))))
      ;; and every declaration is a difference that is really there, which takes
      ;; BOTH halves of what a difference is. Asking only that the line is absent
      ;; from the other copy lets a declaration name a line neither copy has ever
      ;; had - stale in the way a diff goes stale, and invisible.
      (doseq [line declared]
        (is (contains? present-in line)
            (str file " names a line that is in neither copy - stale: "
                 (pr-str line)))
        (is (not (contains? absent-from line))
            (str file " names a line that is not " label " - stale: "
                 (pr-str line)))))))

(h/deftest-when cljs-jar? test-support-cljc-is-vendored-unmodified
  (is (= (jar-copy "cljs/support.cljc") (slurp (io/resource "cljs/support.cljc")))
      "cljs/support.cljc has been edited - it is six lines and needs nothing from us"))

(deftest test-the-bootstrap-namespace-family-answers-or-says-why-not
  ;; core.cljs carried a block of "Bootstrap helpers" that found a namespace by
  ;; munging its name and walking the segments as properties of goog.global.
  ;; cljs-repl.md §3.1 replaced that addressing scheme with a registry, so every
  ;; one of them answered for no namespace at all. Measured before they went:
  ;;
  ;;   (find-ns 'cljs.user)           => nil
  ;;   (ns-name (find-ns 'cljs.user)) => TypeError on that nil
  ;;   (ns-interns* ...)              => {}
  ;;
  ;; THEY WERE ALL REMOVED, AND MOST OF THEM CAME BACK (§5.48). What made the
  ;; difference is one function: find-ns-obj now reads the registry, and every
  ;; caller of it above was already right. So the split this pins is no longer
  ;; gone/not-gone but ANSWERS/CANNOT ANSWER, which is the same rule stated once
  ;; more - remove what would answer wrongly, keep what answers.
  (let [c (h/core-env)]
    ;; what answers: it resolves like any other cljs.core var, and the node test
    ;; below is where it is actually called
    (doseq [sym '[find-ns find-ns-obj create-ns Namespace ns-name]]
      (is (nil? (h/message #(h/analyze c sym)))
          (str "cljs.core/" sym " no longer resolves")))
    ;; what cannot: a $macros half there is none of, the walk and its cache, and
    ;; self-hosting's eval. Each says why rather than only that it is missing -
    ;; the answer §5.5 gave for goog.Uri: do not do nothing silently.
    (doseq [sym '[find-macros-ns NS_CACHE ns-interns* eval]]
      (let [msg (str (h/message #(h/analyze c sym)))]
        (is (re-find #"was removed from this fork's core.cljs" msg)
            (str "cljs.core/" sym " does not say why it is gone: " msg))))
    ;; qualified too, which is a different error site
    (is (re-find #"was removed from this fork's core.cljs"
                 (str (h/message #(h/analyze c 'cljs.core/eval)))))
    ;; NOT a blanket ban on cljs.core: an ordinary var still resolves
    (is (nil? (h/message #(h/analyze c 'inc))))))

(def ^:private mechanical
  "The one rewrite applied wholesale: cljs.analyzer, in both of the two spellings
  core.cljc uses for it, becomes the `ana` alias - which the ns form points at
  clojure.cljs.analyzer. 58 of the 122 uses are ::ana/numeric and ::ana/no-resolve
  metadata that repointing the alias adapts by itself."
  (fn [^String s]
    (-> s
        (.replace ":cljs.analyzer/" "::ana/")
        (.replace "cljs.analyzer/" "ana/"))))

(def ^:private declared-removals
  "Every line of ClojureScript's core.cljc our copy no longer has, once the
  mechanical rewrite above is accounted for.

  In a file beside this one rather than inline, and that is the point: 206 lines
  do not read as a set literal, but they read very well as a diff. Each belongs to
  an adaptation marked `ADAPTED (M5)` at its site, and the site says why."
  (declared-in "clojure/cljs/core_cljc_removals.edn"))

(h/deftest-when cljs-jar? test-every-adaptation-to-core-cljc-is-declared
  ;; The test that makes "vendored" an honest word for a file we DID edit. It is
  ;; the same property goog_test asserts by byte equality, weakened by exactly the
  ;; amount §4.4 says we have to weaken it - and no more.
  (let [theirs (set (str/split-lines (mechanical (jar-copy "cljs/core.cljc"))))
        ours   (set (str/split-lines (slurp (io/resource "cljs/core.cljc"))))
        gone   (into (sorted-set) (remove ours) theirs)]
    (doseq [line gone]
      (is (contains? @declared-removals line)
          (str "core.cljc line removed but not declared in core_cljc_removals.edn: "
               (pr-str line))))
    ;; BOTH DIRECTIONS, as core.cljs's test does. Checking only that a declared
    ;; line is absent from ours leaves a declaration that is in NEITHER copy
    ;; passing forever - it names nothing, so nothing contradicts it, and the file
    ;; slowly fills with lines that once described an adaptation and now describe
    ;; a file that has moved on.
    (doseq [line @declared-removals]
      (is (contains? theirs line)
          (str "core_cljc_removals.edn names a line that is in neither copy - stale: "
               (pr-str line)))
      (is (not (contains? ours line))
          (str "core_cljc_removals.edn names a line core.cljc still has - stale: "
               (pr-str line))))))

(h/deftest-when cljs-jar? test-our-cljs-core-is-the-one-that-loads
  ;; src/clj comes before the jar on the classpath, and the whole front end
  ;; depends on that staying true.
  (is (not= "jar" (.getProtocol (io/resource "cljs/core.cljc")))
      "the ClojureScript jar's cljs/core.cljc is shadowing ours - check classpath order"))

;; --- it loads, and the macros run --------------------------------------------

(defn- cenv []
  (env/compile-env {:ns 'app.core :core-macros 'cljs.core}))

(defn- js
  "`src` compiled with cljs.core as the macro namespace. One name scope, as
  test-harness/js uses, since every form lands in one JavaScript scope."
  [src]
  (names/with-name-scope
    (let [c (cenv), aenv (env/analysis-env c)]
      (str/join "\n" (mapv #(emitter/emit-top (ana/analyze-top c aenv %))
                           (reader/read-forms c src))))))

(deftest test-cljs-core-loads
  ;; 3,504 lines and 192 macros, and Clojure resolves a var at the moment it
  ;; compiles the form that names it - so this passing means all 25 analyzer and
  ;; compiler names core.cljc reaches for resolve, not merely the ones a test
  ;; happens to exercise.
  (is (nil? (require 'cljs.core)) "cljs.core failed to load")
  (doseq [sym '[when when-not if-not and or cond loop dotimes doto -> ->> str
                defn defn- defmacro defonce declare when-let if-some assert
                lazy-seq this-as case letfn for deftype defprotocol extend-type
                satisfies? instance? identical? aget aset bit-and]]
    (is (some-> (ns-resolve 'cljs.core sym) meta :macro)
        (str "cljs.core/" sym " is not a macro"))))

(deftest test-the-core-macros-expand-and-compile
  ;; A sample, not a sweep. Each of these is a macro core.cljs uses at least once
  ;; per hundred lines, and each expands into forms the analyzer already handles -
  ;; so a failure here is the macro layer, not the milestone.
  ;; Absent, and deliberately: if-not, condp, for, lazy-seq and the rest of the
  ;; macros that expand into a cljs.core VAR rather than into special forms. They
  ;; are not blocked by the macro layer - `(if (not ~x) ...)` is a correct
  ;; expansion - but by cljs.core/not not existing until core.cljs compiles, which
  ;; is the rest of M5. test-how-much-of-core-cljs-compiles is where they count.
  (doseq [src ["(when true 1)"
               "(when-not false 1)"
               "(let [x 1] (when-not (nil? x) x))"
               "(defn f [a b] (+ a b))"
               "(defn g ([a] a) ([a b] b))"
               "(and 1 2 3)"
               "(or nil 2)"
               "(cond true 1 :else 2)"
               "(loop [i 0] (if (< i 3) (recur (inc i)) i))"
               "(dotimes [i 3] (js/console.log i))"
               "(-> 1 inc inc)"
               "(->> 1 inc inc)"
               "(str \"a\" 1)"
               "(defonce x 1)"
               "(declare y)"
               "(when-let [a 1] a)"
               "(if-some [a 1] a 2)"
               "(assert true)"
               "(this-as t t)"
               "(case 1 1 :a :b)"
               "(letfn [(a [] 1)] (a))"
               "(instance? js/Object 1)"
               "(identical? 1 1)"
               "(bit-and 1 2)"
               "(aget (array 1 2) 0)"]]
    (is (string? (js src)) (str "did not compile: " src))))

(deftest test-clojure-core-is-cljs-core
  ;; Every syntax-quote in core.cljc resolves against the JVM, so `(if (not ~x))`
  ;; arrives at the analyzer as clojure.core/not. Nothing else could make if-not
  ;; expand into something that resolves - and this is the one name rewritten.
  (let [c (cenv)]
    (env/add-require! c 'app.core 'cljs.core)
    (intern (env/cljs-ns c 'cljs.core) 'not)
    (is (= 'cljs.core/not
           (:name (ana/analyze-top c (env/analysis-env c) 'clojure.core/not))))
    (testing "and only that one name - clojure.string is not clojure.core"
      ;; nothing here has ever heard of clojure.string, so §5.8 reads it as a
      ;; JavaScript global and warns. What matters to this test is what it did
      ;; NOT become, and cljs.string/join is not it.
      (let [node (atom nil)
            w    (h/warnings #(reset! node (ana/analyze-top c (env/analysis-env c)
                                                            'clojure.string/join)))]
        (is (re-find #"undeclared-ns" w))
        (is (= 'js/clojure.string.join (:name @node)))))
    (testing "an alias still wins, as it does in cljs.analyzer"
      (env/add-require! c 'app.core 'my.core)
      (intern (env/cljs-ns c 'my.core) 'not)
      (.addAlias ^clojure.lang.Namespace (env/cljs-ns c 'app.core)
                 'clojure.core (env/cljs-ns c 'my.core))
      (is (= 'my.core/not
             (:name (ana/analyze-top c (env/analysis-env c) 'clojure.core/not)))))))

;; --- the calling convention, where cljs.core's macros meet core.cljs ----------
;;
;; §5.4's convention is protocols-test's subject and it is tested there, through
;; these same macros. What is left here is the two cases that are about CLJS.CORE
;; rather than about the convention: IFn, the one protocol whose implementation the
;; host itself calls, and reify, which is a deftype minted inside a macro.

(defn- run
  "`src` compiled with cljs.core's macros, beside a COMPILED cljs.core, and run
  under node.

  It used to compile into a namespace called cljs.core in an environment where
  cljs.core was empty, with -write and aclone stubbed in by hand so that deftype's
  own expansion had something to name. Every part of that is gone: §5.12 made
  cljs.core a namespace every other one requires, so a type outside it reaches
  cljs.core/-write like any other var, and h/core-env hands out a namespace inside
  the real thing. What the stubs were standing in for is now under test too."
  [src]
  ;; h/js wraps the LAST form in console.log, and every source below ends in a
  ;; console.log of its own - so node prints one trailing `undefined` for the
  ;; value of that call. Dropped once here rather than expected in every test.
  (str/replace (h/output-with-core (h/core-env) src) #"\nundefined$" ""))

(h/deftest-when h/node? test-a-deftype-can-be-called
  ;; IFn is the one protocol whose implementation the HOST calls: (b 5) emits
  ;; b.call(null, 5), so `call` goes on the prototype and this-as is still
  ;; load-bearing there - the first parameter absorbs that null.
  ;; cljs.core's OWN IFn, reached by the refer half of the implicit require - a
  ;; locally declared protocol that happened to be called IFn would not do, because
  ;; add-ifn-methods tests the resolved name against cljs.core/IFn.
  (is (= "7\n12"
         (run "(deftype Boxed [v]
                 IFn (-invoke [this] v) (-invoke [this a] (+ v a)))
               (def b (Boxed. 7))
               (js/console.log (b))
               (js/console.log (b 5))"))))

(h/deftest-when h/node? test-extend-type-and-reify
  (is (= "1000\nfrom-reify"
         (run "(defprotocol IBox (-unbox [this]))
               (extend-type js/Date IBox (-unbox [this] (.getTime this)))
               (js/console.log (-unbox (js/Date. 1000)))
               (js/console.log (-unbox (reify IBox (-unbox [this] \"from-reify\"))))"))))

(h/deftest-when h/node? test-a-reify-inside-a-method-reaches-the-enclosing-object
  ;; §5.50. reify makes every local in scope a field of the type it mints, and
  ;; inside a deftype method one of those locals is the SELF BINDING - the symbol
  ;; deftype* gives the object its methods are called on. The reify's own deftype
  ;; binds that same symbol, so making it a field was a name collision, and the
  ;; compiler said so and stopped: "A field cannot be named self__2947__auto__".
  ;;
  ;; 58 of one real application's 414 namespaces died of it, all of them behind
  ;; malli, whose -simple-schema returns a reify from inside a schema method.
  ;;
  ;; What the body actually reaches the enclosing object by is the name the USER
  ;; wrote. Both spellings, because they take different routes: `this` is a local
  ;; bound by a let the macro writes, and `x` is a FIELD, whose bare name analyses
  ;; as a property read of the enclosing object - out here, where that object is
  ;; still in scope, and its value is then passed to the reify's constructor.
  (is (= "x=7 this-x=7"
         (run "(defprotocol IReach (-reach [this]))
               (deftype Outer [x]
                 IReach
                 (-reach [this]
                   (reify Object
                     (toString [_] (str \"x=\" x \" this-x=\" (.-x this))))))
               (js/console.log (.toString (-reach (Outer. 7))))"))))

(h/deftest-when h/node? test-a-reify-inside-a-method-copies-the-right-object
  ;; THE ASSERTION THE FIX RESTS ON, and the reason dropping the self binding is
  ;; not merely an economy. reify's -with-meta rebuilds the object with
  ;; (new t <every captured local> meta), and that expression sits INSIDE one of
  ;; the reify's own methods - where the self symbol names THIS object. Had the
  ;; enclosing self stayed a field, the copy would have been handed itself in the
  ;; place where it meant to carry the object it was created inside, and the field
  ;; read below would have gone looking on the wrong one.
  ;;
  ;; So the meta round-trip is the test: x has to survive the copy.
  (is (= "x=7 k=1"
         (run "(defprotocol ICopy (-copy [this]))
               (deftype Outer [x]
                 ICopy
                 (-copy [this] (reify Object (toString [_] (str \"x=\" x)))))
               (def r (with-meta (-copy (Outer. 7)) {:k 1}))
               (js/console.log (str (.toString r) \" k=\" (:k (meta r))))"))))

(h/deftest-when h/node? test-a-reify-nests-in-a-reify-and-in-a-record
  ;; The same shape one level in, where the enclosing self comes from a type the
  ;; reify macro minted rather than one the user wrote
  (is (= "n=3"
         (run "(defprotocol INest (-nest [this]))
               (def outer (let [n 3]
                            (reify INest
                              (-nest [this] (reify Object (toString [_] (str \"n=\" n)))))))
               (js/console.log (.toString (-nest outer)))")))
  ;; and from a defrecord, which is the case that always worked and has to go on
  ;; working. A record mints a self symbol of its own, so the name reify drops is
  ;; not the one in scope here: the record's self is captured, becomes a field,
  ;; and the field is fine - nothing shadows it. NO DEFEAT BITES THIS ONE, which
  ;; is the point of writing it down: it is a guard on a case that passes for a
  ;; different reason than the two above, not a second test of the filter.
  (is (= "x=7"
         (run "(defprotocol INestRec (-nest-rec [this]))
               (defrecord Rec [x]
                 INestRec
                 (-nest-rec [this] (reify Object (toString [_] (str \"x=\" x)))))
               (js/console.log (.toString (-nest-rec (Rec. 7))))"))))

(h/deftest-when h/node? test-find-ns-answers-from-the-registry
  ;; THE MEASUREMENT THE REMOVAL WAS MADE ON, taken again. (find-ns 'cljs.user) was
  ;; nil for a namespace that certainly exists, because find-ns-obj walked munged
  ;; segments off goog.global and nothing has lived there since doc/cljs-repl.md
  ;; §3.1 put namespaces in a registry. find-ns-obj reads that registry now, and
  ;; everything above it in the block is upstream's code unchanged.
  ;;
  ;; cljs.core is the namespace to ask about: it is the one a test program is
  ;; certain to have loaded beside it.
  (is (= "cljs.core\ntrue\nfalse"
         (run "(js/console.log (str (ns-name (find-ns 'cljs.core))))
               (js/console.log (some? (find-ns 'cljs.core)))
               (js/console.log (some? (find-ns 'no.such.namespace)))")))
  ;; AND ASKING DOES NOT CREATE ONE. $CLJS.ns() would have - it is the call every
  ;; module body makes - so the difference between the two is the whole reason
  ;; find-ns-obj reaches for .get, and a second ask is where it would show.
  (is (= "false\nfalse"
         (run "(js/console.log (some? (find-ns 'no.such.namespace)))
               (js/console.log (some? (find-ns 'no.such.namespace)))")))
  ;; A Namespace is by NAME, not by identity: no cache stands behind find-ns any
  ;; more, so two asks give two objects, and -equiv is what makes them the same
  ;; namespace.
  (is (= "true\nfalse"
         (run "(js/console.log (= (find-ns 'cljs.core) (find-ns 'cljs.core)))
               (js/console.log (identical? (find-ns 'cljs.core) (find-ns 'cljs.core)))"))))

;; --- how far core.cljs gets ---------------------------------------------------

(def ^:private core-cljs-floor
  "Top-level forms of core.cljs that compile today. Only ever raised.

  A form that WARNS does not count - see the binding below.

  ALL OF THEM, as of §5.11. It stays a floor rather than becoming an = because the
  two assertions below already bracket it: this one refuses a regression and the
  next refuses a count larger than the file.

  946 until the \"Bootstrap helpers\" and eval were removed, which took eleven
  top-level forms with them - see the removals file. 939 since four of those eleven
  came back (§5.48). The number counts what the file HAS, so it moves when the
  file does."
  939)

(deftest test-how-much-of-core-cljs-compiles
  (let [c     (env/compile-env {:ns 'cljs.core :core-macros 'cljs.core})
        aenv  (env/analysis-env c)
        forms (reader/read-forms c (slurp (io/resource "cljs/core.cljs")))
        ;; A WARNING COUNTS AS A FAILURE HERE, and that is the whole reason each
        ;; form gets its own writer. An unresolvable prefix is a warning in the
        ;; compiler and not an error - Math/floor has to compile (§5.8) - so
        ;; without this a typo in core.cljs would be indistinguishable from a
        ;; clean form and the number below would stop measuring anything. What we
        ;; give real programs is ClojureScript's forgiveness; what we hold this
        ;; file to is the old strictness.
        ok    (names/with-name-scope
                (binding [ana/*cljs-warnings* {:undeclared-var false}]
                  (count (filter (fn [form]
                                   (let [w (java.io.StringWriter.)]
                                     (binding [*err* w]
                                       (try
                                         (emitter/emit-top (ana/analyze-top c aenv form))
                                         (zero? (count (str w)))
                                         (catch Throwable _ false)))))
                                 forms))))]
    (testing "the file reads"
      (is (= 939 (count forms))
          (str "core.cljs no longer has 939 top-level forms - either the jar"
               " version moved, or something was removed from our copy without"
               " moving this number and core-cljs-floor with it")))
    (testing "and this much of it compiles"
      (is (>= ok core-cljs-floor)
          (str "core.cljs regressed: " ok " forms compile, was " core-cljs-floor))
      (is (<= ok 939)))))

;; --- what the collection literals unblocked ----------------------------------

(h/deftest-when h/node? test-a-type-outside-cljs-core-needs-nothing-declared
  ;; Two things stood between deftype and a namespace of its own: getBasis returns
  ;; a quoted vector, which the collection literals unblocked (§5.7), and the
  ;; expansion names cljs.core/-write, so cljs.core has to RESOLVE - which §5.9's
  ;; naming half now makes it do from anywhere, with no :require written down.
  ;;
  ;; What is still supplied by hand is the two VARS, because this environment has
  ;; no compiled cljs.core in it. A real build has, and the point of the test is
  ;; how little else is needed.
  (let [c (env/compile-env {:ns 'app.core :core-macros 'cljs.core})]
    (doseq [sym '[-write aclone]] (intern (env/cljs-ns c 'cljs.core) sym))
    (let [js (h/js c "(defprotocol IShape (-area [this]))
                      (deftype Point [x y] IShape (-area [this] (* x y)))
                      (js/console.log (.-cljs$lang$ctorStr Point))")]
      ;; the basis is a vector of quoted symbols, built by cljs.core - and since
      ;; §5.10 a quoted symbol is a cljs.core allocation too, so the basis names
      ;; two of its types rather than one
      (is (str/includes? js "cljs$core$ns.PersistentVector(null, 2, 5") js)
      (is (str/includes? js "(new cljs$core$ns.Symbol(null, \"x\", \"x\", ") js)
      (is (str/includes? js "(new cljs$core$ns.Symbol(null, \"y\", \"y\", ") js)
      ;; and the one name that still needs the require
      (is (str/includes? js "cljs$core$ns._write") js)))
  ;; and without those two vars, the VAR is what is missing - the namespace is
  ;; found, which is the whole of what §5.9's naming half changed here
  (let [c (env/compile-env {:ns 'app.core :core-macros 'cljs.core})]
    (is (re-find #"No such var: cljs.core/-write"
                 (h/message #(h/js c "(defprotocol IShape (-area [this]))
                                      (deftype Point [x y] IShape (-area [this] 1))"))))))

;; --- what str compiles into --------------------------------------------------

(deftest test-str-names-a-var-rather-than-a-global-path
  ;; ClojureScript's str macro writes cljs.core.str_ into a js* template as TEXT -
  ;; the global path a ClojureScript var has and ours does not. Ours puts the name
  ;; through a ~{} hole and lets the compiler spell it, which is the only spelling
  ;; that can be right in both targets (doc/cljs-compiler.md §5.9).
  (let [c (cenv)]
    ;; str is a var of cljs.core, and this environment has no compiled one
    (intern (env/cljs-ns c 'cljs.core) 'str)
    (names/with-name-scope
      (let [aenv (env/analysis-env c)
            out  (str/join "\n" (mapv #(emitter/emit-top (ana/analyze-top c aenv %))
                                      (reader/read-forms c "(def x 1)
                                                            (def a (str x))
                                                            (def b (str_ x))")))]
        (is (not (str/includes? out "cljs.core.str")) out)
        ;; a property of the namespace object, munged our way
        (is (str/includes? out "cljs$core$ns.str.cljs$core$IFn$_invoke$arity$1") out)
        ;; and str_ resolves with nothing interned at all, because the macro tags
        ;; the name ::ana/no-resolve - core.cljs uses str_ three thousand lines
        ;; before it defines it
        (is (str/includes? out "cljs$core$ns.str$US$") out))))
  ;; a constant needs no call in either target, and still does not
  (is (= "app$core$ns.s = (\"\"+(1)+\"a\"+(2));" (js "(def s (str 1 \"a\" 2))"))))

;; --- keywords and symbols are values -----------------------------------------
;;
;; doc/cljs-compiler.md §5.10. The last placeholder: a keyword used to emit as the
;; string naming it, and now emits as an allocation of cljs.core/Keyword. What that
;; buys is everything downstream of a keyword being a VALUE - printing above all,
;; since core.cljs's printer dispatches on the type it now really is.

(deftest test-a-keyword-is-an-allocation
  (is (= "app$core$ns.k = (new cljs$core$ns.Keyword(null, \"a\", \"a\", (-2123407586)));"
         (js "(def k :a)")))
  ;; a namespaced keyword carries all three spellings, because fqn is what name,
  ;; namespace and toString are read off and rebuilding it per call would cost more
  ;; than the string does
  (is (= "app$core$ns.k = (new cljs$core$ns.Keyword(\"x\", \"a\", \"x/a\", (-2123407450)));"
         (js "(def k :x/a)")))
  ;; a symbol takes a trailing null for its metadata, which a QUOTED symbol never
  ;; has: quote does not walk what it quotes
  (is (= "app$core$ns.s = (new cljs$core$ns.Symbol(null, \"a\", \"a\", (-482876059), null));"
         (js "(def s (quote a))"))))

(deftest test-the-hash-is-computed-here
  ;; THE ONE THING THAT MAKES BAKING A HASH IN SOUND. The literal carries a number
  ;; computed on the JVM; a keyword the program builds at run time computes its own
  ;; in JavaScript. If those two ever disagreed the symptom would be a map that has
  ;; a key and cannot find it, so the agreement is pinned rather than assumed - and
  ;; pinned on both sides, here against the JVM and below against node.
  (are [x expected] (= expected (hash x))
    :a        -2123407586
    :foo/bar  -1386151538
    'a        -482876059
    'foo/bar   254379989))

(h/deftest-when h/node? test-a-keyword-is-the-same-value-however-it-is-made
  ;; the other side of the hash: what the compiler baked in and what cljs.core
  ;; computes are one number, so a literal and a built keyword are one map key
  (are [src expected] (= expected (h/output-with-core src))
    "(cljs.core/= :a (cljs.core/keyword \"a\"))"                    "true"
    "(cljs.core/= :x/a (cljs.core/keyword \"x\" \"a\"))"            "true"
    "(cljs.core/hash :a)"                                           "-2123407586"
    "(cljs.core/hash (cljs.core/keyword \"a\"))"                    "-2123407586"
    "(cljs.core/hash (quote foo/bar))"                              "254379989"
    ;; the point of all of it: a literal key found by a built one
    "(cljs.core/get {:a 1} (cljs.core/keyword \"a\"))"              "1"
    ;; and past PersistentArrayMap's threshold, where the hash is what does the
    ;; finding rather than a linear scan over =
    "(cljs.core/get {:a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i 9} (cljs.core/keyword \"i\"))" "9"))

(h/deftest-when h/node? test-a-program-prints-itself
  ;; pr-str, which is what the placeholder blocked: core.cljs calls a keyword as a
  ;; function, and a string is not callable. Everything here is our compiler's
  ;; output run against our compiled cljs.core - the read-analyze-emit-load path
  ;; end to end.
  (are [src expected] (= expected (h/output-with-core (str "(cljs.core/pr-str " src ")")))
    ":a"                    ":a"
    ":x/a"                  ":x/a"
    "(quote a)"             "a"
    "(quote x/a)"           "x/a"
    "[:a 1 \"s\"]"          "[:a 1 \"s\"]"
    "{:a 1 :b/c 2}"         "{:a 1, :b/c 2}"
    "#{:a}"                 "#{:a}"
    "(quote (1 :b c))"      "(1 :b c)"
    ;; nested, because a constant is one expression however deep it goes
    "{:a [:b {:c (quote d)}]}" "{:a [:b {:c d}]}")
  ;; and a keyword is a function of a map, which is the call that used to throw
  (is (= "1" (h/output-with-core "(:a {:a 1})")))
  ;; a string and the keyword naming it are two values now, which is the one way
  ;; the placeholder was observably wrong
  (is (= "false" (h/output-with-core "(cljs.core/= :a \"a\")"))))

;; --- the last two forms -------------------------------------------------------
;;
;; doc/cljs-compiler.md §5.11. What kept core.cljs at 944 was one name written with
;; dots instead of a slash, and one set! target the list did not have.

(deftest test-a-dotted-symbol-is-a-name-in-one-piece
  ;; the LAST dot splits a namespace from a name, so cljs.core.Var is cljs.core/Var
  ;; - and unchecked, which is what lets core.cljs write (instance? cljs.core.Var v)
  ;; at line 1162 and define Var at 1186
  (is (str/includes? (js "(def v 1) (def x (instance? cljs.core.Var v))")
                     "(app$core$ns.v instanceof cljs$core$ns.Var)"))
  ;; the FIRST dot splits a value from its properties when the head names one, and
  ;; a local wins over any namespace of the same name
  (is (str/includes? (js "(let* [p 1] p.a.b)") "p__1.a.b"))
  ;; a prefix nothing knows is a JavaScript global, exactly as Foo/bar is (§5.8)
  (let [c (cenv)]
    (is (str/includes? (h/warnings #(h/js c "(def x Foo.Bar.baz)")) "undeclared-ns"))
    (is (str/includes? (h/warnings #(h/js c "(def x Foo.Bar.baz)")) "Foo.Bar.baz")))
  ;; and a goog provide is named in full rather than SPLIT, because it is one name
  ;; and not a var called Long in a namespace called goog.math. Writing it out is
  ;; the require (doc/cljs-compiler.md §5.18), so what proves it was not split is
  ;; the name in the output.
  (let [c (cenv)]
    (is (str/includes? (h/js c "(def x goog.math.Long)")
                       "$ns(\"goog.math.Long\")"))))

(deftest test-a-goog-var-is-a-set-target
  ;; goog/global emits goog$ns.global, and $ns("goog") IS the goog object once
  ;; base.js has run - so this is a property assignment like any other
  (let [c (env/compile-env {:ns 'cljs.core :core-macros 'cljs.core})]
    (env/add-require! c 'cljs.core 'goog)
    (is (str/includes? (h/js c "(set! goog/global js/global)")
                       "(goog$ns.global = global)")))
  ;; and the refusals it did not loosen
  (is (re-find #"a local is immutable" (h/message #(js "(let* [a 1] (set! a 2))"))))
  (is (re-find #"must be a var or a property access" (h/message #(js "(set! 1 2)")))))

(h/deftest-when h/node? test-all-of-core-cljs-loads
  ;; the whole file now, with nothing skipped - which is what the fixture asserts by
  ;; not catching anything. var? is the form §5.11 added and the one worth running.
  (are [src expected] (= expected (h/output-with-core src))
    "(cljs.core/var? 1)"                                   "false"
    "(cljs.core/var? (cljs.core/Var. (fn* [] 1) (quote x) nil))" "true"
    ;; js/COMPILED is a bare identifier the prelude defines, since an ES module
    ;; cannot make one global the way Closure's base.js does with a top-level var
    "js/COMPILED"                                          "false"))

;; --- the implicit require, referred -------------------------------------------
;;
;; doc/cljs-compiler.md §5.12. An unqualified `reduce` means cljs.core/reduce, in
;; every namespace, whether or not it said so.

(deftest test-cljs-core-is-referred-into-every-namespace
  (let [c (cenv)]
    (intern (env/cljs-ns c 'cljs.core) 'reduce)
    (is (= 'cljs.core/reduce (:name (h/analyze c 'reduce))))
    ;; and it emits as a property of cljs.core's object, like any other var
    (is (str/includes? (h/js c "(def r reduce)") "cljs$core$ns.reduce")))

  ;; A DEF OF THIS NAMESPACE'S OWN WINS, because it is asked first - as it is in
  ;; Clojure, where (def reduce ...) shadows the core one
  (let [c (cenv)]
    (intern (env/cljs-ns c 'cljs.core) 'reduce)
    (h/analyze c '(def reduce 1))
    (is (= 'app.core/reduce (:name (h/analyze c 'reduce))))
    (is (str/includes? (h/js c "(def reduce 1) (def r reduce)")
                       "app$core$ns.r = app$core$ns.reduce")))

  ;; :refer-clojure :exclude is the other way to say the same thing, and it was
  ;; recorded long before there were core vars for it to hide (env/excluded?)
  (let [c (cenv)]
    (intern (env/cljs-ns c 'cljs.core) 'reduce)
    (h/analyze c '(ns app.core (:refer-clojure :exclude [reduce])))
    (is (re-find #"neither a local nor a var" (h/message #(h/analyze c 'reduce)))))

  ;; a var that is not there is still not there
  (is (re-find #"neither a local nor a var"
               (h/message #(h/analyze (cenv) 'no-such-core-var))))

  ;; and cljs.core does not refer itself - it finds its own vars as its own
  (let [c (env/compile-env {:ns 'cljs.core})]
    (intern (env/cljs-ns c 'cljs.core) 'reduce)
    (is (= 'cljs.core/reduce (:name (h/analyze c 'reduce))))))

(h/deftest-when h/node? test-an-unqualified-core-name-runs
  ;; the same thing end to end, with the real cljs.core behind it
  (are [src expected] (= expected (h/output-with-core src))
    "(reduce + [1 2 3])"          "6"
    "(pr-str (map inc [1 2]))"    "(2 3)"
    "(first (vals {:a 1}))"       "1"
    "(str \"a\" :b 1)"            "a:b1"))

;; --- the cljs global --------------------------------------------------------

(h/deftest-when h/node? test-the-cljs-global-is-the-real-namespace-object
  ;; 5.60. runtime.js publishes globalThis.cljs, which is the object a
  ;; goog.provide build makes and this compiler otherwise does not. Nothing we
  ;; emit reads it; cljs-bean does, and 339 of nosco-gamma's 684 modules stop
  ;; there without it.
  (testing "a read finds the real type, not a copy of it"
    (is (= "true"
           (h/output-with-core
            (h/core-env 'app.glob)
            (str "(cljs.core/pr-str (identical? (.. js/cljs -core -PersistentArrayMap -EMPTY)"
                 " cljs.core/PersistentArrayMap.EMPTY))")))))
  (testing "and a WRITE through it lands on the real type"
    ;; which is the half a synthesised object would get silently wrong, and which
    ;; cljs-bean does on purpose - it replaces the empty map to make ->clj's
    ;; result the default one
    (is (= "true"
           (h/output-with-core
            (h/core-env 'app.glob2)
            (str "(set! (.. js/cljs -core -PersistentArrayMap -EMPTY) 42)"
                 " (cljs.core/pr-str (identical? 42 cljs.core/PersistentArrayMap.EMPTY))")))))
  (testing "and on the NAMESPACE OBJECT, which the read above cannot tell"
    ;; PersistentArrayMap is the same object in a copy of the namespace as in the
    ;; namespace, so setting a property OF IT proves nothing about `core` itself -
    ;; a shallow copy passes that assertion. Writing a new name is the one that
    ;; separates them, because exists? reads $ns("cljs.core") directly: through a
    ;; view the write is there, through a copy it went somewhere else and is lost.
    (is (= "true"
           (h/output-with-core
            (h/core-env 'app.glob3)
            (str "(set! (.. js/cljs -core -brandnew) 42)"
                 " (cljs.core/pr-str (cljs.core/exists? cljs.core/brandnew))"))))))

;; --- exists? -----------------------------------------------------------------

(deftest test-exists-asks-the-question-this-compiler-can-answer
  ;; Three questions wearing one name, and ClojureScript answers all three with the
  ;; same expression because all three are a global path there. Here they are three
  ;; (doc/cljs-compiler.md §5.26).
  (let [cenv (h/core-env 'app.ex)]
    (testing "a ClojureScript var is a property of a namespace object"
      (let [js (h/js cenv "(cljs.core/exists? cljs.core/map)")]
        (is (str/includes? js "(void 0 !== $ns(\"cljs.core\")[\"map\"])") js)
        ;; the walk that used to be here answered false for EVERY var in the tree
        (is (not (str/includes? js "typeof cljs")) js)))

    (testing "a js/ name keeps the walk, because it really is a path"
      (let [js (h/js cenv "(cljs.core/exists? js/Math.floor)")]
        (is (str/includes? js "(typeof Math !== 'undefined')") js)
        (is (str/includes? js "(typeof Math.floor !== 'undefined')") js)))

    (testing "a dotted name that is not a var is a NAMESPACE"
      ;; how cljs.spec.test.alpha/check asks whether test.check was loaded
      (let [js (h/js cenv "(cljs.core/exists? clojure.test.check)")]
        (is (str/includes? js "$CLJS.loaded.has(\"clojure.test.check\")") js)))

    (testing "and a qualified name in a namespace nobody required is still a var"
      ;; cljs.spec.gen.alpha/dynaload reaches one on purpose
      (let [js (h/js cenv "(cljs.core/exists? clojure.test.check.generators/foo)")]
        (is (str/includes? js "(void 0 !== $ns(\"clojure.test.check.generators\")[\"foo\"])") js)))

    (testing "a qualified name whose NAME half has dots is a path INTO the var"
      ;; 5.59. cljs-ajax writes (exists? goog/global.XMLHttpRequest) on one line
      ;; and goog/global.XMLHttpRequest on the next, and the two disagreed: the
      ;; value was a member chain and the test was a single property called
      ;; "global.XMLHttpRequest", which nothing has. So the answer was FALSE
      ;; whatever was there, and cljs-ajax took its no-XMLHttpRequest branch in a
      ;; browser that has one - silently, which is the whole complaint.
      (let [js (h/js cenv "(cljs.core/exists? goog/global.XMLHttpRequest)")]
        (is (str/includes? js "$ns(\"goog\")[\"global\"][\"XMLHttpRequest\"]") js)
        (is (not (str/includes? js "\"global.XMLHttpRequest\"")) js)
        ;; WALKED, a segment at a time, for the reason the js/ branch walks:
        ;; reading a property of undefined throws, and exists? is the question
        ;; asked when you do not know that it is not
        (is (str/includes? js "(void 0 !== $ns(\"goog\")[\"global\"]) &&") js)))

    (testing "a dotted name that IS a var is the var, not a namespace"
      ;; §5.29. cljs.core.first and clojure.test.check are the same SHAPE - a
      ;; simple symbol with dots - and one is a var. env/dotted-var-sym splits it
      ;; the way the analyzer splits it, so the two questions cannot drift apart.
      ;; cljs/core_test.cljs writes (exists? cljs.core.first) and wants true.
      (let [js (h/js cenv "(cljs.core/exists? cljs.core.first)")]
        (is (str/includes? js "(void 0 !== $ns(\"cljs.core\")[\"first\"])") js)
        (is (not (str/includes? js "loaded.has")) js))
      ;; and a dotted name that resolves to nothing is still the namespace question
      (let [js (h/js cenv "(cljs.core/exists? cljs.core.no-such-var)")]
        (is (str/includes? js "$CLJS.loaded.has(\"cljs.core.no-such-var\")") js)))))

(h/deftest-when h/node? test-exists-runs
  (is (= "true"  (h/output-with-core (h/core-env) "(cljs.core/exists? cljs.core/map)")))
  (is (= "false" (h/output-with-core (h/core-env) "(cljs.core/exists? cljs.core/nope-not-here)")))
  (is (= "true"  (h/output-with-core (h/core-env) "(cljs.core/exists? js/Math)")))
  (is (= "false" (h/output-with-core (h/core-env) "(cljs.core/exists? js/NoSuchGlobal)")))
  ;; cljs.core is loaded in every program; nothing loads this one
  (is (= "true"  (h/output-with-core (h/core-env) "(cljs.core/exists? cljs.core)")))
  (is (= "false" (h/output-with-core (h/core-env) "(cljs.core/exists? no.such.namespace)")))
  ;; a def of this namespace's own
  (is (= "true"  (h/output-with-core (h/core-env 'app.ex3)
                                     "(def q 1) (cljs.core/exists? q)")))
  ;; §5.29: a var spelled with dots
  (is (= "true"  (h/output-with-core (h/core-env) "(cljs.core/exists? cljs.core.first)")))
  (is (= "false" (h/output-with-core (h/core-env) "(cljs.core/exists? cljs.core.nope)")))
  ;; §5.59: a property path INTO a var - and the missing prefix, which is the
  ;; reason the walk exists at all: reading .a of undefined is a TypeError, and
  ;; the answer wanted is false
  (is (= "true"  (h/output-with-core (h/core-env 'app.ex4)
                                     "(def o #js {:a 1}) (cljs.core/exists? app.ex4/o.a)")))
  (is (= "false" (h/output-with-core (h/core-env 'app.ex5)
                                     "(def o #js {:a 1}) (cljs.core/exists? app.ex5/o.b)")))
  (is (= "false" (h/output-with-core (h/core-env 'app.ex6)
                                     "(def o #js {:a 1}) (cljs.core/exists? app.ex6/missing.a)"))))

(h/deftest-when h/node? test-ns-imports-runs
  ;; §5.30. cljs.core's own (:import [goog.string StringBuffer]), read back at
  ;; runtime: the bare class name to the CLASS, not to a symbol naming it. This
  ;; used to hand back an empty map, because an :import applied as a require plus
  ;; an alias and nothing kept the pair - see clojure.cljs.env/add-imports!.
  ;; cljs/core_test.cljs asks for it as test-cljs-2184.
  (is (= "true" (h/output-with-core
                 (h/core-env)
                 "(contains? (ns-imports 'cljs.core) 'StringBuffer)")))
  (is (= "true" (h/output-with-core
                 (h/core-env)
                 "(= (find (ns-imports 'cljs.core) 'StringBuffer)
                     ['StringBuffer goog.string.StringBuffer])")))
  ;; a namespace that imported nothing, and one that does not exist: both empty,
  ;; and asking about the second creates nothing
  (is (= "true" (h/output-with-core
                 (h/core-env 'app.ni1)
                 "(= {} (ns-imports 'app.ni1))")))
  (is (= "true" (h/output-with-core
                 (h/core-env) "(= {} (ns-imports 'no.such.namespace))"))))

(h/deftest-when h/node? test-a-def-of-a-core-name-runs
  ;; §5.32, end to end. cljs/extend_to_native_test.cljs asks for it as
  ;; test-protocol-with-slash: a protocol method named / was interned and resolved
  ;; correctly all along, and (/ "") still emitted ((1) / "") - because cljs.core's
  ;; `/` MACRO expands before anything is resolved.
  (is (= "[\"result\" 2]"
         (h/output-with-core
          (h/core-env 'app.cn1)
          "(defprotocol Slashy (/ [_]))
           (extend-type string Slashy (/ [_] \"result\"))
           (pr-str [(/ \"\") (cljs.core// 6 3)])")))
  ;; and a name that shadows a core macro of any other shape
  (is (= "[:mine 2]"
         (h/output-with-core
          (h/core-env 'app.cn2)
          "(defprotocol P (count [_]))
           (extend-type string P (count [_] :mine))
           (pr-str [(count \"ab\") (cljs.core/count \"ab\")])")))
  ;; a namespace that defines neither is untouched
  (is (= "[2 2]"
         (h/output-with-core (h/core-env 'app.cn3)
                             "(pr-str [(/ 6 3) (count [1 2])])"))))

(h/deftest-when h/node? test-a-boolean-tag-runs
  ;; §5.32, and the assertion that says why a tag cannot be guessed:
  ;; cljs/binding_test.cljs binds the same var to "" twice, once ^boolean and once
  ;; not, and expects DIFFERENT answers - truth_("") is true, `if ("")` is false.
  ;; test-tag-inference, verbatim.
  (is (= "[2 1 1 2 1 2]"
         (h/output-with-core
          (h/core-env 'app.bt1)
          "(def ^:dynamic *foo* false)
           (def ^:dynamic ^boolean *foo-tagged* false)
           (defn bar [] (if *foo* 1 2))
           (defn bar-tagged [] (if *foo-tagged* 1 2))
           (pr-str [(bar) (binding [*foo* \"abc\"] (bar)) (binding [*foo* \"\"] (bar))
                    (bar-tagged) (binding [*foo-tagged* \"abc\"] (bar-tagged))
                    (binding [*foo-tagged* \"\"] (bar-tagged))])")))
  ;; the predicates cljs.core inlines still answer correctly, which is what the
  ;; js* half of the tag has to leave alone
  (is (= "[true false true false]"
         (h/output-with-core
          (h/core-env 'app.bt2)
          "(pr-str [(if (nil? nil) true false) (if (nil? 0) true false)
                    (if (identical? 1 1) true false) (if (== 1 2) true false)])"))))

(h/deftest-when h/node? test-extend-via-metadata-runs
  ;; §5.31. A protocol declared :extend-via-metadata true looks for an
  ;; implementation in the VALUE'S metadata, under the method's qualified name,
  ;; before it looks for a property. clojure.core.protocols/Datafiable and
  ;; Navigable are declared that way, which is what clojure/datafy_test.cljs asks
  ;; for; cljs/core_test.cljs asks for it as test-cljs-2960.
  (is (= "[:num :meta]"
         (h/output-with-core
          (h/core-env 'app.evm1)
          "(defprotocol P :extend-via-metadata true (m [_]))
           (extend-type number P (m [_] :num))
           (pr-str [(m 1) (m (with-meta {} {'app.evm1/m (fn [_] :meta)}))])")))
  ;; METADATA FIRST, which is the order cljs.analyzer's expansion has: a value
  ;; that both implements the protocol and carries an implementation in its
  ;; metadata gets the one from the metadata
  (is (= "[:vec :meta]"
         (h/output-with-core
          (h/core-env 'app.evm2)
          "(defprotocol P :extend-via-metadata true (m [_]))
           (extend-type PersistentVector P (m [_] :vec))
           (pr-str [(m []) (m (with-meta [] {'app.evm2/m (fn [_] :meta)}))])"))))

(deftest test-a-protocol-that-does-not-ask-for-metadata-pays-nothing
  ;; the whole of why §5.31 could restore what M5 removed. The branch is decided
  ;; while the protocol is being DEFINED, from that protocol's own option - so the
  ;; dispatch of a protocol that does not ask for it is emitted unchanged, and
  ;; cljs.core's own protocols carry no lookup. M5 dropped the feature on the
  ;; opposite premise, that it would cost every protocol call in the program.
  (let [plain  (h/js (h/core-env 'app.evm3) "(defprotocol Q (q [_]))")
        opted  (h/js (h/core-env 'app.evm4)
                     "(defprotocol P :extend-via-metadata true (m [_]))")]
    (is (not (str/includes? plain "cljs$core$ns.meta")))
    (is (str/includes? opted "cljs$core$ns.meta"))
    ;; and what plain emits is still the one js* conditional §5.4 argued for
    (is (str/includes? plain "$CLJS.nativeImpl"))))

(h/deftest-when h/node? test-metadata-on-a-fn-runs
  ;; §5.30. A function is a value a program hangs metadata on and reads back;
  ;; parse-fn wraps its node like any other literal's. cljs/core_test.cljs asks for
  ;; it as test-853.
  (is (= "{:foo true}" (h/output-with-core (h/core-env)
                                           "(pr-str (meta ^:foo (fn [])))")))
  (is (= "nil"         (h/output-with-core (h/core-env) "(pr-str (meta (fn [])))")))
  ;; still callable: with-meta on a function is cljs.core/MetaFn
  (is (= "5"           (h/output-with-core (h/core-env) "((^:foo fn [x] x) 5)")))
  (is (= "3"           (h/output-with-core (h/core-env)
                                           "((^:x fn ([] 1) ([a] a)) 3)")))
  ;; the metadata is a map literal like any other, so a value in it is evaluated
  (is (= "{:bar 2}"    (h/output-with-core (h/core-env)
                                           "(pr-str (meta ^{:bar (inc 1)} (fn [] 1)))")))
  ;; and the three keys cljs.core/dt->et puts on every protocol method are the
  ;; annotator's rather than the program's, so a deftype still builds
  (is (= "42" (h/output-with-core (h/core-env 'app.mf1)
                                  "(defprotocol P (m [_])) (deftype T [] P (m [_] 42)) (m (T.))"))))

(h/deftest-when h/node? test-static-arity-dispatch-runs
  ;; §5.33. The emitter test says what the call site SPELLS; this says the program
  ;; still means the same thing - every arity of a multi-arity function, a rest
  ;; arity with and without extra arguments, and apply, which goes nowhere near a
  ;; static call site and must keep agreeing with one.
  ;;
  ;; Bound on, because §5.44 turned it off by default: this is what an optimized
  ;; compilation emits, and everything here is a statement about that mode.
  (binding [emitter/*static-dispatch* true]
    (is (= "[[:1 1] [:2 1 2] [:n 1 2 (3 4)] [:n 1 2 (3)] [1 nil] [1 (2 3)] [:2 1 2] [:n 1 2 (3)]]"
           (h/output-with-core
            (h/core-env 'app.sd1)
            "(defn foo ([x] [:1 x]) ([x y] [:2 x y]) ([x y & z] [:n x y z]))
             (defn bar [a & xs] [a xs])
             (pr-str [(foo 1) (foo 1 2) (foo 1 2 3 4) (foo 1 2 3)
                      (bar 1) (bar 1 2 3)
                      (apply foo [1 2]) (apply foo 1 2 [3])])")))

    (testing "an arity the function does not have still throws, and says so"
      (is (= "\"Invalid arity: 3\""
             (h/output-with-core
              (h/core-env 'app.sd2)
              "(defn two ([x] x) ([x y] y))
               (pr-str (try (two 1 2 3) (catch js/Error e (.-message e))))"))))

    (testing "a redefinition is seen, because the var is still read at call time"
      ;; the property is read off whatever the var holds NOW - which is the whole
      ;; reason a var is a property of a namespace object (§5.2). A static call site
      ;; pins the ARITY, not the function.
      (is (= "[2 20]"
             (h/output-with-core
              (h/core-env 'app.sd3)
              "(defn two ([x] x) ([x y] y))
               (defn use-it [] (two 1 2))
               (def before (use-it))
               (defn two ([x] x) ([x y] (* 10 y)))
               (pr-str [before (use-it)])"))))

    (testing "and what it pins is the arity, which is why the REPL does not pin it"
      ;; THE LIMIT OF STATIC DISPATCH, asserted rather than described. A call site
      ;; compiled against a two-arity function names arity 2; replace the function
      ;; with one that has no arity properties at all - an ordinary fn does not -
      ;; and the old call site is naming something that is no longer there.
      ;; ClojureScript behaves identically, and both answer it the same way: static
      ;; dispatch is off unless a build asks for it (§5.44), so nothing compiled the
      ;; ordinary way - a file or a REPL input alike - can reach this at all. It is
      ;; the price of the mode, asserted here so the price stays known.
      (is (str/includes?
           (h/output-with-core
            (h/core-env 'app.sd4)
            "(defn two ([x] x) ([x y] y))
             (defn use-it [] (two 1 2))
             (set! two (fn [x y] (* 10 y)))
             (pr-str (use-it))")
           "is not a function"))

      ;; but a set! IS seen by the call sites compiled after it, which is the half
      ;; the analyzer can answer: the shape goes away with the function
      (is (= "20"
             (h/output-with-core
              (h/core-env 'app.sd5)
              "(defn two ([x] x) ([x y] y))
               (set! two (fn [x y] (* 10 y)))
               (pr-str (two 1 2))"))))))
