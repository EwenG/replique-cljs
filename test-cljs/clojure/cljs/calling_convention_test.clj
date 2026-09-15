;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The calling convention, tested generatively rather than by example.

  Three of this compiler's bugs have been the same bug: THE ENTRY POINT AND THE
  BODY DISAGREED ABOUT THE SHAPE OF THE FUNCTION.

    §5.33  set! on a var dropped :top-fn, so a call site kept naming an arity the
           var no longer had
    §5.35  a fn read its own public entry point to find its body, and instrument
           replaces that entry point
    §5.36  a variadic body reached through a delegate lost its receiver, so
           this-as in a deftype's IFn method saw undefined

  Each was found by luck or by an upstream regression test for a bug that was not
  ours. That is a bad way to find the third instance of anything, so the shapes are
  generated here instead: a random set of fixed arities, optionally a variadic tail,
  called every way it can be called.

  THE THREE PROPERTIES. For every shape, and every arity it answers:

    1. STATIC DISPATCH ON == STATIC DISPATCH OFF. The same source compiled both
       ways prints the same thing. No external oracle - the compiler is checked
       against itself, which is what makes this cheap.
    2. == JVM CLOJURE. The same shape as a Clojure fn, applied the same ways,
       printed with the same pr-str. Free, because the generated vocabulary was
       chosen to mean the same thing in both languages.
    3. apply == a DIRECT CALL, in both spellings - (apply f [a b]) and
       (apply f a [b]).

  WHY 1 IS WORTH MORE THAN IT LOOKS, AND MORE SINCE §5.44. It used to be that
  emitter/*static-dispatch* defaulted to TRUE, so every file-compiled test there was
  exercised the static path and FALSE had only repl-test and browser-test - which
  are about loading and reload rather than about calling. §5.44 reversed the
  default: static dispatch belongs to optimized compilation and nothing in an
  ordinary compile turns it on. So the asymmetry runs the other way now, and this
  property is not a supplement to the static path's coverage - it is most of it.

  BOTH SIDES ARE BOUND EXPLICITLY below for that reason. Taking either from the
  default would make the property compare a mode with itself, which is a test that
  passes and says nothing.

  WHAT THE GENERATOR DELIBERATELY REACHES. Twenty parameters, which is Clojure's
  own limit and so the most the oracle can express; and calls carrying more than
  twenty ARGUMENTS through a variadic tail, which is a different boundary - it is
  where cljs.core/apply stops having a fixed arity to hand off to.

  WHERE PROPERTY 1 IS VACUOUS, AND IT IS NOT A GAP. arity-target answers nil for a
  shape with ONE method, because core.cljc sets no arity property on a function
  that has only one - so a single-arity defn is emitted as f.call(null, x) whether
  static dispatch is on or off, and the two agree trivially. About a quarter of
  generated shapes are that; the other three quarters have two or more methods and
  are the ones property 1 is about. Properties 2 and 3 bite on all of them.

  Shrinking is the instrument here. A failure arrives as a minimal shape, and the
  report below carries the source and both outputs with it - so diagnosis is a diff
  of two JavaScript programs on the JVM, with no runtime involved.

  CHECKED FOR TEETH, because a property test that cannot fail is worse than none.
  An off-by-one was injected into emitter/arity-target and the property failed on
  the first shape; narrowed to lie only about non-variadic multi-method shapes, the
  minimal witness reads

    on  THREW: app$t3$ns.f.cljs$core$IFn$_invoke$arity$2 is not a function
    off THREW: Invalid arity: 2

  which is §5.33's failure mode exactly: the static call site naming an arity that
  the function does not have, where the dispatch function would have said so.

  REDEFINITION IS A FOURTH PROPERTY, AND IT NEEDED A SEQUENCE. The three above are
  each about ONE definition, so none of them can reach §5.33's bug - a call site
  outliving the shape it named. That one takes two definitions and a caller
  compiled between them:

    (defn f <A>) / (defn g [] <calls>) / (g) / redefine f as <B> / (g)

  and what it asserts is that WHEN g WAS COMPILED DOES NOT MATTER: g answers what a
  caller compiled after the redefinition answers, and both answer what JVM Clojure
  answers for shape B. Both routes a var's value changes are generated - defn,
  which is what a REPL session does, and set!, which is what §5.33 actually broke
  and what instrument does (§5.35) - and every body carries the tag of ITS OWN
  definition, so the two shapes cannot answer a call identically and reaching the
  old f is a wrong answer rather than a coincidence.

  ITS SECOND CLAIM NEEDS THE OTHER GATE. With static dispatch off - the default
  since §5.44 - no call site names an arity, so redefinition safety is close to
  structural and the property is a regression guard. The claim with a compiler in
  it is that a compile AFTER the redefinition knows the NEW shape, and that is only
  visible with static dispatch ON, where the call site says the arity out loud. So
  the property runs one session each way.

  ITS TEETH ARE THAT OTHER GATE TOO, and nothing had to be injected to find them:
  under static dispatch a caller compiled before the redefinition genuinely does
  not survive it, which is pinned by
  test-static-dispatch-is-what-makes-redefinition-unsafe. §5.33's fix was then
  removed as well - its two halves separately, since parse-def and parse-set! clear
  :top-fn in two different places - and the property failed on each, shrinking both
  times to

    shape A {:fixed #{0 1}} -> shape B {:fixed #{0}}
      static session THREW: ...f.cljs$core$IFn$_invoke$arity$0 is not a function

  with the route naming whichever half had been removed.

  DEFTYPE / IFn IS THE SECOND HALF OF THIS FILE, and it is where §5.36 actually
  lived. A deftype implementing IFn is reached through two properties the type
  installs - `call` and `apply` - and its body reaches the receiver through `this`
  rather than through a parameter (adapt-ifn-params). So the shapes are the same
  and the hazards are not, and the properties change with them: every body reads a
  FIELD, and the calls are interleaved between TWO instances, so a receiver that is
  lost or is the wrong object is a wrong answer rather than a coincidence.

  Its oracle is a PLAIN FN of the same shape, closing over the same field value.
  That is the whole claim an IFn deftype makes, and it is also what leaves the
  receiver nowhere to hide.

  ITS TEETH, checked the same way: adapt-ifn-params was rewritten to take the
  receiver from its first parameter instead of from `this` - which is §5.36,
  exactly - and the property failed on the first shape, with

    on  THREW: Cannot read properties of null (reading 'k')
    jvm [[[0 :S] [0 :S]] [[0 :T] [0 :T]]]

  the null being the one in obj.call(null, ...) that the parameter exists to
  absorb.

  ONE THING IS ASSERTED RATHER THAN GENERATED, and it is a divergence we inherited:
  above twenty arguments, `apply` on an IFn deftype does NOT agree with a direct
  call - see the test at the end of this file for the mechanism and for why
  core.cljc being byte-identical to ClojureScript's is the whole argument that it
  is not ours. Generating past that boundary would have bought three hundred copies
  of one known fact.

  AND ONE CALL FORM IS ABSENT ON PURPOSE. (-invoke t 3) does not work on an IFn
  deftype - not here and not in ClojureScript. ifn-invoke-methods installs
  _invoke$arity$N counting the USER arguments, which is the function-call
  convention, while the protocol function -invoke dispatches on N counting the
  RECEIVER too. Those two readings of one property name collide, and upstream's own
  test suite never calls -invoke directly either. Not a call form, so not a
  property.

  Needs node. doc/cljs-compiler.md §5.40."}
  clojure.cljs.calling-convention-test
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.test-harness :as h]
            [clojure.test :refer [is testing use-fixtures]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]))

(use-fixtures :each h/cursor)

;; --- the shape --------------------------------------------------------------

(defn- shape-gen
  "{:fixed #{0 2} :variadic 2}: a set of fixed arities and, maybe, the number of
  fixed parameters ahead of a variadic tail. Parameterised by the arity generator
  because the two halves of this file have different ceilings.

  A fixed arity LARGER than the variadic's prefix is not a legal function in either
  language, so those are filtered out rather than generated and discarded - and a
  fixed arity EQUAL to it is legal and is where the interesting choice lives:
  cljs.core/str is ([] ...) ([x] ...) ([x & ys] ...), and calling it with one
  argument has to reach the second body and not the third."
  [gen-arity]
  (gen/such-that
   (fn [{:keys [fixed variadic]}] (or variadic (seq fixed)))
   (gen/let [variadic (gen/one-of [(gen/return nil) gen-arity])
             fixed    (gen/set gen-arity {:max-elements 5})]
     {:fixed    (into (sorted-set) (if variadic (filter #(<= % variadic) fixed) fixed))
      :variadic variadic})
   100))

(def ^:private gen-shape
  "For a defn. 20 is Clojure's own limit - fn* refuses a twenty-first parameter -
  so it is the most property 2's oracle can express."
  (shape-gen (gen/frequency [[8 (gen/choose 0 6)]
                             [2 (gen/choose 17 20)]])))

(def ^:private gen-ifn-shape
  "For a deftype's IFn methods, where the ceiling is lower and is cljs.core's
  rather than Clojure's: -invoke is declared out to twenty arguments, and a
  variadic sig spends two of its slots on `&` and the rest parameter, so a prefix
  of twenty is one too many and warns protocol-invalid-method. Measured, not
  guessed: 19 is clean and 20 is not."
  (shape-gen (gen/frequency [[8 (gen/choose 0 6)]
                             [2 (gen/choose 16 19)]])))

;; --- the shape as a function, and as the calls it answers -------------------

(defn- params [n] (mapv #(symbol (str "a" %)) (range n)))

(defn- arities
  "The shape's fn tails. Each body names its own arity, so a result says which one
  answered: [2 100 101] from the fixed arity 2, [:v 100 (101)] from the variadic.

  With a TAG each body names its DEFINITION too - [:b 2 100 101] - which is what
  the redefinition property below needs. Two shapes that answer a call the same way
  would otherwise leave no way to tell which of them answered it."
  ([shape] (arities nil shape))
  ([tag {:keys [fixed variadic]}]
   (let [mark (fn [body] (if tag (into [tag] body) body))]
     (cond-> (mapv (fn [n] (list (params n) (mark (into [n] (params n))))) fixed)
       variadic (conj (list (into (params variadic) '[& r])
                            (mark (into [:v] (conj (params variadic) 'r)))))))))

(defn- call-arities
  "Every argument count the shape answers, and no others - an undefined arity is a
  throw in both languages, which is a different property than these three.

  The last one is the point of its line: more than twenty arguments, which only a
  variadic tail can take, and which is where cljs.core/apply runs out of fixed
  arities to hand off to."
  [{:keys [fixed variadic]}]
  (sort (into (set fixed)
              (when variadic
                (conj (range variadic (+ variadic 4)) (+ variadic 22))))))

(defn- calls-on
  "One tuple per arity: the direct call of `sym` and the two spellings of apply.
  Property 3 is that a tuple's elements are all equal; properties 1 and 2 compare
  whole vectors of tuples across compilations."
  [sym ns]
  (vec (for [n ns
             :let [args (vec (range 100 (+ 100 n)))]]
         (cond-> [(cons sym args) (list 'apply sym args)]
           (pos? n) (conj (list 'apply sym (first args) (vec (rest args))))))))

(defn- calls [shape] (calls-on 'f (call-arities shape)))

(defn- cljs-src
  "A TOP-LEVEL defn, which is the whole point: a var of known shape is what
  emitter/*static-dispatch* reads, and a let-bound fn would have none."
  [shape]
  (str (pr-str (list* 'defn 'f (arities shape))) "\n"
       (pr-str (list 'pr-str (mapv vec (calls shape))))))

(defn- clj-form
  "The same shape on the JVM. A let rather than a def so the oracle interns
  nothing; pr-str on both sides so the comparison is of printed values and not of
  two representations."
  [shape]
  (list 'let ['f (list* 'fn 'f (arities shape))]
        (list 'pr-str (mapv vec (calls shape)))))

;; --- the three properties ---------------------------------------------------

(defn- outcomes [shape]
  (let [src (cljs-src shape)
        on  (binding [emitter/*static-dispatch* true]
              (h/output-with-core (h/core-env) src))
        off (binding [emitter/*static-dispatch* false]
              (h/output-with-core (h/core-env) src))
        jvm (eval (clj-form shape))
        tuples (try (read-string on) (catch Throwable _ ::unreadable))]
    {:src src :on on :off off :jvm jvm
     :static-agrees?  (= on off)
     :clojure-agrees? (= on jvm)
     :apply-agrees?   (and (vector? tuples) (every? #(apply = %) tuples))}))

(defn- holds? [shape]
  (let [o (outcomes shape)]
    (and (:static-agrees? o) (:clojure-agrees? o) (:apply-agrees? o))))

(defn- report
  "What a failure prints. The shrunk shape re-run, so the source and both outputs
  are the minimal ones rather than the ones that happened to fail first."
  [shape]
  (let [o (outcomes shape)]
    (str "\nshape " (pr-str shape)
         "\n  static dispatch on == off : " (:static-agrees? o)
         "\n  == JVM Clojure            : " (:clojure-agrees? o)
         "\n  apply == direct call      : " (:apply-agrees? o)
         "\n\nsource\n" (:src o)
         "\n\non  " (:on o)
         "\noff " (:off o)
         "\njvm " (:jvm o) "\n")))

(h/deftest-when h/node? test-every-arity-answers-the-same-whatever-the-call-site
  ;; Forty shapes, which is about nine seconds: two node runs each, against a
  ;; cljs.core compiled once for the whole suite. Run at 400 (86 seconds) while it
  ;; was being written, and it found nothing - see §5.40 for why that is still
  ;; worth having, and for the two boundaries it did reach.
  (let [result (tc/quick-check 40 (prop/for-all [shape gen-shape] (holds? shape)))]
    (testing "no shape where the static path, the generic path and Clojure disagree"
      (is (:pass? result)
          (when-not (:pass? result)
            (report (first (get-in result [:shrunk :smallest]))))))))

;; --- redefinition -----------------------------------------------------------
;;
;; §5.33's bug was a call site OUTLIVING THE SHAPE IT NAMED: set! on a var dropped
;; :top-fn, so a g compiled while f had two arities went on naming arity$2 after f
;; had been redefined with one. None of the three properties above can reach that,
;; because all three are about ONE definition. The property that catches it is a
;; SEQUENCE of two - so this generates two shapes and a route from the first to the
;; second, with a caller compiled in between:
;;
;;   (defn f <A>)              ;; bodies tagged :a
;;   (defn g [] [<calls>])     ;; COMPILED HERE, while f is still A
;;   (g)                       ;; -> A's answers
;;   (defn f <B>)  or  (set! f (fn <B>))
;;   (g)                       ;; -> B's answers, or the bug
;;   (defn g2 [] [<calls>])    ;; the same calls, compiled after
;;   (g2)                      ;; -> B's answers
;;
;; EVERY BODY CARRIES THE TAG OF ITS DEFINITION as well as its arity, so A and B
;; cannot answer a call identically: reaching the old f is a wrong answer rather
;; than a coincidence, whatever the two shapes have in common. And g calls only the
;; arities BOTH shapes answer, because an arity a shape does not have is a throw in
;; both languages - the same excluded property as above.
;;
;; TWO CLAIMS, AND THEY NEED THE TWO GATES.
;;
;;   I.  WHEN g WAS COMPILED DOES NOT MATTER. g, compiled before the redefinition,
;;       answers what g2 - compiled after it - answers, and both answer what JVM
;;       Clojure answers for shape B. That is redefinition safety, and it is what
;;       §5.44 rests on in making *static-dispatch* false the default.
;;
;;   II. A COMPILE AFTER THE REDEFINITION KNOWS THE NEW SHAPE. Run with static
;;       dispatch ON, where a call site names an arity out loud, g2 is right only
;;       if the analyzer's record of f moved when f did. That is §5.33's bug
;;       exactly, and it is the claim the DEFAULT gate cannot state at all, because
;;       with dispatch off no call site names an arity.
;;
;; Claim I is false under static dispatch, on purpose:
;; test-static-dispatch-is-what-makes-redefinition-unsafe pins that, and it doubles
;; as this property's teeth. Nothing has to be injected to show the assertion can
;; fail, because the compiler still has a mode in which it does.

(defn- answers?
  "Whether the shape has a body for a call of n arguments."
  [{:keys [fixed variadic]} n]
  (or (contains? fixed n) (and variadic (>= n variadic))))

(defn- common-arities
  "The argument counts both shapes answer, drawn from both shapes' interesting
  ones - so the pair reaches A's boundaries and B's, not just the first's."
  [a b]
  (sort (filter #(and (answers? a %) (answers? b %))
                (into (sorted-set) (concat (call-arities a) (call-arities b))))))

(def ^:private gen-redefinition
  "Two shapes with at least one arity in common, and the route from one to the
  other. Both routes are a var changing shape under a caller that was compiled
  against the old one; defn is what a REPL session does and set! is what §5.33
  actually broke, and what instrument does (§5.35)."
  (gen/such-that
   (fn [[a b _]] (seq (common-arities a b)))
   (gen/tuple gen-shape gen-shape (gen/elements [:defn :set!]))
   100))

(defn- define
  "A top-level input defining f with `shape`, by either route. Each input ends in a
  0 so that it prints on one line: session-output is one line per input, and node
  printing a multi-arity function object would not be one line."
  [route tag shape]
  (str (pr-str (case route
                 :defn (list* 'defn 'f (arities tag shape))
                 :set! (list 'set! 'f (list* 'fn (arities tag shape)))))
       "\n0"))

(defn- redef-session
  "The sequence claim I is about, as REPL inputs."
  [[a b route] cs]
  [(define :defn :a a)
   (str (pr-str (list 'defn 'g [] cs)) "\n0")
   "(pr-str (g))"
   (define route :b b)
   "(pr-str (g))"
   (str (pr-str (list 'defn 'g2 [] cs)) "\n0")
   "(pr-str (g2))"])

(defn- later-session
  "Claim II: the same redefinition, but only the caller compiled AFTER it. No call
  is made against the old shape, so the session cannot throw for claim I's reason -
  which matters because a throw would take the rest of the run with it."
  [[a b route] cs]
  [(define :defn :a a)
   (define route :b b)
   (str (pr-str (list 'defn 'g2 [] cs)) "\n0")
   "(pr-str (g2))"])

(defn- jvm-answers
  "The oracle: the same shape as a Clojure fn, applied the same ways."
  [tag shape cs]
  (eval (list 'let ['f (list* 'fn 'f (arities tag shape))] (list 'pr-str cs))))

(defn- redef-outcomes [[a b _ :as spec]]
  (let [cs    (calls-on 'f (common-arities a b))
        dyn   (binding [emitter/*static-dispatch* false]
                (h/session-output (h/core-env) (redef-session spec cs)))
        stat  (binding [emitter/*static-dispatch* true]
                (h/session-output (h/core-env) (later-session spec cs)))
        jvm-a (jvm-answers :a a cs)
        jvm-b (jvm-answers :b b cs)
        [before after fresh] [(nth dyn 2 nil) (nth dyn 4 nil) (nth dyn 6 nil)]
        later (nth stat 3 nil)]
    {:spec spec :dyn dyn :stat stat :jvm-a jvm-a :jvm-b jvm-b
     ;; the sanity clause: the caller was right BEFORE the redefinition, so a
     ;; failure below is the redefinition and not the shape
     :was-right-first?      (= before jvm-a)
     ;; ... and the redefinition changed the answer, which the tags guarantee
     :took-effect?          (not= before after)
     ;; claim I
     :survives?             (= after jvm-b)
     :order-irrelevant?     (= after fresh)
     ;; claim II
     :static-knows-the-new? (= later jvm-b)}))

(def ^:private redef-claims
  [:was-right-first? :took-effect? :survives? :order-irrelevant?
   :static-knows-the-new?])

(defn- redef-holds? [spec]
  (let [o (redef-outcomes spec)] (every? o redef-claims)))

(defn- redef-report [[a b route :as spec]]
  (let [o (redef-outcomes spec)]
    (str "\nshape A " (pr-str a) "  ->  " (name route) "  ->  shape B " (pr-str b)
         "\n  caller was right before it  : " (:was-right-first? o)
         "\n  the redefinition took effect: " (:took-effect? o)
         "\n  caller survives it          : " (:survives? o)
         "\n  == a caller compiled after  : " (:order-irrelevant? o)
         "\n  static dispatch knows B     : " (:static-knows-the-new? o)
         "\n\ninputs\n" (clojure.string/join "\n" (redef-session spec (calls-on 'f (common-arities a b))))
         "\n\ndynamic session " (pr-str (:dyn o))
         "\nstatic session  " (pr-str (:stat o))
         "\njvm A           " (:jvm-a o)
         "\njvm B           " (:jvm-b o) "\n")))

(h/deftest-when h/node? test-a-caller-compiled-before-a-redefinition-sees-the-new-one
  ;; Thirty pairs, two node sessions each - about eight seconds. Run at 300 while
  ;; it was written: 71 seconds, nothing found, and §5.40 records where it reached.
  (let [result (tc/quick-check 30 (prop/for-all [spec gen-redefinition]
                                                (redef-holds? spec)))]
    (testing "whatever the shape changed to, and whichever route changed it"
      (is (:pass? result)
          (when-not (:pass? result)
            (redef-report (first (get-in result [:shrunk :smallest]))))))))

(h/deftest-when h/node? test-static-dispatch-is-what-makes-redefinition-unsafe
  ;; WHY THE PROPERTY ABOVE IS NOT VACUOUS, and §5.44's argument as a test.
  ;;
  ;; The same session under the other gate. f loses an arity; g was compiled while
  ;; f still had it. With dispatch off the call is f.call(null, 100) and finds
  ;; whatever f is now; with it on the call site named arity$1 out loud, and a
  ;; single-method f has no such property - core.cljc sets none on a function that
  ;; has only one method - so the call site outlives the shape it named.
  (let [srcs ["(defn f ([x] [:a 1 x]) ([x y] [:a 2 x y]))\n0"
              "(defn g [] [(f 100)])\n0"
              "(defn f ([x] [:b 1 x]))\n0"
              "(pr-str (g))"]
        run  (fn [static?]
               (binding [emitter/*static-dispatch* static?]
                 (h/session-output (h/core-env) srcs)))]
    (testing "off, which is the default, the caller sees the new definition"
      (is (= "[[:b 1 100]]" (last (run false)))))
    (testing "on, it names an arity the new definition does not have"
      (is (clojure.string/includes? (first (run true))
                                    "arity$1 is not a function")))))

;; --- deftype / IFn ----------------------------------------------------------
;;
;; The same shapes reached through a different mechanism. core.cljc's
;; add-ifn-methods installs TWO properties on the type - `call`, which is the
;; variadic shim over every method, and `apply`, which repacks an argument array
;; and forwards to `call` - and adapt-ifn-params rewrites each method so that its
;; first parameter absorbs the null in obj.call(null, ...) and the receiver comes
;; from `this`. §5.36 was that rewrite losing the receiver.
;;
;; So the receiver is the thing to test, and the way to test it is to make losing
;; it impossible to get right by accident: every body reads a field, and the calls
;; alternate between two instances whose fields differ.

(def ^:private max-ifn-arity
  "core.cljc's own constant (add-ifn-methods). A call of more than this many
  arguments is where `apply` and a direct call part company - see
  test-apply-and-a-direct-call-part-company-above-twenty-arguments, which pins
  that rather than letting the generator rediscover it 300 times."
  20)

(defn- ifn-call-arities [shape]
  (filter #(<= % max-ifn-arity) (call-arities shape)))

(defn- ifn-methods
  "The -invoke tails. The leading _ is the receiver parameter, which the body does
  NOT use - k is read out of the field, so the answer is only right if `this` is
  the instance that was called."
  [{:keys [fixed variadic]}]
  (cond-> (mapv (fn [n] (list (into '[_] (params n)) (into [n 'k] (params n)))) fixed)
    variadic (conj (list (into (conj (into '[_] (params variadic)) '&) '[r])
                         (into [:v 'k] (conj (params variadic) 'r))))))

(defn- ifn-call-tuples
  "One tuple per (arity, instance): the direct call and the two spellings of apply,
  against `s` and then `t`. Alternating the instance is what makes a lost receiver
  a wrong ANSWER - the two differ only in their field."
  [shape]
  (vec (for [n   (ifn-call-arities shape)
             obj '[s t]
             :let [args (vec (range 100 (+ 100 n)))]]
         (cond-> [(cons obj args) (list 'apply obj args)]
           (pos? n) (conj (list 'apply obj (first args) (vec (rest args))))))))

(defn- ifn-cljs-src
  "Two instances of one IFn deftype, and every call spelled against each."
  [shape]
  (str (pr-str (list* 'deftype 'T '[k] 'IFn
                      ;; each impl carries its own method name, which is what
                      ;; distinguishes a protocol impl from an fn tail
                      (map #(cons '-invoke %) (ifn-methods shape))))
       "\n"
       (pr-str (list 'let '[s (T. :S) t (T. :T)]
                     (list 'pr-str (ifn-call-tuples shape))))))

(defn- ifn-clj-form
  "The oracle: a plain fn of the same shape, closing over the same k. An IFn
  deftype's whole claim is that it is a function of that shape, so a function of
  that shape is what it has to answer like - which also means the receiver has
  nowhere to hide, since k is what the bodies return."
  [shape]
  (let [tails (mapv (fn [[sig & body]] (cons (vec (rest sig)) body))
                    (ifn-methods shape))]
    (list 'let ['mk (list 'fn '[k] (list* 'fn 'f tails))]
          (list 'let ['s (list 'mk :S) 't (list 'mk :T)]
                (list 'pr-str (ifn-call-tuples shape))))))

(defn- quietly
  "A variadic -invoke warns - protocol-impl-with-variadic-method - and so does
  ClojureScript's own, for the same reason and at the same place. The warning is
  right; a few hundred copies of it in the middle of a test run are not."
  [f]
  (binding [ana/*cljs-warnings*
            (assoc ana/*cljs-warnings* :protocol-impl-with-variadic-method false)]
    (f)))

(defn- ifn-outcomes [shape]
  (let [src (ifn-cljs-src shape)
        on  (quietly #(binding [emitter/*static-dispatch* true]
                        (h/output-with-core (h/core-env) src)))
        off (quietly #(binding [emitter/*static-dispatch* false]
                        (h/output-with-core (h/core-env) src)))
        jvm (eval (ifn-clj-form shape))
        tuples (try (read-string on) (catch Throwable _ ::unreadable))]
    {:src src :on on :off off :jvm jvm
     :static-agrees?  (= on off)
     :fn-agrees?      (= on jvm)
     :apply-agrees?   (and (vector? tuples) (every? #(apply = %) tuples))}))

(defn- ifn-holds? [shape]
  (let [o (ifn-outcomes shape)]
    (and (:static-agrees? o) (:fn-agrees? o) (:apply-agrees? o))))

(defn- ifn-report [shape]
  (let [o (ifn-outcomes shape)]
    (str "\nshape " (pr-str shape)
         "\n  static dispatch on == off  : " (:static-agrees? o)
         "\n  == a plain fn of that shape: " (:fn-agrees? o)
         "\n  apply == direct call       : " (:apply-agrees? o)
         "\n\nsource\n" (:src o)
         "\n\non  " (:on o)
         "\noff " (:off o)
         "\njvm " (:jvm o) "\n")))

(h/deftest-when h/node? test-an-ifn-deftype-answers-like-a-function-of-that-shape
  (let [result (tc/quick-check 30 (prop/for-all [shape gen-ifn-shape] (ifn-holds? shape)))]
    (testing "and every body sees the instance it was called on"
      (is (:pass? result)
          (when-not (:pass? result)
            (ifn-report (first (get-in result [:shrunk :smallest]))))))))

(h/deftest-when h/node? test-apply-and-a-direct-call-part-company-above-twenty-arguments
  ;; A DIVERGENCE INHERITED, NOT INTRODUCED, and pinned here so that it becomes a
  ;; test failure if it ever stops being true.
  ;;
  ;; core.cljc's add-ifn-methods gives the type an `apply` that repacks its
  ;; argument array before forwarding to `call`: past max-ifn-arity it slices the
  ;; first twenty and PUSHES THE REMAINDER AS ONE ARRAY as the twenty-first
  ;; argument. `call` is the variadic shim, which collects its arguments into a
  ;; seq - so the tail arrives as a seq whose last element is a JavaScript array,
  ;; where a direct call of the same arguments gives them flat.
  ;;
  ;; That function is byte-identical to ClojureScript's (cljs/core.cljc 1.12.145,
  ;; add-ifn-methods), so this is ClojureScript's behaviour and not ours. It is why
  ;; the generator above stops at twenty: a property that is false upstream is not
  ;; a property, and generating past the boundary would have bought 300 copies of
  ;; one known divergence.
  (let [answers (fn [n]
                  (let [as (clojure.string/join " " (range 1 (inc n)))]
                    (quietly
                     #(h/output-with-core
                       (h/core-env)
                       (str "(deftype V [k] IFn (-invoke [_ & r] [:v r]))\n"
                            "(let [t (V. :K)]"
                            " (pr-str [(t " as ") (apply t [" as "])]))")))))]
    (testing "at the boundary they agree"
      (let [out (answers max-ifn-arity)
            [direct applied] (read-string out)]
        (is (= direct applied) out)))
    (testing "one argument later they do not, and the tail is the shape of it"
      (let [out (answers (inc max-ifn-arity))]
        (is (clojure.string/includes? out "#js [")
            (str "expected apply's tail to carry a nested array: " out))))))
