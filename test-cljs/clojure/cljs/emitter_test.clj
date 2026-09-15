;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The execution oracle: compiled ClojureScript, run under node, produces
  the value it should.

  The AST oracle (clojure.cljs.oracle-test) checks that we understand the form the
  way ClojureScript does; this checks that what we emit means the same thing. The
  two are independent, and both are needed - matching ASTs would not save us from
  emitting the wrong JavaScript.

  js* supplies arithmetic and interop, so this needs no core library at all - only
  clojure/cljs/runtime.js, which is two functions: $ns, the namespace registry a
  var is a property of, and truth_, because ClojureScript truthiness is not
  JavaScript's. Each program imports it the way a compiled module will.

  Skipped when node is not on PATH."}
  clojure.cljs.emitter-test
  (:require [clojure.cljs.emitter :as emitter]
            [clojure.cljs.test-harness :as h]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

(defmacro emits
  "Each (src => expected) pair compiles, runs, and prints `expected`."
  [& pairs]
  `(are [src# expected#] (= expected# (h/output src#))
     ~@pairs))

(h/deftest-when h/node? test-literals-and-truthiness
  (emits
   "1"                                  "1"
   "\"a string\""                       "a string"
   "nil"                                "null"
   ;; 0 and "" are true in ClojureScript, which is what truth_ is for
   "(if 0 \"zero is true\" \"zero is false\")"   "zero is true"
   "(if \"\" \"empty is true\" \"empty is false\")" "empty is true"
   "(if nil \"y\" \"n\")"               "n"
   "(if false \"y\" \"n\")"             "n"))

(h/deftest-when h/node? test-let-and-do
  (emits
   "(let* [x 1] x)"                     "1"
   "(let* [x 1 y (js* \"~{} + 1\" x)] y)" "2"
   ;; shadowing: the analyzer renames, so the inner x cannot collide
   "(let* [x 1] (let* [x 2] x))"        "2"
   "(do 1 2 3)"                         "3"
   ;; an if in expression position needs no function wrapper
   "(let* [x 1] (if x (let* [y 2] y) 3))" "2"))

(h/deftest-when h/node? test-fn
  (emits
   "((fn* ([x] x)) 42)"                          "42"
   "((fn* ([x y] (js* \"~{} + ~{}\" x y))) 3 4)" "7"
   ;; arity dispatch
   "(let* [f (fn* ([x] x) ([x y] (js* \"~{} + ~{}\" x y)))] (f 6 7))" "13"
   ;; self-reference by name
   "((fn* fact ([n] (if (js* \"~{} <= 1\" n) 1 (js* \"~{} * ~{}\" n (fact (js* \"~{} - 1\" n)))))) 5)" "120"
   ;; a rest parameter is a JavaScript array until cljs.core arrives
   ;; a rest argument is not in here, because it is a SEQ since §5.14 and nothing
   ;; in this environment can read one - see test-a-rest-argument-is-a-seq below
   ))

(h/deftest-when h/node? test-a-rest-argument-is-a-seq
  ;; It was a JavaScript array until §5.14, and the test that was here read
  ;; `r.length` - which is why the emitter could carry a docstring saying the array
  ;; was provisional for two milestones without anything failing. A seq needs
  ;; cljs.core to be read at all, so this is the one fn test that cannot live in
  ;; the block above.
  (let [run #(h/output-with-core (h/core-env) %)]
    (is (= "13" (run "((fn* ([x & r] (js* \"~{} + ~{}\" x (count r)))) 10 1 2 3)")))
    (is (= "(1 2 3)" (run "(pr-str ((fn* ([& r] r)) 1 2 3))")))
    ;; nil and not an empty seq when nothing was passed, which is Clojure's answer
    (is (= "nil" (run "(pr-str ((fn* ([& r] r))))")))
    (is (= "[1 (2 3)]" (run "(pr-str [((fn* ([n & r] n)) 1 2 3) ((fn* ([n & r] r)) 1 2 3)])")))))

(h/deftest-when h/node? test-apply-does-not-realize-the-rest-of-an-argument-seq
  ;; A VARIADIC FN CARRIES TWO PROPERTIES cljs.core/apply looks for, and without
  ;; them apply falls back to apply-to-simple, which walks the argument sequence to
  ;; the end to build an argument array. So (apply (fn [& xs] ...) (iterate inc 0))
  ;; exhausted the heap, which is how it was found: it is the one line in
  ;; ClojureScript's primitives-test that took the whole run down with it (§5.15).
  ;;
  ;; Only fn* was missing them. A variadic defn already had them, because
  ;; cljs.core's defn macro builds the same two properties by hand
  ;; (core.cljc:3298) - so nothing that read them could notice, and the two
  ;; spellings had to be made to agree rather than one of them invented.
  (let [run #(h/output-with-core (h/core-env) %)]
    (testing "the properties are there, and say the right arity"
      (is (= "[true 0]" (run "(let [f (fn [& xs] xs)]
                               (pr-str [(boolean (.-cljs$lang$applyTo f))
                                        (.-cljs$lang$maxFixedArity f)]))")))
      (is (= "[true 2]" (run "(let [f (fn [a b & xs] xs)]
                               (pr-str [(boolean (.-cljs$lang$applyTo f))
                                        (.-cljs$lang$maxFixedArity f)]))")))
      ;; and a defn agrees with an fn*, which is the point of using ClojureScript's
      ;; spelling for the property the body hangs on
      (is (= "[true 1]" (run "(defn g [a & xs] xs)
                              (pr-str [(boolean (.-cljs$lang$applyTo g))
                                       (.-cljs$lang$maxFixedArity g)])"))))
    (testing "so apply counts no further than the fixed arity"
      (is (= "3" (run "(apply (fn [& xs] (+ (nth xs 0) (nth xs 1) (nth xs 2)))
                              (iterate inc 0))")))
      (is (= "1" (run "(apply (fn [a & xs] (+ a (first xs))) (iterate inc 0))")))
      ;; the rest parameter is the seq apply was handed, still unrealized
      (is (= "[2 3 4]" (run "(pr-str (vec (apply (fn [a b & r] (take 3 r))
                                                 (iterate inc 0))))"))))
    (testing "and the body, which now lives on a property, is still the same body"
      ;; a variadic fn that names itself has to see itself from its new home
      (is (= "[:x :x :x :a]"
             (run "(pr-str ((fn h [n & xs] (if (zero? n) (vec xs) (apply h (dec n) :x xs))) 3 :a))")))
      ;; and one that recurs still has a loop to jump to
      (is (= "[:y :y :z]"
             (run "(pr-str ((fn [n & xs] (if (zero? n) (vec xs) (recur (dec n) (cons :y xs)))) 2 :z))")))
      ;; a variadic arity alongside fixed ones dispatches as before
      (is (= "[:one 1] [:many 1 2 [3 4]] [:many 1 2 [3 4]]"
             (run "(let [g (fn ([a] [:one a]) ([a b & r] [:many a b (vec r)]))]
                     (str (pr-str (g 1)) \" \" (pr-str (g 1 2 3 4)) \" \" (pr-str (apply g 1 2 [3 4]))))"))))))

(h/deftest-when h/node? test-loop-recur
  (emits
   "(loop* [i 0 acc 0] (if (js* \"~{} < 10\" i) (recur (js* \"~{} + 1\" i) (js* \"~{} + ~{}\" acc i)) acc))" "45"
   ;; recur rebinds simultaneously
   "(loop* [a 1 b 2 n 0] (if (js* \"~{} < 3\" n) (recur b a (js* \"~{} + 1\" n)) (js* \"'a=' + ~{} + ' b=' + ~{}\" a b)))" "a=2 b=1"
   ;; a loop nobody recurs to is a let
   "(loop* [x 42] x)" "42"
   ;; recur to a fn method, not a loop
   "((fn* ([n] (if (js* \"~{} < 15\" n) (recur (js* \"~{} + 1\" n)) n))) 0)" "15"))

(h/deftest-when h/node? test-a-closure-keeps-the-iteration-it-was-made-in
  ;; A LOOP BINDING IS IMMUTABLE and recur starts a new iteration, so a fn made in
  ;; one iteration keeps that iteration's values. Assigning the body's own variable
  ;; makes every such fn see the LAST values instead - JavaScript's var-in-a-loop
  ;; problem, arrived at from Clojure semantics - which is what this emitted until
  ;; §5.14. emitter/carriers! has the fix and why it is at the loop rather than at
  ;; each closure.
  ;;
  ;; Against a compiled cljs.core because seeing it needs a collection of closures,
  ;; and it needs cljs.core for the same reason ClojureScript's own primitives-test
  ;; is where it surfaced.
  (let [run #(h/output-with-core (h/core-env) %)]
    (testing "a loop*"
      (is (= "[4 3 2 1 0]"
             (run "(pr-str (loop [i 0 j ()]
                     (if (< i 5) (recur (inc i) (conj j (fn [] i))) (vec (map #(%) j)))))"))))
    (testing "and a fn method, which is the same recur point wearing a hat"
      (is (= "[0 1 2]"
             (run "(def fs (atom []))
                   ((fn [i] (if (< i 3) (do (swap! fs conj (fn [] i)) (recur (inc i))) nil)) 0)
                   (pr-str (mapv #(%) @fs))"))))
    (testing "a nested fn closing over BOTH loops"
      (is (= "[[0 0] [0 1] [1 0] [1 1]]"
             (run "(pr-str (vec (mapv #(%)
                     (loop [i 0 out []]
                       (if (< i 2)
                         (recur (inc i)
                                (loop [j 0 out out]
                                  (if (< j 2) (recur (inc j) (conj out (fn [] [i j]))) out)))
                         out)))))"))))
    (testing "and the values still travel, which is what a carrier is for"
      (is (= "45" (run "(loop [i 0 acc 0] (if (< i 10) (recur (inc i) (+ acc i)) acc))")))
      (is (= "a=2 b=1" (run "(loop [a 1 b 2 n 0]
                              (if (< n 3) (recur b a (inc n)) (str \"a=\" a \" b=\" b)))"))))))

(h/deftest-when h/node? test-def
  (emits
   "(def x 1) x"                        "1"
   "(def x 1) (def y (js* \"~{} + 1\" x)) y" "2"
   "(def f (fn* ([a] (js* \"~{} * 2\" a)))) (f 21)" "42"
   ;; def at any depth. A var is a property, so there is nothing to declare and
   ;; nothing to hoist - the property simply comes into being when the assignment
   ;; runs. Reading it through the namespace object, not through a bare name, is
   ;; what makes this observe the var rather than an absent global.
   "(def before (js* \"typeof app$core$ns.inner\")) (def setit (fn* ([] (def inner 99)))) (do (setit) (js* \"~{} + ' ' + ~{}\" before inner))"
   "undefined 99"))

(h/deftest-when h/node? test-vars-are-namespace-object-properties
  ;; The Option B decision (doc/cljs-repl.md 3.1), tested by its consequences
  ;; rather than by the shape of the emitted text.
  (emits
   ;; the registry is idempotent: a reloaded module gets the same object back,
   ;; which is what makes every existing reference see new definitions
   "(js* \"$ns('a.b') === $ns('a.b')\")" "true"

   ;; a var is reachable BY NAME from code that holds no module binding. This is
   ;; the property a module-scoped var cannot have, and the whole reason for the
   ;; decision: evaluated REPL code is never inside the module it wants to change.
   "(def answer 42) (js* \"globalThis.$CLJS.namespaces.get('app.core').answer\")" "42"

   ;; and it can be redefined from there - code compiled earlier, holding no
   ;; reference to the new definition, picks it up because every var reference is
   ;; resolved at call time
   "(def greet (fn* ([] \"v1\"))) (def call (fn* ([] (greet)))) (do (js* \"globalThis.$CLJS.namespaces.get('app.core').greet = function () { return 'v2'; }\") (call))"
   "v2"))

(h/deftest-when h/node? test-interop
  (emits
   "(.-length \"abcd\")"                "4"
   "(.toUpperCase \"abc\")"             "ABC"
   "(.indexOf \"abcd\" \"c\")"          "2"
   "(. (. \"a,b,c\" (split \",\")) -length)" "3"
   "(.toUpperCase (.slice \"hello world\" 6))" "WORLD"
   "(.-PI js/Math)"                     "3.141592653589793"
   "(js/Math.max 3 9 4)"                "9"
   "(.getFullYear (new js/Date 2026 0 15))" "2026"
   "(.-message (js/Error. \"boom\"))"   "boom"
   "(.-length (new js/Array 5))"        "5"
   ;; a reserved word is a fine property name, so it is not munged
   "(let* [m (new js/Map)] (do (.set m \"k\" 1) (.delete m \"k\") (.-size m)))" "0"
   ;; statements bubble out of a target position
   "(.toUpperCase (if (js* \"true\") (let* [x \"ab\"] x) \"cd\"))" "AB"))

(h/deftest-when h/node? test-set!
  (emits
   "(def x 1) (do (set! x 42) x)"       "42"
   "(let* [o (js/Object.)] (do (set! (.-a o) 9) (.-a o)))" "9"
   ;; the three-place sugar
   "(let* [o (js/Object.)] (do (set! o -b 5) (.-b o)))" "5"
   ;; a set! is an expression, and its value is the assigned value
   "(def y 0) (set! y 3)"               "3"
   "(let* [o (js/Object.)] (do (set! (.-inner o) (js/Object.)) (set! (.-deep (.-inner o)) \"hi\") (.-deep (.-inner o))))" "hi"))

(h/deftest-when h/node? test-throw
  (emits
   "(throw (js/Error. \"boom\"))"       "THREW: boom"
   ;; the other branch still produces a value
   "(if (js* \"false\") (throw (js/Error. \"no\")) 7)" "7"
   ;; control never reaches the call: no function wrapper needed to say so
   "(js/Math.max 1 (throw (js/Error. \"cut\")) 3)" "THREW: cut"
   "(def boom (fn* ([] (throw (js/Error. \"inner\"))))) (boom)" "THREW: inner"
   ;; nothing is assigned, and there is no declaration to leave behind either
   "(def z (throw (js/Error. \"nope\")))" "THREW: nope"))

(h/deftest-when h/node? test-quote
  ;; Against the REAL cljs.core, because a quoted symbol and a keyword are objects
  ;; of its types (§5.10) and there is nothing to see in one but what cljs.core
  ;; makes of it. pr-str is the observation: a quoted symbol prints as itself, and
  ;; is not the string that names it.
  (are [src expected] (= expected (h/output-with-core (str "(cljs.core/pr-str " src ")")))
    "(quote foo)"     "foo"
    "(quote foo/bar)" "foo/bar"
    "(quote :bar)"    ":bar"
    "(quote :a/b)"    ":a/b"
    "(quote 42)"      "42"
    "(quote \"s\")"   "\"s\"")
  ;; and a symbol is a Symbol rather than the string: the two printed the same
  ;; while the placeholder stood, which is the one way it was observably wrong
  (is (= "false" (h/output-with-core "(cljs.core/= (quote foo) \"foo\")")))
  (is (= "true"  (h/output-with-core "(cljs.core/= (quote foo) (cljs.core/symbol \"foo\"))")))
  (is (= "true"  (h/output-with-core "(cljs.core/= :bar (cljs.core/keyword \"bar\"))"))))

(h/deftest-when h/node? test-letfn
  (emits
   "(letfn* [f (fn* ([x] x))] (f 1))" "1"
   ;; mutual recursion: every name is in scope in every init
   "(letfn* [ev (fn* ([n] (if (js* \"~{} === 0\" n) \"even\" (od (js* \"~{} - 1\" n))))) od (fn* ([n] (if (js* \"~{} === 0\" n) \"odd\" (ev (js* \"~{} - 1\" n)))))] (ev 10))" "even"
   ;; self-recursion, which ClojureScript does not manage - see oracle-test
   "(letfn* [fact (fn* ([n] (if (js* \"~{} <= 1\" n) 1 (js* \"~{} * ~{}\" n (fact (js* \"~{} - 1\" n))))))] (fact 5))" "120"))

(h/deftest-when h/node? test-case
  (emits
   "(let* [x 2] (case* x [[1] [2 3]] [\"one\" \"two-or-three\"] \"other\"))" "two-or-three"
   "(let* [x 3] (case* x [[1] [2 3]] [\"one\" \"two-or-three\"] \"other\"))" "two-or-three"
   "(let* [x 9] (case* x [[1] [2 3]] [\"one\" \"two-or-three\"] \"other\"))" "other"
   "(let* [x \"b\"] (case* x [[\"a\"] [\"b\"]] [1 2] 0))" "2"
   ;; a branch may need statements of its own
   "(let* [x 1] (case* x [[1]] [(let* [y 5] (js* \"~{} + 1\" y))] 0))" "6"
   ;; recur from a branch: continue leaves the loop, break would only leave the
   ;; switch, so a jumping branch emits no break
   "(loop* [i 0] (case* i [[0] [1]] [(recur (js* \"~{} + 1\" i)) (recur (js* \"~{} + 1\" i))] i))" "2"
   ;; a branch that throws
   "(let* [x 1] (case* x [[1]] [(throw (js/Error. \"cased\"))] 0))" "THREW: cased"))

(h/deftest-when h/node? test-def-emits-no-declaration
  (let [js (h/js "(def x 1)")]
    (is (str/includes? js "app$core$ns.x = (1);") js)
    ;; not `var x = 1;` - nothing a module can hide from the outside
    (is (not (str/includes? js "var ")) js))
  ;; (def x) with no init assigns nothing: (declare x) expands to it, and an
  ;; assignment would wipe the definition on a reload
  (let [js (h/js "(def x)")]
    (is (not (str/includes? js "app$core$ns.x =")) js)))

(h/deftest-when h/node? test-a-realistic-module
  ;; The test that was missing. Every other program here is one form, or a few
  ;; forms with distinct names, in a namespace called app.core - which is how
  ;; three separate bugs survived: duplicate `let` across top-level forms, an
  ;; unmunged hyphenated namespace, and the conj-shaped fn* arity.
  (let [src (str "(def zero? (fn* ([n] (js* \"~{} === 0\" n))))\n"
                 ;; same parameter name as the form above, and as the one below
                 "(def dec1 (fn* ([n] (js* \"~{} - 1\" n))))\n"
                 ;; a fixed arity sharing the variadic method's fixed arity
                 "(def count-args (fn* ([n] 1) ([n & more] (js* \"1 + ~{}.length\" more))))\n"
                 "(def down (fn* ([n] (loop* [i n acc 0]\n"
                 "  (if (zero? i) acc (recur (dec1 i) (js* \"~{} + ~{}\" acc i)))))))\n"
                 "(js* \"~{} + ' ' + ~{} + ' ' + ~{}\" (down 4) (count-args 1) (count-args 1 2 3))")
        js  (h/js (h/fresh-env 'my-app.core) src)]
    ;; the alias is a legal identifier, hyphen and all
    (is (str/includes? js "const my_app$core$ns = $ns(\"my-app.core\");") js)
    ;; no name is declared twice anywhere in the module
    (let [declared (map second (re-seq #"(?m)^\\s*let ([A-Za-z0-9_$]+)" js))]
      (is (= (count declared) (count (distinct declared)))
          (str "duplicate declarations: "
               (pr-str (map key (filter #(< 1 (val %)) (frequencies declared))))))))
  ;; and it RUNS, which is the other half. Against a compiled cljs.core rather
  ;; than the prelude alone, because count-args has a rest argument and a rest
  ;; argument is a seq (§5.14) - the local defs of zero? and dec1 stay as they
  ;; were, and shadowing cljs.core's zero? is part of what they now test.
  (is (= "10 1 3"
         (h/output-with-core
          (h/core-env 'my-app.core)
          (str "(def zero? (fn* ([n] (js* \"~{} === 0\" n))))\n"
               "(def dec1 (fn* ([n] (js* \"~{} - 1\" n))))\n"
               "(def count-args (fn* ([n] 1) ([n & more] (js* \"1 + ~{}\" (count more)))))\n"
               "(def down (fn* ([n] (loop* [i n acc 0]\n"
               "  (if (zero? i) acc (recur (dec1 i) (js* \"~{} + ~{}\" acc i)))))))\n"
               "(js* \"~{} + ' ' + ~{} + ' ' + ~{}\" (down 4) (count-args 1) (count-args 1 2 3))")))))

(h/deftest-when h/node? test-evaluation-is-left-to-right
  ;; Statements and expressions travel separately, so a later argument needing
  ;; statements used to run before an earlier argument whose effects live in its
  ;; expression. Each of these logs g then h, in that order.
  (let [g "(js* \"globalThis.log = (globalThis.log||'') + 'g'\")"
        h "(let* [y (js* \"globalThis.log = (globalThis.log||'') + 'h'\")] y)"]
    (emits
     (str "(def f (fn* ([a b] b))) (f " g " " h ") (js* \"globalThis.log\")") "gh"
     (str "(js* \"~{} + ~{}\" " g " " h ") (js* \"globalThis.log\")")        "gh"
     ;; a host call, where the target is the earlier of the two
     (str "(.concat " g " " h ") (js* \"globalThis.log\")")                    "gh"))
  ;; a local and a literal are stable, so neither is spilled for nothing - unlike
  ;; the var in head position, which a later sibling could redefine
  (let [js (h/js "(def f (fn* ([a b c] c))) (let* [k 5] (f k 1 (let* [y 2] y)))")]
    (is (re-find #"\(null, k__\d+, \(1\), y__\d+\)" js) js)))

(h/deftest-when h/node? test-numeric-literals
  ;; Every spelling here was checked against cljs.compiler/emit-str: pr-str, which
  ;; this used to use, round-trips Clojure syntax that JavaScript cannot read.
  (emits
   "##Inf"      "Infinity"
   "##-Inf"     "-Infinity"
   "##NaN"      "NaN"
   "(def x ##Inf) x" "Infinity"
   "1.5"        "1.5"
   "-3"         "-3"
   ;; JavaScript has one number type, so these are simply doubles, as in CLJS
   "10N"        "10"
   "1.5M"       "1.5"
   "(js* \"~{} + 1\" 10N)" "11")
  ;; an integer is parenthesised so that a member access after it parses
  (is (= "42" (h/output "(.toString 42)")))
  (is (= "101010" (h/output "(.toString 42 2)")))
  (is (= "1.5" (h/output "(.toFixed 1.5 1)"))))

(h/deftest-when h/node? test-order-hazards-around-mutable-values
  ;; A second review found two wrong answers hiding in the ordering fix itself.
  (emits
   ;; A set! target is an lvalue. Spilling it into a temporary made the whole
   ;; assignment a no-op, silently: the write landed on the temporary.
   "(def o (js* \"({x: 1})\")) (set! (.-x o) (let* [y 42] y)) (.-x o)" "42"
   "(def o (js* \"({x: 1})\")) (set! (.-x o) (if (js* \"true\") (let* [y 7] y) 0)) (.-x o)" "7"

   ;; A var read has no side effects but is not order-independent: a later
   ;; sibling can set! it or def over it, and the read must not float past that.
   "(def y 1) (def f (fn* ([a b] (js* \"'' + ~{} + ',' + ~{}\" a b)))) (f y (do (set! y 2) y))" "1,2"
   "(def y 1) (def f (fn* ([a b] (js* \"'' + ~{} + ',' + ~{}\" a b)))) (f y (do (def y 3) y))" "1,3"
   ;; a js/ global likewise
   "(def f (fn* ([a b] (js* \"'' + ~{} + ',' + ~{}\" a b)))) (do (set! js/globalThis.q 1) (f js/globalThis.q (do (set! js/globalThis.q 2) 5)))" "1,5"

   ;; and a local still is stable, so it is not spilled for nothing
   "(let* [k 1] (js* \"'' + ~{} + ',' + ~{}\" k (let* [y 2] y)))" "1,2"))

(h/deftest-when h/node? test-statements-with-effects-are-kept
  ;; Dropping a value used as a statement is only safe when there is no effect to
  ;; lose. A property read throws on null, so it is not droppable - a def's own
  ;; value, a var read and a literal are.
  (is (str/includes? (h/js "(let* [o nil] (do (. o -x) 1))") "o__1.x;"))
  (is (= "THREW: Cannot read properties of null (reading 'x')"
         (h/output "(let* [o nil] (do (. o -x) 1))")))
  (let [js (h/js "(def z 1) (def w 2)")]
    (is (not (str/includes? js "app$core$ns.z;")) js)
    (is (not (str/includes? js "app$core$ns.w;")) js)))

(h/deftest-when h/node? test-js-globals-are-spelled-the-hosts-way
  (emits
   ;; as ClojureScript spells them: js/foo-bar is the global foo_bar
   "(js* \"globalThis.foo_bar = 7\") js/foo-bar" "7"
   "(.-PI js/Math)"                               "3.141592653589793"
   ;; the one name whose leading minus is part of it, special-cased in CLJS too
   "js/-Infinity"                                 "-Infinity"))

(h/deftest-when h/node? test-a-fn-self-name-shadows-nothing
  ;; §5.34. The name a def gives its function is the qualified one ClojureScript
  ;; gives it, because cljs.spec.alpha reads it back (names/var-fn-name).
  (is (str/includes? (h/js "(def f (fn* ([] 1)))") "function app$core$f()"))
  ;; and it is host-spelled, which is what demunge inverts - _QMARK_, not $QMARK$
  (is (str/includes? (h/js "(def f? (fn* ([] 1)))") "function app$core$f_QMARK_()"))

  ;; THE ONE NAME THAT SPELLING IS NOT OURS TO USE. app$core$ns is the alias of
  ;; the namespace itself, bound by the prologue and read by every var reference
  ;; in the body - so (def ns ...) falls back to the $fn shape rather than
  ;; shadowing it.
  (let [js (h/js "(def other 7) (def ns (fn* ([] other)))")]
    (is (str/includes? js "function ns$fn()") js)
    ;; and not $ns, which is the runtime helper the prologue calls
    (is (not (str/includes? js "function $ns(")) js)
    ;; and the body still reads its vars through the alias the prologue bound,
    ;; which is the whole reason the fallback exists
    (is (str/includes? js "app$core$ns.other") js))

  ;; a js/ global of the same name is still reachable from inside the body
  (is (= "7" (h/output "(js* \"globalThis.g = 7\") (def g (fn* ([] js/g))) (g)"))))

(h/deftest-when h/node? test-no-function-wrappers
  ;; The point of destination-driven emission: an if in expression position never
  ;; becomes an IIFE. ClojureScript wraps both of these in (function (){...})().
  (let [pure (h/js "(let* [x 1] (if x 1 2))")]
    (is (not (str/includes? pure "function")) pure)
    ;; branches that need no statements need no temporary either
    (is (str/includes? pure "(truth_(x__1) ? (1) : (2))") pure))
  (let [stmts (h/js "(let* [x 1] (if x (let* [y 2] y) 3))")]
    (is (not (str/includes? stmts "function")) stmts)
    ;; a branch with a binding needs one, and gets a plain if statement
    (is (str/includes? stmts "if (truth_(x__1)) {") stmts)
    ;; a temporary, whatever number it drew
    (is (re-find #"let t\$\d+;" stmts) stmts))
  ;; case and throw are the other two ClojureScript wraps
  (let [c (h/js "(let* [x 1] (case* x [[1]] [\"a\"] \"b\"))")]
    (is (not (str/includes? c "function")) c)
    (is (str/includes? c "switch (x__1) {") c))
  (let [t (h/js "(let* [x 1] (js* \"~{}\" (throw x)))")]
    (is (not (str/includes? t "function")) t)))

(h/deftest-when h/node? test-a-call-passes-no-receiver
  ;; A var is a property of its namespace object, so emitting (f 1) as
  ;; app$core$ns.f(1) ran f with the NAMESPACE OBJECT as `this` - and a body doing
  ;; (js* "this.x = 1") would have written a var. cljs.compiler emits
  ;; cljs.user.f.call(null,(1)) for exactly this reason, and so do we now.
  (let [this "(js* \"this === null || this === undefined ? 'no this' : 'GOT THIS'\")"]
    (emits
     (str "(def f (fn* ([] " this "))) (f)")            "no this"
     ;; and the same call once a later argument needs statements, which spills the
     ;; head into a temporary. This is the half that used to disagree with the
     ;; other: same form, two meanings, decided by a sibling.
     (str "(def f (fn* ([a] " this "))) (f (let* [q 1] q))") "no this"
     ;; a property's VALUE, called - ClojureScript's o.f.call(null, ...): the
     ;; receiver is not part of a function value extracted from an object
     (str "(let* [o (js* \"({n: 7, f: function(a){ return this === null ||"
          " this === undefined ? 'no this' : this.n + a; }})\")] ((. o -f) 1))")
     "no this"
     ;; spilled, it must still mean that
     (str "(let* [o (js* \"({n: 7, f: function(a){ return this === null ||"
          " this === undefined ? 'no this' : this.n + a; }})\")]"
          " ((. o -f) (let* [q 1] q)))")
     "no this"))
  (is (str/includes? (h/js "(def f (fn* ([] 1))) (f)") ".f.call(null)")
      (h/js "(def f (fn* ([] 1))) (f)")))

(h/deftest-when h/node? test-a-host-method-keeps-its-receiver
  ;; The exception, and ClojureScript makes the same one: js/console.log names a
  ;; host METHOD, whose receiver is part of what it is - console.log.call(null) is
  ;; an Illegal invocation in a browser. So a dotted js/ name is called on its
  ;; object, which spills the OBJECT and keeps both the receiver and the order.
  (emits
   "(js/Math.max 1 2)"                        "2"
   ;; the spilled case: a later argument with statements used to give
   ;; `let t = host.m; t(1)`, and `this` was gone
   "(js* \"globalThis.host = { n: 5, m: function(a){ return this.n + a; } }\")
    (js/host.m (let* [q 1] q))"               "6"
   ;; an undotted js/ global has no receiver to lose, so it is called plainly
   "(js/parseInt \"11\" 2)"                   "3")
  (let [js (h/js "(js* \"globalThis.host = {m: function(a){return a}}\")
                  (js/host.m (let* [q 1] q))")]
    ;; the object is what goes into the temporary, not the method
    (is (re-find #"let t\$\d+ = host;" js) js)
    (is (re-find #"t\$\d+\.m\(q__\d+\)" js) js))
  ;; a host CALL always kept its receiver; this pins that it still does
  (is (= "8" (h/output (str "(let* [o (js* \"({n: 7, m: function(a){ return this.n + a; }})\")]"
                            " (. o m (let* [q 1] q)))")))))

(h/deftest-when h/node? test-a-value-nobody-uses-emits-no-line
  ;; a def's value is the property it just assigned, so naming it again does
  ;; nothing - and a do or a let is dead as a statement exactly when its own value
  ;; is, which is what carries that through
  (are [src] (not (re-find #"(?m)^app\$core\$ns\.x;$" (h/js src)))
    "(def x 1) (js* \"0\")"
    "(do (def x 1)) (js* \"0\")"
    "(let* [q 1] (def x q)) (js* \"0\")")
  ;; but a value that CAN throw is still evaluated: dropping the line would
  ;; swallow the TypeError
  (is (= "THREW: Cannot read properties of null (reading 'x')"
         (h/output "(let* [o nil] (do (. o -x))) (js* \"0\")"))))

(h/deftest-when h/node? test-indentation-cannot-change-what-code-means
  ;; A JavaScript literal may span lines, and then its newline is part of its
  ;; VALUE. indent used to rewrite every line of a statement, including the inner
  ;; lines of one of these, which put two spaces inside the string - a silent
  ;; wrong answer, and js* is exactly where raw JavaScript arrives.
  (let [tl   (str "`a" \newline "b`.length")        ; a template literal
        cont (str "\"a\\" \newline "b\".length")]   ; a string continued with \
    (are [src expected] (= expected (h/output src))
      ;; unindented to begin with
      (str "(js* " (pr-str tl) ")")                       "3"
      (str "(js* " (pr-str cont) ")")                     "2"
      ;; and in the three places a statement gets indented: a branch, a spill,
      ;; and a function body
      (str "(if true (js* " (pr-str tl) ") 0)")           "3"
      (str "(js* \"~{} + ~{}\" (js* " (pr-str tl) ") (let* [q 0] q))") "3"
      (str "((fn* [] (js* " (pr-str tl) ")))")            "3"
      (str "((fn* [] (js* " (pr-str cont) ")))")          "2"))
  ;; nesting is still legible: a block's own lines are indented under it
  (let [js (h/js "(let* [x 1] (if x (let* [y 2] y) 3))")]
    (is (str/includes? js "\n  let y__2 = (2);") js)))

;; --- the evaluation unit ----------------------------------------------------
;;
;; doc/cljs-repl.md §5. The same compiled forms, sent to a runtime as a script to
;; evaluate instead of written to disk as a module to import. Everything below is
;; about what that change of destination has to preserve, and what it buys.

(h/deftest-when h/node? test-a-script-is-a-module-with-a-different-destination
  ;; The body has to be the same either way, because §7.1 loads a namespace by
  ;; evaluating it and that only works if evaluating it is importing it. So the
  ;; two paths differ in the last form's destination and nowhere else.
  (are [src expected] (= expected (h/output src) (h/script-output src))
    "42"                                    "42"
    "(def x 41) (let* [y x] y)"             "41"
    "((fn* [a] a) 42)"                      "42"
    ;; a string rather than a keyword, and that is not incidental: a keyword is an
    ;; allocation of a cljs.core type now (§5.10), and these run against the
    ;; prelude ALONE - which is a real configuration, being the world a REPL is in
    ;; before cljs.core has loaded, and the one this test is about
    "(if nil \"a\" \"b\")"                    "b"
    "(loop* [a 3] (if (js* \"~{} > 0\" a) (recur (js* \"~{} - 1\" a)) a))" "0"
    "(js* \"~{} + ~{}\" 1 2)"               "3"))

(h/deftest-when h/node? test-a-script-yields-the-last-form-s-value
  ;; return-value is the seam: the module path passes the same expression to
  ;; console.log, the REPL path returns it out of the IIFE.
  (is (= "3" (h/script-output "(js* \"1\") (js* \"2\") (js* \"3\")")))
  ;; a def's value is the property it just assigned, so a def is a fine last form
  (is (= "7" (h/script-output "(def x 7)"))))

(h/deftest-when h/node? test-a-terminal-form-has-no-value-to-return
  ;; emit-top does not call `f` for a terminal node, so nothing tries to return
  ;; past a throw. The rejection is what the runtime's eval hook sees.
  (is (= "THREW: boom" (h/script-output "(throw (js* \"new Error(\\\"boom\\\")\"))")))
  (is (not (str/includes? (h/script "(throw (js* \"new Error(\\\"boom\\\")\"))")
                          "return"))))

(h/deftest-when h/node? test-each-script-is-its-own-scope
  ;; The reason the unit is a function and not a run of top-level statements. The
  ;; analyzer restarts local numbering at each top-level form, so two consecutive
  ;; REPL inputs both emit x__1; in one shared scope the second `let x__1` is a
  ;; SyntaxError. Do not 'fix' this by emitting var.
  (let [[a b] (h/session ["(let* [x 1] x)" "(let* [x 2] x)"])]
    (is (str/includes? a "x__1"))
    (is (str/includes? b "x__1")))
  (is (= ["1" "2"] (h/session-output ["(let* [x 1] x)" "(let* [x 2] x)"])))
  ;; and within ONE script they share a scope, so there the names must differ
  (is (= "2" (h/script-output "(let* [x 1] x) (let* [x 2] x)"))))

(h/deftest-when h/node? test-a-var-can-be-redefined-across-scripts
  ;; §3.2: a var is a property of a namespace object, and the object outlives the
  ;; script that assigned to it - which is what makes a REPL a REPL.
  (is (= ["1" "1" "2" "2"]
         (h/session-output ["(def x 1)" "x" "(def x 2)" "x"])))
  ;; and a function reads the property when it runs, so it sees the new value
  ;; rather than the one that was there when it was defined
  (let [[_ _ before _ after]
        (h/session-output ["(def x 1)" "(def f (fn* [] x))" "(f)" "(def x 9)" "(f)"])]
    (is (= ["1" "9"] [before after])))
  ;; the registry is what carries this: nothing else survives between scripts
  (is (str/includes? (first (h/session ["(def x 1)"])) "$ns(\"app.core\")")))

(h/deftest-when h/node? test-a-script-binds-the-prelude-from-the-global
  ;; A script may not contain an import declaration, so the names the body spells
  ;; have to arrive some other way. This is the only difference between the two
  ;; prologues, and getting it wrong is `$ns is not defined` at runtime.
  ;;
  ;; ON THE OPENING LINE rather than under it, and the reason is arithmetic rather
  ;; than taste: it is what makes a script's prologue exactly as many lines as the
  ;; module's, so a reloaded body sits at the same line number in both. See
  ;; driver-test/test-a-reloaded-body-sits-where-the-module-does.
  (let [s (h/script "(if nil 1 2)")]
    (is (str/starts-with? s (str "(async function () { const $CLJS = globalThis.$CLJS,"
                                " $ns = $CLJS.ns, truth_ = $CLJS.truth_;\n"))
        s)
    (is (not (str/includes? s "import")) s))
  ;; both names are reached, not just declared
  (is (= "2" (h/script-output "(if nil 1 2)"))))

(deftest test-a-source-url-is-the-last-line
  ;; It is a comment, so anything following it on its line is a comment too. The
  ;; wrapper is the one place that knows where the script ends.
  (let [s (emitter/script ["return 1;"] "repl://app.core/3")]
    (is (str/ends-with? s "\n//# sourceURL=repl://app.core/3"))
    (is (str/includes? s "})()\n//#")))
  (is (not (str/includes? (emitter/script ["return 1;"]) "sourceURL"))))

(deftest test-a-script-is-an-expression
  ;; Its value is a promise, which is what the runtime's eval hook awaits to get
  ;; either the value or the throw. A statement would give eval nothing to return.
  (let [s (emitter/script ["return 1;"])]
    (is (str/starts-with? s "(async function"))
    (is (str/ends-with? s "})()"))
    ;; no try/catch of its own: a rejected promise is already catchable where it
    ;; matters, and a catch here could only rethrow
    (is (not (str/includes? s "catch")))))

(deftest test-emit-top-keeps-its-statements-apart
  ;; script indents per statement, and what is inside a multi-line statement is
  ;; not ours to reflow - so the boundaries have to survive as far as the wrapper.
  ;; Joining them first is what destroys that, which is why emit-top-lines exists.
  (let [node  (h/analyze '(let* [x 1] x))
        lines (emitter/emit-top-lines node emitter/return-value)]
    (is (vector? lines))
    (is (= ["let x__1 = (1);" "return x__1;"] lines))
    (is (= (str/join "\n" lines) (emitter/emit-top node emitter/return-value)))))

;; --- namespaces -------------------------------------------------------------

(deftest test-the-prologue-binds-one-object-per-nameable-namespace
  ;; a var is a property of one of these objects, so the body can only name a
  ;; namespace the prologue bound. cljs.core is always among them, because a
  ;; collection literal calls into it whether or not the file says so
  (is (= ["const app$core$ns = $ns(\"app.core\");"
          "const cljs$core$ns = $ns(\"cljs.core\");"]
         (emitter/ns-prologue 'app.core)))
  (is (= ["const app$core$ns = $ns(\"app.core\");"
          "const cljs$core$ns = $ns(\"cljs.core\");"
          "const my_lib$core$ns = $ns(\"my-lib.core\");"]
         (emitter/ns-prologue 'app.core '#{my-lib.core})))
  ;; requiring yourself, which (:require [app.core]) in app.core would do, binds
  ;; one object rather than declaring the same const twice
  (is (= 2 (count (emitter/ns-prologue 'app.core '#{app.core}))))
  ;; and cljs.core's own module binds it once, as its own namespace
  (is (= ["const cljs$core$ns = $ns(\"cljs.core\");"]
         (emitter/ns-prologue 'cljs.core))))

(deftest test-cljs-core-is-bound-but-not-required
  ;; the split the binding rests on: naming cljs.core costs a $ns line, which
  ;; cannot fail; LOADING it is the implicit require, which waits on there being a
  ;; cljs/core.js to fetch (doc/cljs-compiler.md §5.7)
  (let [lines (emitter/script-prologue 'app.core '#{my-lib.core})]
    (is (= ["await $CLJS.require(\"my-lib.core\");"]
           (filter #(str/includes? % "$CLJS.require") lines)))
    (is (some #(str/includes? % "$ns(\"cljs.core\")") lines))))

(deftest test-a-script-requires-what-a-module-imports
  ;; the two prologues over one body (doc/cljs-repl.md §4): a script may not carry
  ;; an import declaration, so it asks the runtime instead
  (let [lines (emitter/script-prologue 'app.core '#{my-lib.core})]
    (is (= "await $CLJS.require(\"my-lib.core\");" (first lines)))
    ;; the requires complete before anything is bound or used
    (is (= (emitter/ns-prologue 'app.core '#{my-lib.core}) (rest lines))))
  ;; nothing to fetch, nothing emitted
  (is (= (emitter/ns-prologue 'app.core) (emitter/script-prologue 'app.core))))

(h/deftest-when h/node? test-a-namespace-marks-itself-loaded
  ;; set by the body, never inferred from the registry: $ns creates on demand, so
  ;; an object exists as soon as anything REFERENCES a namespace - exactly the
  ;; case require exists to catch
  (is (str/includes? (first (h/session ["(ns app.core)"])) "$CLJS.loaded.add(\"app.core\")"))
  ;; console.log, not the runtime's printer, so a nil arrives as node spells it
  (is (= ["null" "true" "false"]
         (h/session-output (h/fresh-env 'cljs.user)
                           ["(ns app.core)"
                            "(js* \"globalThis.$CLJS.loaded.has(\\\"app.core\\\")\")"
                            ;; merely naming one does not mark it
                            "(js* \"globalThis.$CLJS.loaded.has(\\\"other.ns\\\")\")"]))))

(h/deftest-when h/node? test-a-call-across-namespaces
  (is (= ["null" "[Function: my_lib$core$helper]" "null" "42"]
         (h/session-output
          (h/fresh-env 'cljs.user)
          ["(ns my-lib.core)"
           "(def helper (fn* [] 42))"
           "(ns app.core (:require [my-lib.core :as lib]))"
           "(lib/helper)"]))))

(h/deftest-when h/node? test-a-script-fetches-a-namespace-it-does-not-hold
  ;; The other half of $CLJS.require, and the only thing that exercises the layout
  ;; end to end: the JVM knows my-lib.core because it compiled it, the runtime has
  ;; never seen it, and the only thing connecting them is that runtime.js computes
  ;; the same path from the name that clojure.cljs.output wrote the file at.
  (let [cenv (h/fresh-env 'cljs.user)
        f    (h/write-module! cenv "(ns from.disk) (def answer (fn* [] 42))")]
    (is (str/ends-with? (.getPath f) "ns/from/disk.js"))
    ;; a fresh node: its loaded set is empty, so the require has to fetch
    (is (= ["null" "42"]
           (h/session-output cenv ["(ns app.core (:require [from.disk :as d]))"
                                   "(d/answer)"])))))

;; --- try -------------------------------------------------------------------

(h/deftest-when h/node? test-try-catch-and-finally-run
  ;; The behaviour, under node, form by form. A typed catch is an instanceof test
  ;; and :default is the else, which is all one JavaScript catch parameter can be
  ;; asked to do.
  (is (= "1" (h/run-script (h/script "(try 1 (catch :default e 2))"))))
  (is (= "boom" (h/run-script
                 (h/script "(try (js* \"(function(){ throw new Error('boom') })()\")
                                 (catch :default e (js* \"~{}.message\" e)))"))))
  ;; the clause bodies are strings rather than keywords because these run against
  ;; the prelude alone, with no cljs.core to allocate a keyword from (§5.10);
  ;; :default is a name the COMPILER reads and never emits, so it stays
  (is (= "type" (h/run-script
                 (h/script "(try (js* \"(function(){ throw new TypeError('t') })()\")
                                 (catch js/TypeError e \"type\")
                                 (catch :default e \"other\"))"))))
  ;; a clause whose type does not match falls through to the next one
  (is (= "other" (h/run-script
                  (h/script "(try (js* \"(function(){ throw new RangeError('r') })()\")
                                  (catch js/TypeError e \"type\")
                                  (catch :default e \"other\"))")))))

(h/deftest-when h/node? test-an-unmatched-exception-keeps-travelling
  ;; The else of the chain when there is no :default is a rethrow, not nothing.
  ;; Swallowing here would be the worst kind of quiet: a try written to catch one
  ;; type would silently absorb every other.
  (is (= "THREW: unmatched"
         (h/run-script
          (h/script "(try (js* \"(function(){ throw new Error('unmatched') })()\")
                          (catch js/TypeError e :type))")))))

(h/deftest-when h/node? test-finally-runs-after-the-body-and-through-a-throw
  (is (= "[ 1, 2 ]"
         (h/run-script
          (h/script "(let* [a (js* \"[]\")]
                       (try (js* \"~{}.push(1)\" a) (finally (js* \"~{}.push(2)\" a)))
                       a)"))))
  ;; the inner finally runs on the way out, and the outer catch still sees it
  (is (= "[ 'fin', 'caught' ]"
         (h/run-script
          (h/script "(let* [a (js* \"[]\")]
                       (try (try (js* \"(function(){ throw 1 })()\")
                                 (finally (js* \"~{}.push('fin')\" a)))
                            (catch :default e (js* \"~{}.push('caught')\" a)))
                       a)")))))

(deftest test-a-try-needs-no-function-wrapper
  ;; The fourth place, after if, case and throw, where ClojureScript reaches for an
  ;; immediately-invoked function and destination-driven emission does not.
  (let [js (h/script "(js* \"~{} + 1\" (try 41 (catch :default e 0)))")]
    (is (str/includes? js "try {"))
    (is (str/includes? js "catch ("))
    ;; one IIFE only - the evaluation unit's own
    (is (= 1 (count (re-seq #"\(async function" js))))
    (is (not (re-find #"\(function \(\)\{" js))))
  (is (= "42" (h/run-script (h/script "(js* \"~{} + 1\" (try 41 (catch :default e 0)))")))))

(deftest test-a-try-with-neither-catch-nor-finally-is-a-do
  (let [plain (h/script "(do 1)")
        tried (h/script "(try 1)")]
    (is (= plain tried))))

(h/deftest-when h/node? test-a-wrapper-would-make-await-in-a-try-uncompilable
  ;; Where the missing function wrapper stops being a tidiness argument. An
  ;; evaluation unit is an async IIFE (doc/cljs-repl.md 5), so `await` is legal in
  ;; it - but only until a second, non-async wrapper goes round the try, which is
  ;; exactly what cljs.compiler emits for a try in expression position.
  (is (= "7" (h/run-script
              (h/script "(try (js* \"await Promise.resolve(7)\")
                              (catch :default e :no))"))))
  ;; the same thing wrapped by hand, to show what the wrapper costs
  (is (re-find #"await is only valid in async functions"
               (h/run-script
                (h/script "(js* \"(function () { try { return await Promise.resolve(7) }
                                                catch (e) { return 0 } })()\")")))))

;; --- the collection literals -------------------------------------------------
;;
;; A vector, map, set or list is an object of a type cljs.core defines, so what
;; is checked here is a CALL SHAPE: the right constructor, the right arguments,
;; in the right order. cljs.core itself does not run yet, so the types are stood
;; in for - which is not a weaker test than the real ones would be, because the
;; stand-ins report what they were handed and the real types would not.

(def ^:private core-types
  "Stand-ins for the cljs.core types a collection literal names, defined IN
  cljs.core so that they land on the same namespace object the literals read.

  Each records its arguments rather than building anything, so a test can ask
  what the emitted call passed. .-EMPTY-NODE is written with the hyphen core.cljs
  writes it with, which is the point of pinning it: the literal spells that
  property EMPTY_NODE, and the two only meet because a property access is spelled
  the host's way (clojure.cljs.names/host-name)."
  (str "(def List (js* \"function(){}\"))\n"
       "(set! (.-EMPTY List) \"()\")\n"
       "(def list (js* \"function(){ return 'list:' + Array.prototype.slice.call(arguments).join(','); }\"))\n"
       "(def PersistentVector (js* \"function(m,c,s,r,tail,h){ this.v = tail; this.node = r; this.cnt = c; }\"))\n"
       "(set! (.-EMPTY PersistentVector) \"[]\")\n"
       "(set! (.-EMPTY-NODE PersistentVector) \"NODE\")\n"
       "(set! (.-fromArray PersistentVector) (js* \"function(a,b){ return 'fromArray:' + a.length + ':' + b; }\"))\n"
       "(def PersistentArrayMap (js* \"function(m,c,arr,h){ this.v = arr; this.cnt = c; }\"))\n"
       "(set! (.-EMPTY PersistentArrayMap) \"{}\")\n"
       "(set! (.-createAsIfByAssoc PersistentArrayMap) (js* \"function(a){ return 'assoc:' + JSON.stringify(a); }\"))\n"
       "(def PersistentHashSet (js* \"function(m,map,h){ this.v = map; }\"))\n"
       "(set! (.-EMPTY PersistentHashSet) \"#{}\")\n"
       "(set! (.-createAsIfByAssoc PersistentHashSet) (js* \"function(a){ return 'set-assoc:' + JSON.stringify(a); }\"))\n"
       "(def PersistentHashMap (js* \"function(){}\"))\n"
       "(set! (.-fromArrays PersistentHashMap) (js* \"function(ks,vs){ return 'hash:' + ks.length + ':' + vs.length; }\"))\n"
       ;; A keyword and a symbol are allocations too now (§5.10), so they need
       ;; stand-ins like the collections do. Each reports itself as the text it
       ;; used to BE, which is what keeps these tests on their own subject: what a
       ;; collection literal passes its constructor, not what a keyword is.
       "(def Keyword (js* \"function(ns,name,fqn,h){ this.fqn = fqn; this.h = h; this.toJSON = function(){ return ':' + fqn; }; }\"))\n"
       "(def Symbol (js* \"function(ns,name,s,h,m){ this.s = s; this.h = h; this.toJSON = function(){ return s; }; }\"))\n"))

(defn- built
  "`src` compiled in cljs.core, over the stand-ins, and run.

  In cljs.core because that is where the stand-ins have to be defined: a literal
  reads cljs.core's namespace object whatever namespace it appears in, so the
  only way to put something there is to be there."
  [src]
  (h/run-js (h/js (h/fresh-env 'cljs.core) (str core-types src))))

(defmacro ^:private builds
  [& pairs]
  `(are [src# expected#] (= expected# (built src#)) ~@pairs))

(h/deftest-when h/node? test-an-empty-collection-is-a-shared-value
  ;; EMPTY, not a fresh allocation, for all four - which is why they are the one
  ;; case with no constructor call at all
  (builds
   "[]"  "[]"
   "{}"  "{}"
   "#{}" "#{}"
   ;; () is a value rather than a call, and it used to emit the literal text `()`
   "()"  "()"))

(h/deftest-when h/node? test-a-small-vector-is-its-own-tail
  ;; under 32 elements a vector IS its tail, so it is built directly rather than
  ;; through fromArray's trie walk
  (builds
   "(js/JSON.stringify (.-v [1 2 3]))" "[1,2,3]"
   "(.-cnt [1 2 3])"                   "3"
   ;; the property core.cljs writes as .-EMPTY-NODE and we read as EMPTY_NODE
   "(.-node [1])"                      "NODE"
   ;; and at 32 the other path, which is why the boundary is worth a test
   "(.-cnt [1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31])" "31"
   "[1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32]"
   "fromArray:32:true"))

(h/deftest-when h/node? test-a-map-is-an-array-map-until-it-is-not
  (builds
   "(js/JSON.stringify (.-v {:a 1 :b 2}))" "[\":a\",1,\":b\",2]"
   "(.-cnt {:a 1 :b 2})"                   "2"
   ;; nine entries is one past PersistentArrayMap's own threshold, and the two
   ;; arrays go over separately. Their ORDER is a hash map's business and not
   ;; ours, so only the count is asserted
   "{:a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8 :i 9}" "hash:9:9"
   ;; and eight is still an array map
   "(.-cnt {:a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8})" "8"
   ;; keys that cannot be shown to differ go through assoc, which is the only
   ;; thing that can collapse two of them into one entry at run time
   "{1 :a 1.0 :b}" "assoc:[1,\":a\",1,\":b\"]"
   "(let* [k 1] {k :a 2 :b})" "assoc:[1,\":a\",2,\":b\"]"))

(h/deftest-when h/node? test-a-set-is-a-hash-set-over-an-array-map
  (builds
   "(js/JSON.stringify (.-v (.-v #{1 2})))" "[1,null,2,null]"
   ;; 1 and 1.0 are two Clojure members and one JavaScript number, so they are
   ;; not known to be distinct - cljs.compiler says they are, and builds a set
   ;; holding the same member twice
   ;; (JSON.stringify prints both as 1, which is exactly the point)
   "#{1 1.0}" "set-assoc:[1,1]"))

(h/deftest-when h/node? test-a-quoted-collection-is-one-constant
  ;; nothing inside a quote evaluates, so the whole structure is built in one
  ;; expression, symbol allocations and all
  (builds
   "(quote (1 2 3))"                       "list:1,2,3"
   "(quote ())"                            "()"
   "(js/JSON.stringify (.-v (quote [a b])))" "[\"a\",\"b\"]"))

(h/deftest-when h/node? test-the-two-literals-that-need-no-core
  ;; a JavaScript array, object and regex are the host's own, and a character is
  ;; a one-character string because ClojureScript has no character type
  (builds
   "(js/JSON.stringify #js [1 2])"        "[1,2]"
   "(js/JSON.stringify #js {:a 1 :b \"x\"})" "{\"a\":1,\"b\":\"x\"}"
   ;; the key is a property name however it is written
   "(js/JSON.stringify #js {\"a\" 1})"    "{\"a\":1}"
   "(.test #\"^ab\" \"abc\")"             "true"
   ;; Clojure spells its flags at the front, JavaScript at the end
   "(.test #\"(?i)^AB\" \"abc\")"         "true"
   ;; and a slash inside the pattern would otherwise close the literal
   "(.test #\"a/b\" \"a/b\")"             "true"
   "\\x"                                  "x"))

(h/deftest-when h/node? test-elements-are-evaluated-left-to-right
  ;; the same in-order rule every other node gets: a later element contributing
  ;; statements pins an earlier one in a temporary rather than letting it float
  (builds
   ;; the second element is a let*, which contributes a STATEMENT - so the first
   ;; has to be spilled into a temporary rather than left to float past it
   "(def out (js* \"[]\"))
    (def f (fn* ([x] (do (.push out x) x))))
    [(f 1) (let* [y (f 2)] y)]
    (js/JSON.stringify out)" "[1,2]"
   ;; a map evaluates key, value, key, value
   "(def out (js* \"[]\"))
    (def f (fn* ([x] (do (.push out x) x))))
    {(f 1) (f 2) (f 3) (let* [y (f 4)] y)}
    (js/JSON.stringify out)" "[1,2,3,4]"
   ;; a SET is the exception, and the exception is the set's rather than ours: its
   ;; elements are a set by the time the analyzer sees them, so they are evaluated
   ;; in iteration order and the source order is already gone. ClojureScript does
   ;; the same. What survives is the part that is ours - an element contributing
   ;; statements still pins the ones before it, in whatever order those are
   "(def out (js* \"[]\"))
    (def f (fn* ([x] (do (.push out x) x))))
    #{(f 1) (let* [y (f 2)] y)}
    (js/JSON.stringify (.sort out))" "[1,2]"
   ;; #js is no different: it is the elements that need ordering, not the type
   "(def out (js* \"[]\"))
    (def f (fn* ([x] (do (.push out x) x))))
    #js [(f 1) (let* [y (f 2)] y)]
    (js/JSON.stringify out)" "[1,2]"
   ;; an element that never returns takes the literal with it, with no function
   ;; wrapper to say so
   "[1 (throw (js/Error. \"cut\")) 3]" "THREW: cut"))

(deftest test-the-three-tagged-literals-are-spelled
  ;; doc/cljs-compiler.md §5.22, and every spelling below was read off stock
  ;; ClojureScript rather than guessed.
  (are [src expected] (str/includes? (h/js src) expected)
    ;; #inst - a host Date, from the epoch milliseconds of the Instant our reader
    ;; built. `Date` is written as a JavaScript global, as regex-js writes
    ;; `new RegExp`.
    "(def a #inst \"2020-01-02T03:04:05.678-00:00\")"
    "(new Date((1577934245678)))"
    ;; BEFORE 1582, where Clojure's java.util.Date is Julian and JavaScript's
    ;; Date is proleptic Gregorian. Read as a Date these were nine days early and
    ;; silently so; read as a java.time.Instant they are these, which is what
    ;; stock ClojureScript emits and what their reader-test/testing-cljs-3291
    ;; asserts. See clojure.cljs.reader/cljs-data-readers.
    "(def a #inst \"1500-01-10T00:00:00.000-00:00\")"
    "(new Date((-14830992000000)))"
    "(def a #inst \"1582-10-14T00:00:00.000-00:00\")"
    "(new Date((-12219379200000)))"
    ;; #uuid - a cljs.core type, so core-name like Keyword and Symbol. THE HASH IS
    ;; THE HASH OF ITS STRING, not of the UUID: cljs.core hashes the text, and
    ;; Clojure's hash of that same text is the same number. ClojureScript emits
    ;; this exact pair.
    "(def b #uuid \"550e8400-e29b-41d4-a716-446655440000\")"
    "(new cljs$core$ns.UUID(\"550e8400-e29b-41d4-a716-446655440000\", (-257403564)))")

  ;; #queue needs nothing here at all: reader/read-queue hands back a FORM, so
  ;; what is emitted is an ordinary call and its elements are expressions
  (is (= '(cljs.core/into cljs.core.PersistentQueue.EMPTY [1 2])
         (clojure.cljs.reader/read-queue '[1 2]))))

(deftest test-metadata-on-a-literal-reaches-the-value
  ;; doc/cljs-compiler.md §5.21, and the failure it fixes was a WRONG ANSWER:
  ;; ^{:b :c} [1 2] and [1 2] emitted byte-identical JavaScript, so a program
  ;; could write metadata and read nil back. Five assertions of
  ;; cljs.seqs-test/test-empy-and-seq are this bug, and running them is where the
  ;; fix is actually observed - here is the emission it turns on.
  (are [src] (str/includes? (h/js src) "with_meta.call(null, ")
    "(def x ^{:b :c} [1 2])"
    "(def x ^{:b :c} {:a 1})"
    "(def x ^{:b :c} #{1})"
    ;; the QUOTED half, which the emitter carries rather than the analyzer: a
    ;; quoted structure is one constant, and the metadata on every piece of it is
    ;; as much a constant as the piece
    "(def x (quote ^{:b :c} (1 2 3)))"
    "(def x (quote ^{:b :c} ()))"
    "(def x (quote [^{:a 1} [9]]))")

  ;; NOT the reader's own keys. Every collection carries :line and :column, so
  ;; without eliding them every literal in the file would allocate a map of line
  ;; numbers and (meta [1 2]) would answer one.
  (are [src] (not (str/includes? (h/js src) "with_meta"))
    "(def x [1 2])"
    "(def x {:a 1})"
    "(def x (quote (1 2)))"
    ;; an fn* with nothing on it but the reader's keys, like any other literal
    "(def x (fn* ([] 1)))"
    ;; and one carrying only the three keys cljs.core/dt->et puts on every
    ;; protocol method, which are the annotator's rather than the program's
    ;; (§5.30) - without dropping them, every protocol method in cljs.core would
    ;; be built by calling with-meta, most of them before with-meta exists
    (str "(def x ^#:clojure.cljs.analyzer{:type T"
         " :protocol-impl true :protocol-inline false} (fn* ([] 1)))"))

  ;; an fn* IS wrapped when the metadata is the program's (§5.30)
  (is (str/includes? (h/js "(def x ^:once (fn* ([] 1)))") "with_meta.call(null, "))

  ;; the metadata is a map literal like any other, so a value in it is an
  ;; expression - and in-order puts the collection before it, which is the order
  ;; Clojure evaluates in
  (let [js (h/js "(def f (fn* ([x] x))) (def x ^{:a (f 1)} [(f 2)])")]
    (is (str/includes? js "with_meta.call(null, ") js)
    (is (< (.indexOf js "(2)") (.indexOf js "(1)")) js)))

(deftest test-a-boolean-test-skips-truth
  ;; §5.32. truth_ and JavaScript are not the same question: truth_(x) is
  ;; x != null && x !== false, so "" and 0 are TRUE, while `if (x)` makes both
  ;; false. So the check cannot simply be dropped - it is dropped exactly where a
  ;; program has said the value is already a JavaScript boolean, and nowhere else.
  ;; cljs/binding_test.cljs asserts the difference at "" with a ^boolean var.
  (let [cenv (h/core-env 'app.bt)]
    (h/analyze cenv '(def ^boolean tagged false))
    (h/analyze cenv '(def untagged false))
    (is (str/includes? (h/js cenv "(if untagged 1 2)") "truth_("))
    (is (not (str/includes? (h/js cenv "(if tagged 1 2)") "truth_(")))

    (testing "a ^boolean defn is a RETURN tag, so the call is what loses truth_"
      (h/analyze cenv '(defn ^boolean p [x] false))
      (h/analyze cenv '(defn q [x] false))
      (is (not (str/includes? (h/js cenv "(if (p 1) 1 2)") "truth_(")))
      (is (str/includes? (h/js cenv "(if (q 1) 1 2)") "truth_(")))

    (testing "and a js* that cljs.core/bool-expr marked"
      ;; the hot case by far: (nil? x) is a MACRO expanding to (coercive-= x nil),
      ;; so it never reaches an :invoke and the tag has to ride on the js*
      (is (not (str/includes? (h/js cenv "(if (nil? 1) 1 2)") "truth_(")))
      (is (not (str/includes? (h/js cenv "(if (identical? 1 2) 1 2)") "truth_(")))
      ;; something inlined that is NOT a boolean keeps its check
      (is (str/includes? (h/js cenv "(if (aget (array 1) 0) 1 2)") "truth_(")))

    (testing "and a ^boolean local"
      (is (not (str/includes? (h/js cenv "(let [^boolean x true] (if x 1 2))")
                              "truth_(")))
      (is (str/includes? (h/js cenv "(let [x true] (if x 1 2))") "truth_(")))))

(deftest test-a-literal-names-cljs-core-wherever-it-appears
  ;; the reason the prologue binds cljs.core in every module: this file never
  ;; mentions it, and the emitted code cannot run without it
  (let [js (h/js "(def v [1 2])")]
    (is (str/includes? js "const cljs$core$ns = $ns(\"cljs.core\");") js)
    (is (str/includes? js "cljs$core$ns.PersistentVector") js)))

(deftest test-an-empty-literal-is-dropped-as-a-statement
  ;; allocating a collection does nothing observable, so a literal is dead as a
  ;; statement exactly when its elements are
  (let [dead (h/js "(def a [1 2]) (def b 1)")]
    (is (not (str/includes? dead "\n[1, 2];")) dead))
  ;; but an element with an effect keeps the line
  (let [live (h/js "(def f (fn* ([] 1))) (do [(f)] 2)")]
    (is (str/includes? live "PersistentVector") live)))

;; --- host globals ------------------------------------------------------------

(h/deftest-when h/node? test-an-unknown-prefix-runs-as-a-javascript-global
  ;; Math/floor means Math.floor, and there is nothing between the two: no
  ;; namespace object, no import, no externs. This is what §5.8 bought, and the
  ;; test is that node agrees.
  (are [src expected] (= expected (h/run-js (h/js src)))
    "(Math/floor 1.5)"          "1"
    "(Math/imul 3 4)"           "12"
    "(Math/max 1 7 3)"          "7"
    "Math/PI"                   "3.141592653589793"
    "(String/fromCharCode 65)"  "A"
    ;; the receiver survives, as it does for a dotted js/ name: Math.floor called
    ;; with the wrong `this` is a different function in some hosts, and taking the
    ;; method off its object is what would do that
    "(let* [f 1] (Math/abs -3))" "3"))

(deftest test-a-host-global-emits-the-name-and-nothing-else
  (let [js (h/js "(def x (Math/floor 1.5))")]
    (is (str/includes? js "Math.floor(1.5)") js)
    ;; no namespace object was invented for Math, and none could be
    (is (not (str/includes? js "$ns(\"Math\")")) js))
  ;; a goog namespace does not fall through to the host either, and does not need
  ;; to: writing the name out is the require (doc/cljs-compiler.md §5.18), so it
  ;; goes through $ns like any other namespace rather than becoming a global path.
  (let [js (h/js "(def o 1) (def x (goog.object/get o 1))")]
    ;; the prologue binds it, which is what the recorded require buys
    (is (str/includes? js "const goog$object$ns = $ns(\"goog.object\");") js)
    (is (str/includes? js "goog$object$ns.get(") js)))

;; --- qualified methods -------------------------------------------------------

(deftest test-a-qualified-method-emits-the-closure-clojurescript-emits
  ;; the shape is stock ClojureScript's, verbatim (compiler.cljc:1318). Reflect
  ;; rather than a bound method because the receiver has to be an ORDINARY first
  ;; argument - that is what lets (map String/.toUpperCase coll) work - and
  ;; Reflect.construct because spreading arguments into a constructor has no other
  ;; spelling.
  (let [js (h/js "(ns app.core (:refer-global :only [String]))
                  (def f String/.toUpperCase)")]
    (is (str/includes?
         js "(function (x, ...args) { return Reflect.apply(String.prototype.toUpperCase, x, args); })")
        js))
  (let [js (h/js "(ns app.core (:refer-global :only [Object]))
                  (def f Object/new)")]
    (is (str/includes?
         js "(function (...args) { return Reflect.construct(Object, args); })")
        js))
  ;; a goog class reaches its namespace object, and naming it was the require
  (let [js (h/js "(ns app.core) (def f goog.string.StringBuffer/new)")]
    (is (str/includes? js "const goog$string$StringBuffer$ns = $ns(\"goog.string.StringBuffer\");") js)
    (is (str/includes? js "Reflect.construct(goog$string$StringBuffer$ns, args)") js)))

(h/deftest-when h/node? test-a-qualified-method-runs
  (let [run #(h/output-with-core
              (h/core-env)
              (str "(ns app.core (:refer-global :only [Object String])) " %))]
    ;; in call position it is a call of that closure - one reading everywhere
    (is (= "FOO" (run "(String/.toUpperCase \"foo\")")))
    ;; and as a value, which is the point of the form
    (is (= "(\"FOO\" \"BAR\" \"BAZ\")"
           (run "(cljs.core/pr-str
                   (cljs.core/map String/.toUpperCase [\"foo\" \"bar\" \"baz\"]))")))
    (is (= "true" (run "(cljs.core/some? (Object/new))")))
    (is (= "true" (run "(let* [f Object/new] (cljs.core/some? (f)))")))))

(deftest test-loop-bindings-are-sequential
  ;; A loop's bindings are sequential, exactly as a let's are: the second init sees
  ;; the FIRST LOOP BINDING, not whatever that name meant outside. The analyzer
  ;; always resolved it that way; a recurring loop's inits are computed into
  ;; carriers, and the binding's own name was only declared inside the while - so
  ;; the reference was to a variable that did not exist yet.
  ;;
  ;; cljs/pprint.cljc has one, and it cost every cl-format directive that pads:
  ;; `ReferenceError: strs__2222 is not defined`, 18 of pprint-test's assertions.
  (let [js (h/js "(loop* [a 1 b (js* \"~{} + 1\" a)] (if (js* \"~{} > 10\" b) b (recur b a)))")]
    ;; the own name is declared from the carrier before the next init reads it
    (is (re-find #"let (t\$\d+) = \(1\);\nlet (a__\d+) = \1;\nlet t\$\d+ = \2 \+ 1;" js) js))

  (testing "and it is not emitted for the last binding, which nothing can read"
    (let [js (h/js "(loop* [a 1 b 2] (if (js* \"~{} > 10\" b) b (recur b a)))")]
      ;; a gets the alias line, b does not
      (is (re-find #"let a__\d+ = t\$\d+;" js) js)
      (is (not (re-find #"let b__\d+ = t\$\d+;\nwhile" js)) js)))

  (testing "a loop nobody recurs to keeps its own names and needs none of this"
    (let [js (h/js "(loop* [a 1 b (js* \"~{} + 1\" a)] b)")]
      (is (not (str/includes? js "while")) js)
      (is (not (re-find #"let t\$" js)) js))))

(h/deftest-when h/node? test-a-sequential-loop-binding-runs
  (is (= "10" (h/output-with-core
               (h/core-env)
               "(loop [xs [1 2 3 4] n (cljs.core/count xs) acc 0]
                  (if (cljs.core/seq xs)
                    (recur (cljs.core/rest xs) n (cljs.core/+ acc (cljs.core/first xs)))
                    acc))")))
  ;; the shape pprint has: a later init reads an earlier LOOP binding
  (is (= "true" (h/output-with-core
                 (h/core-env)
                 "(loop [strs [\"a\"] one? (cljs.core/= 1 (cljs.core/count strs))]
                    (if (cljs.core/seq strs) (recur (cljs.core/rest strs) one?) one?))"))))

;; --- ^:async and await -------------------------------------------------------

(deftest test-an-async-fn-is-one-keyword-in-the-output
  ;; §5.28. ^:async is a prefix on the function expression and nothing else, which
  ;; is what the destination-driven emitter buys: a let, a loop, a case or a try in
  ;; expression position is STATEMENTS in the enclosing function, so an await
  ;; nested in one is still an await in this function.
  (let [js (h/js "(fn* ([x] x))")]
    (is (not (str/includes? js "async function")) js))
  (let [js (h/js "(^:async fn* ([x] x))")]
    (is (str/includes? js "(async function(") js))
  (testing "several arities are one function, so one keyword covers them"
    (let [js (h/js "(^:async fn* ([x] x) ([x y] y))")]
      (is (= 1 (count (re-seq #"async function" js))) js)))
  (testing "a variadic fn marks both halves: the entry point returns what the"
    ;; delegate returned, and applyTo hands the same promise on
    (let [js (h/js "(^:async fn* ([x & ys] ys))")]
      (is (= 2 (count (re-seq #"async function" js))) js)))
  (testing "a nested plain fn is not async"
    (let [js (h/js "(^:async fn* ([x] (fn* ([] 1))))")]
      (is (= 1 (count (re-seq #"async function" js))) js))))

(deftest test-await-needs-an-async-context
  ;; core.cljc's await asserts on (:async &env), so the env has to carry the flag
  ;; into the body - and has to clear it again for a plain fn nested inside one.
  ;; the assert is core.cljc's own, so what comes back is an AssertionError rather
  ;; than the analyzer's ExceptionInfo - which h/message does not catch
  (let [cenv    (h/core-env)
        refused #(try (h/js cenv %) nil (catch Throwable t (.getMessage t)))]
    (is (nil? (refused "(^:async fn* ([x] (cljs.core/await x)))")))
    (is (re-find #"await can only be used in async contexts"
                 (refused "(fn* ([x] (cljs.core/await x)))")))
    (testing "a let inside an async fn is still inside it"
      (is (nil? (refused "(^:async fn* ([x] (let* [y (cljs.core/await x)] y)))"))))
    (testing "a plain fn inside an async one is not"
      (is (re-find #"await can only be used in async contexts"
                   (refused "(^:async fn* ([x] (fn* ([] (cljs.core/await x)))))"))))))

(h/deftest-when h/node? test-an-async-fn-runs
  (is (= "30" (h/output-with-core
               (h/core-env)
               "(def f (^:async fn* ([x] (cljs.core/+ x (cljs.core/await (js/Promise.resolve 20))))))
                (js* \"await ~{}\" (f 10))")))
  (testing "awaiting inside a nested let, which needs no wrapper here"
    (is (= "3" (h/output-with-core
                (h/core-env)
                "(def f (^:async fn* ([] (let* [a (cljs.core/await (js/Promise.resolve 1))
                                                b (let* [c (cljs.core/await (js/Promise.resolve 2))] c)]
                                           (cljs.core/+ a b)))))
                 (js* \"await ~{}\" (f))"))))
  (testing "and inside a loop"
    (is (= "6" (h/output-with-core
                (h/core-env)
                "(def f (^:async fn* ([] (loop* [n 3 acc 0]
                                           (if (cljs.core/zero? n)
                                             acc
                                             (recur (cljs.core/dec n)
                                                    (cljs.core/+ acc (cljs.core/await (js/Promise.resolve n)))))))))
                 (js* \"await ~{}\" (f))"))))
  (testing "a variadic async fn, reached through apply"
    (is (= "6" (h/output-with-core
                (h/core-env)
                "(def f (^:async fn* ([x & ys] (cljs.core/apply cljs.core/+ (cljs.core/await (js/Promise.resolve x)) ys))))
                 (js* \"await ~{}\" (cljs.core/apply f 1 [2 3]))")))))

(h/deftest-when h/node? test-defn-carries-async-from-the-name
  ;; (defn ^:async foo ...) is (def ^:async foo (fn foo ...)): the mark is on the
  ;; DEF's name, so parse-def moves it onto the init form's head before the body is
  ;; analysed. Without that step the body would be analysed non-async and `await`
  ;; would refuse before anything could notice the fn was meant to be one.
  (is (= "11" (h/output-with-core
               (h/core-env)
               "(defn ^:async foo [n] (cljs.core/+ n (cljs.core/await (js/Promise.resolve 1))))
                (js* \"await ~{}\" (foo 10))"))))

;; --- js/goog is the subset, not the host ------------------------------------

(deftest test-js-goog-is-the-vendored-closure
  ;; §5.28. base.js keeps `goog` off globalThis on purpose, so js/goog read the way
  ;; every other js/ name is read would be a ReferenceError at load. It is read as
  ;; the Closure name it spells instead - and records its own require, like any
  ;; written-out Closure name.
  (let [js (h/js "js/goog")]
    (is (str/includes? js "$ns(\"goog\")") js))
  (testing "a dotted one splits into a namespace and a var, as the bare name does"
    (let [js (h/js "(js/goog.string.urlDecode \"a+b\")")]
      (is (str/includes? js "const goog$string$ns = $ns(\"goog.string\");") js)
      (is (str/includes? js "goog$string$ns.urlDecode(") js)))
  (testing "and everything else about js/ is unchanged"
    (let [js (h/js "js/googleThing")]
      (is (str/includes? js "console.log(googleThing)") js)
      (is (not (str/includes? js "$ns(\"goog")) js))))

(h/deftest-when h/node? test-js-goog-runs
  ;; the three spellings cljs/ns_test.cljs writes in one form, which there are the
  ;; same object by accident of layout and here by rule
  (is (= "true" (h/output "(ns app.g (:require [goog :as goog-alias]))
                           (js* \"~{} && ~{} && ~{}\"
                                (.isArrayLike js/goog (js* \"[1]\"))
                                (goog/isArrayLike (js* \"[1]\"))
                                (goog-alias/isArrayLike (js* \"[1]\")))")))
  (is (= "a b" (h/output "(js/goog.string.urlDecode \"a+b\")"))))

;; --- the arity a caller wrote ------------------------------------------------

(deftest test-the-arity-error-counts-what-the-caller-wrote
  ;; §5.29. A protocol method's first parameter is the object it was called on, so
  ;; arguments.length is one more than the arity anyone asked for. ({} 1 2 3) is
  ;; PersistentArrayMap.prototype.call(map, 1, 2, 3) and must say 3.
  ;;
  ;; cljs.compiler emits the same two spellings, chosen the same way
  ;; (compiler.cljc:1096).
  (let [js (h/js "(fn* ([a] a) ([a b] b))")]
    (is (str/includes? js "\"Invalid arity: \" + arguments.length") js))
  (testing "and one fewer when the first parameter is the receiver"
    ;; self__ is the name cljs.core's adapt-ifn-params uses; ::ana/method-target is
    ;; the marker it uses when the deftype named a self. Either one is enough.
    (let [js (h/js "(fn* ([self__ a] a) ([self__ a b] b))")]
      (is (str/includes? js "\"Invalid arity: \" + (arguments.length - 1)") js))))

(h/deftest-when h/node? test-the-arity-error-message-runs
  (are [src expected] (= expected (h/output-with-core
                                   (h/core-env)
                                   (str "(try " src " (catch :default e (.-message e)))")))
    ;; a map, whose call is a protocol method and so carries the receiver
    "({})"                              "Invalid arity: 0"
    "({} 1 2 3)"                        "Invalid arity: 3"
    ;; and an ordinary multi-arity fn, which does not. (A SINGLE-arity fn checks
    ;; nothing at all - it is a plain JavaScript function and extra arguments are
    ;; ignored, here as in ClojureScript.)
    "((cljs.core/fn ([a] a) ([a b] b)) 1 2 3)" "Invalid arity: 3"))

(deftest test-a-call-goes-straight-to-the-arity-that-answers-it
  ;; §5.33. A multi-arity function is a dispatch function plus one property per
  ;; arity; core.cljc emits both, and a call that goes through the dispatcher has
  ;; it read `arguments`, switch on its length and forward to the property the call
  ;; site could have named itself.
  ;;
  ;; BOUND TRUE RATHER THAN LEFT TO THE DEFAULT, because the default is false
  ;; (§5.44): this is what optimized compilation emits, and it is asked for by
  ;; name. The last block below is the one that shows what a compile gets without
  ;; asking.
  (binding [emitter/*static-dispatch* true]
    (let [cenv (h/core-env 'app.sd)]
      (h/analyze cenv '(defn two ([x] x) ([x y] y)))
      (h/analyze cenv '(defn rest-arg [a & xs] xs))
      (h/analyze cenv '(defn one [x] x))

      (testing "a fixed arity names its property"
        (is (str/includes? (h/js cenv "(two 1)")
                           "two.cljs$core$IFn$_invoke$arity$1((1))"))
        (is (str/includes? (h/js cenv "(two 1 2)")
                           "two.cljs$core$IFn$_invoke$arity$2((1), (2))")))

      (testing "a rest arity gets the seq the dispatch function would have built"
        (let [js (h/js cenv "(rest-arg 1 2 3)")]
          (is (str/includes? js "rest_arg.cljs$core$IFn$_invoke$arity$variadic((1), ")
              js)
          (is (str/includes? js "array_seq.call(null, [(2), (3)], (0))") js)))

      (testing "a call the shape does not answer is left to the dispatch function"
        ;; (rest-arg 1) is one argument on a fn whose only method takes a rest arg,
        ;; so there is no fixed arity 1 to name - and a wrong guess here would be a
        ;; call to undefined rather than the `Invalid arity` the dispatcher throws
        (is (str/includes? (h/js cenv "(rest-arg 1)") "rest_arg.call(null, (1))")))

      (testing "a single-method fn has no arity property, so nothing changes"
        (is (str/includes? (h/js cenv "(one 1)") "one.call(null, (1))")))

      (testing "the RECEIVER is what spills, not the property read off it"
        ;; an argument that contributes statements makes in-order pin the head in a
        ;; temporary; what has to be pinned is the function, because the property is
        ;; a method call on it and a spilled method would lose `this`
        (let [js (h/js cenv "(two 1 (let* [y 2] y))")]
          (is (re-find #"t\$\d+ = app\$sd\$ns\.two;" js) js)
          (is (re-find #"t\$\d+\.cljs\$core\$IFn\$_invoke\$arity\$2\(" js) js)))

      ;; which is the default a file and a REPL input are now both compiled with
      (testing "and none of it happens when static dispatch is off"
        (binding [emitter/*static-dispatch* false]
          (is (str/includes? (h/js cenv "(two 1 2)") "two.call(null, (1), (2))")))))))

(deftest test-static-dispatch-is-off-unless-a-caller-asks
  ;; §5.44, and worth an assertion of its own because it is the whole of that
  ;; section: a call site that names an arity does not survive the var being
  ;; redefined without it, which is a trade a whole-program build can make and a
  ;; reloadable file cannot. The driver turns it on for a caller that passes
  ;; :static-dispatch; nothing else does.
  (is (false? emitter/*static-dispatch*)))

(h/deftest-when h/node? test-the-variadic-entry-point-is-replaceable
  ;; §5.35. A variadic function's body lives on cljs$core$IFn$_invoke$arity$variadic,
  ;; which is an ENTRY POINT rather than the body's only home: a program is allowed
  ;; to replace it, and cljs.spec.test.alpha's instrument does exactly that, so a
  ;; static call site reaches the instrumented function. Replacing it must redirect
  ;; CALLERS, never rewrite the function.
  ;;
  ;; It used to rewrite it, because the entry point read the property to find its
  ;; own body. So (stest/instrument 'cljs.core/=) left = answering (= 1 nil) for
  ;; every call - the replacement receives the rest seq as one argument, not as the
  ;; arguments it stands for - and every test after it in cljs/spec/test_test.cljs
  ;; failed on a broken =. ClojureScript calls a closed-over __delegate here
  ;; (compiler.cljc:1012) and has never had the question.
  (let [run #(h/output-with-core (h/core-env) %)]
    (testing "the function keeps its own body when the property is replaced"
      (is (= "[[1 2 3] :replaced [1 2 3]]"
             (run "(def f (fn [& xs] (vec xs)))
                   (let [before (f 1 2 3)
                         orig   (.-cljs$core$IFn$_invoke$arity$variadic f)]
                     (set! (.-cljs$core$IFn$_invoke$arity$variadic f) (fn [_] :replaced))
                     (pr-str [before
                              (.cljs$core$IFn$_invoke$arity$variadic f nil)
                              (f 1 2 3)]))"))))

    (testing "and so does apply, which reaches the body the same way"
      (is (= "[1 2 3]"
             (run "(def f (fn [& xs] (vec xs)))
                   (set! (.-cljs$core$IFn$_invoke$arity$variadic f) (fn [_] :replaced))
                   (pr-str (apply f [1 2 3]))"))))

    (testing "with fixed arities in front of the rest one"
      (is (= "[1 2 [3 4]]"
             (run "(def f (fn [a b & xs] [a b (vec xs)]))
                   (set! (.-cljs$core$IFn$_invoke$arity$variadic f) (fn [_ _ _] :replaced))
                   (pr-str (f 1 2 3 4))"))))

    (testing "but the property is still assigned, because a caller may use it"
      ;; this is what static arity dispatch emits (§5.33) and what instrument
      ;; overwrites - it has to be the body until someone replaces it
      (is (= "[[1 2] :replaced]"
             (run "(def f (fn [& xs] (vec xs)))
                   (let [through (.cljs$core$IFn$_invoke$arity$variadic f (seq [1 2]))]
                     (set! (.-cljs$core$IFn$_invoke$arity$variadic f) (fn [_] :replaced))
                     (pr-str [through (.cljs$core$IFn$_invoke$arity$variadic f nil)]))"))))))

(h/deftest-when h/node? test-a-variadic-body-still-sees-the-receiver
  ;; §5.36. §5.35 moved a variadic function's body out of its entry point and into
  ;; a delegate local. A body is not only expressions, though - it may read `this`,
  ;; and moving it into a second function silently changed what `this` was.
  ;;
  ;; cljs.core's deftype depends on exactly that. adapt-ifn-params (core.cljc:1653)
  ;; compiles an IFn method to (fn [self__ & args] (this-as self__ ...)) because
  ;; `call` is reached as obj.call(null, ...): the first parameter absorbs the null
  ;; and the object has to come from `this`. That works for a fixed-arity method,
  ;; whose body IS the property on the prototype, and did not for a variadic one.
  ;;
  ;; So the entry point forwards its receiver rather than dropping it. Measured at
  ;; 20M calls, .call(this, ...) on a monomorphic callee is not distinguishable
  ;; from a direct call.
  (let [run #(h/output-with-core (h/core-env) %)]
    (testing "this-as inside a variadic fn is the object the call was made on"
      (is (= "42"
             (run "(def o #js {:n 42})
                   (set! (.-f o) (fn [& _] (this-as t (.-n t))))
                   (pr-str (.f o))"))))

    (testing "a deftype whose only IFn method is variadic - CLJS-2133"
      ;; their own test calls this an INVALID implementation and asks that it work
      ;; anyway; we warn on it (protocol-impl-with-variadic-method) and run it
      (is (= "3"
             (run "(deftype P [f args]
                     IFn
                     (-invoke [_ & a] (apply (apply partial f args) a)))
                   (pr-str ((P. + [1]) 2))"))))

    (testing "with fixed arities ahead of the rest argument"
      (is (= "[42 1 [2 3]]"
             (run "(def o #js {:n 42})
                   (set! (.-f o) (fn [a & r] (this-as t [(.-n t) a (vec r)])))
                   (pr-str (.f o 1 2 3))"))))

    (testing "and through apply, which reaches the body by the same delegate"
      (is (= "[42 1 [2 3]]"
             (run "(def o #js {:n 42})
                   (set! (.-f o) (fn [a & r] (this-as t [(.-n t) a (vec r)])))
                   (pr-str (.apply (.-f o) o (into-array [1 2 3])))"))))))
