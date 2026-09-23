;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The AST oracle: every form we analyse must project exactly as
  cljs.analyzer projects it (clojure.cljs.oracle).

  Skipped when ClojureScript is not on the classpath. Run with `mvn -o test`."}
  clojure.cljs.oracle-test
  ;; clojure.cljs.oracle loads without ClojureScript present - it reaches for
  ;; cljs.analyzer through resolve, at call time - so it can be required here
  ;; unconditionally. Only the calls are gated.
  (:require [clojure.cljs.oracle :as o]
            [clojure.cljs.test-harness :as h]
            [clojure.test :refer [are is use-fixtures]])
  (:import [cljs.tagged_literals JSValue]))

(use-fixtures :each h/cursor)

(defmacro agree
  "Each form projects the same both ways. `setup` declares the vars the forms
  refer to, in both worlds."
  [setup & forms]
  `(are [form#] (true? (o/agree? ~setup form#))
     ~@forms))

(h/deftest-when h/cljs-analyzer? test-core-forms
  (agree []
    '(if 0 1 2)
    '(do 1 2 3)
    '(let* [x 1] (if x 1 2))
    '(let* [x 1 y 2] (js* "~{} + ~{}" x y))
    '(js* "~{} + ~{}" 1 2)))

(h/deftest-when h/cljs-analyzer? test-fn
  (agree []
    '(fn* ([x] x))
    '(fn* ([x] x) ([x y] y))
    '(fn* ([x & r] r))
    '(fn* self ([x] (self x)))
    '((fn* ([x] x)) 1)
    '(let* [f (fn* ([x] x))] (f 1))
    '(fn* ([n] (if (js* "~{} < 3" n) (recur (js* "~{} + 1" n)) n)))))

(h/deftest-when h/cljs-analyzer? test-def
  (agree []
    '(def x 1)
    '(def x)
    '(def x "doc" 1)
    ;; the divergence the oracle caught: ClojureScript gives a def'd anonymous fn
    ;; a self-name, emission-only and $-prefixed
    '(def f (fn* ([a] a)))))

(h/deftest-when h/cljs-analyzer? test-loop-recur
  (agree []
    '(loop* [i 0] (if (js* "~{} < 3" i) (recur (js* "~{} + 1" i)) i))
    '(loop* [a 1 b 2] (recur b a))))

(h/deftest-when h/cljs-analyzer? test-dot
  (agree '[(def o nil)]
    '(. o -x)
    '(. "abc" -length)
    '(. o m)
    '(. o m 1 2)
    '(. o (m 1 2))
    '(. (. o -a) -b)
    '(.toUpperCase "abc")
    '(.-length "abc")
    '(.indexOf "abc" "b")
    '(.log js/console "hi")))

(h/deftest-when h/cljs-analyzer? test-new-and-js-globals
  (agree []
    '(new js/Date)
    '(new js/Date 2026 1 1)
    '(js/Date. 1)
    'js/console
    'js/console.log
    '(js/console.log "hi")
    ;; a local of the same name wins over the js/ prefix, in both
    '(fn* ([x] js/x))
    '(let* [d (new js/Date)] (.getTime d))))

(h/deftest-when h/cljs-analyzer? test-throw
  (agree '[(def o nil)]
    '(throw (new js/Error "boom"))
    '(throw o)
    '(if o 1 (throw o))
    '(fn* ([x] (throw x)))
    '(let* [e o] (throw e))))

(h/deftest-when h/cljs-analyzer? test-set!
  (agree '[(def o nil) (def x 1)]
    '(set! x 1)
    '(set! (.-foo o) 1)
    '(set! o -foo 1)
    '(set! (.-a (.-b o)) 2)
    '(set! js/globalThis.z 1)))

(h/deftest-when h/cljs-analyzer? test-quote
  (agree []
    '(quote foo)
    '(quote :k)
    '(quote 42)
    '(quote "s")
    '(quote nil)
    ;; a quoted collection is one :const carrying the whole structure in both
    ;; analyzers - nothing inside it evaluates, so there is nothing to walk
    '(quote [1 2])
    '(quote (1 2))
    '(quote {:a 1})
    '(quote #{1})))

(h/deftest-when h/cljs-analyzer? test-collection-literals
  ;; the other half: elements are EXPRESSIONS, so each literal is a node with
  ;; children, and the two analyzers build the same shape from the same form
  (agree '[(def a nil)]
    '[] '[1 2] '[a (if a 1 2)]
    '{} '{:a 1} '{a 1 :b a}
    '#{} '#{1 2} '#{a}
    ;; the empty list is a value rather than a call, and both say so
    ()
    ;; and the two literals that need no cljs.core at all
    \x
    #"ab"))

(h/deftest-when h/cljs-analyzer? test-a-js-literal
  ;; The literal this file could not ask about until 5.68, and the reason was not
  ;; about either analyzer: the marker the reader wrapped it in was a defrecord of
  ;; this compiler's own, so cljs.analyzer met an unknown RECORD - analyze-record,
  ;; two lines above its JSValue test - and built something else entirely. The two
  ;; now share ClojureScript's class, so the question can be put.
  ;;
  ;; Constructed rather than read, because `agree' takes a form and #js is a data
  ;; reader: what the reader hands back IS one of these.
  (is (true? (o/agree? [] (JSValue. {:a 1 "b" 2}))))
  (is (true? (o/agree? [] (JSValue. [1 2]))))
  ;; and the values are code in both, while the keys are not
  (is (true? (o/agree? '[(def a nil)] (JSValue. {:a 'a}))))
  (is (true? (o/agree? '[(def a nil)] (JSValue. ['a (list 'if 'a 1 2)])))))

(h/deftest-when h/cljs-analyzer? test-mixed
  (agree '[(def o nil) (def x 1)]
    '(if (.-x o) (.y o) (new js/Error "no"))
    '(do (set! x (quote sym)) (throw (new js/Error "x")))))

(h/deftest-when h/cljs-analyzer? test-letfn-and-case
  (agree []
    '(letfn* [f (fn* ([] (g))) g (fn* ([] 1))] (f))
    '(letfn* [f (fn* ([x] x))] (f 1))
    '(let* [x 1] (case* x [[1] [2 3]] ["a" "b"] "c"))
    '(let* [x 1] (case* x [[1]] [(js* "~{} + 1" x)] 0))
    '(loop* [i 0] (case* i [[0]] [(recur 1)] i))))

(h/deftest-when h/cljs-analyzer? test-known-divergences
  ;; The one place the analyzers deliberately part company inside M2's subset.
  ;; Asserted rather than described, so a change to it shows up here.
  ;;
  ;; There used to be a second, and it is worth recording that it closed rather
  ;; than deleting it: a quoted collection was refused here where ClojureScript
  ;; analysed it, because building one calls into cljs.core. It is in test-quote
  ;; above now (doc/cljs-compiler.md §5.7).
  ;;
  ;; There used to be a second one recorded here too, and it also closed: #js
  ;; could not be asked about while the marker was a record of this compiler's
  ;; own. It is ClojureScript's own class now, and test-a-js-literal above asks
  ;; (doc/cljs-compiler.md 5.68).

  ;; letfn* self-reference. cljs.analyzer binds a name to its OUTER meaning
  ;;    while analysing that name's own init, so a self-call resolves to a var and
  ;;    emits a namespace reference - (letfn [(f [] (f))] ...) does not recur
  ;;    there. Clojure's letfn is self-recursive and ours is too, so the inner f is
  ;;    a :local for us and a :var for them.
  (let [diff (o/agree? [] '(letfn* [f (fn* ([] (f)))] (f)))
        init-op (fn [ast] (-> ast :bindings first :init :methods first
                              :body :ret :fn :op))]
    (is (map? diff) "if this passes, ClojureScript has fixed it and we can agree")
    (is (= :var   (init-op (:cljs-analyzer diff))))
    (is (= :local (init-op (:ours diff)))))

  ;; A HOST GLOBAL. Math/floor emits Math.floor in both, and the two say so with
  ;; different nodes: cljs.analyzer answers a :var whose :ns is Math, we answer a
  ;; :js-var. Not a disagreement about the program - a ClojureScript var IS a
  ;; global path, so :var/Math there already reads as `the global Math, property
  ;; floor`, while a var of ours is a property of a namespace object reached
  ;; through $ns and Math has none (doc/cljs-compiler.md §5.2, §5.8).
  (let [diff (o/agree? [] 'Math/floor)]
    (is (map? diff))
    (is (= :var    (:op (:cljs-analyzer diff))))
    (is (= :js-var (:op (:ours diff))))))
