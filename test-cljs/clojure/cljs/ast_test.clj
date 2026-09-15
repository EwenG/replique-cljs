;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The AST walk, and the invariant it rests on.

  clojure.cljs.ast is vendored from tools.analyzer and knows nothing about
  ClojureScript: it finds a node's children by reading :children, a vector of keys.
  So a pass written against it is correct for every node type, including ones added
  after the pass was written - and that whole property is one declaration away from
  being false. A node that holds a child under a key it does not name in :children
  is invisible to every walk, silently, and the failure looks like a pass that
  forgot a case rather than like a node that lied.

  THE INVARIANT, stated once and checked against a real analysis:

    every map with an :op reachable from an AST node - excluding :env, whose
    :locals legitimately hold binding nodes that are not children - is also
    reachable by following :children from the root.

  Checking it needs a program that reaches every node type there is, which is what
  `corpus` is for, and `test-the-corpus-reaches-every-op` is what keeps `corpus`
  honest: add an :op to the analyzer and that test fails until the corpus produces
  one, so the invariant is never quietly checked over 38 of 39 node types.

  The same invariant was measured once at a scale no test should pay for: 101,120
  nodes over a full cljs.core compile, 36 distinct ops, nothing hidden. That is
  doc/cljs-compiler.md §5.39; this file is the part of it that runs every time.

  Needs the ClojureScript jar for nothing, and node for nothing - the AST never
  reaches a runtime."}
  clojure.cljs.ast-test
  (:require [clojure.cljs.ast :as ast]
            [clojure.cljs.env :as env]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.test-harness :as h]
            [clojure.test :refer [deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

;; --- the corpus -------------------------------------------------------------

(def ^:private corpus
  "One program that reaches every :op clojure.cljs.analyzer can produce.

  Read with our reader rather than the JVM's, because #js is ours; analysed form by
  form in one environment, because the ns form has to move the cursor before the
  requires below it resolve.

  Written to be dense rather than realistic. Each line is here for the node it
  makes, and the ones that are not obvious:

    ^{:m 1} [1 2]     :with-meta. (with-meta [1] ...) would be an :invoke - the
                      node comes from metadata the reader attached, not from a call
    (var f)           :the-var, as distinct from :var
    goog.math.Long    :goog-ns - a Closure provide is a value as well as a module
    String/.toUpperCase  :qualified-method, which is why the ns form says
                      :refer-global - a bare host name has to be declared here"
  "(ns corpus.ast-test
     (:require [goog.string :as gstring]
               [goog.math.Long :as Long])
     (:refer-global :only [String]))

   (def ^:dynamic *d* 1)

   (defn f
     ([x] x)
     ([x & r] (let [y (+ x 1)]
                (loop [i 0]
                  (if (< i y) (recur (inc i)) i)))))

   (defn g [x] (case x 1 :a 2 :b :other))

   (defn h [x]
     (try (throw (js/Error. \"boom\"))
          (catch :default e (.-message e))
          (finally (.log js/console x))))

   (letfn [(p [x] (q x)) (q [x] (p x))] (p 1))

   (deftype T [a b] Object (toString [_] (str a b)))
   (defrecord R [a])

   (set! *d* 2)

   (def coll [1 {:a #{:b}} (quote (x y)) (var f) ^{:m 1} [1 2]])
   (def jsl #js {:a 1 :b #js [2 3]})
   (def raw (js* \"~{} + 1\" 2))

   (gstring/isEmptyOrWhitespace \"\")
   (instance? Long 1)
   (String/.toUpperCase \"a\")")

(def ^:private every-op
  "Every :op clojure.cljs.analyzer emits.

  Kept by hand, and kept honest by test-the-corpus-reaches-every-op below: this set
  is what the corpus is measured against, so it is the thing that has to be updated
  when a node type is added. :no-op is deliberately absent - cljs.analyzer returns
  one for a compiler-flag set! and we analyse the value instead (§5.37)."
  '#{:binding :case :case-node :case-test :case-then :const :def :deftype :do
     :fn :fn-method :goog-ns :goog-var :host-call :host-field :if :invoke :js
     :js-array :js-object :js-var :let :letfn :local :loop :map :new :ns
     :qualified-method :quote :recur :set :set! :the-var :throw :try :var
     :vector :with-meta})

(defn- corpus-asts
  "The corpus, analysed, as one node per top-level form."
  []
  (let [cenv (h/core-env)]
    (mapv #(h/analyze cenv %) (reader/read-forms cenv corpus))))

(defn- op-maps
  "Every map with an :op anywhere under `x`, found WITHOUT consulting :children -
  which is the point: this is the other half of the comparison.

  :env is not descended into. Its :locals hold binding nodes by design, and they
  are not children of the node whose environment they are."
  [x]
  (let [acc (transient [])]
    ((fn go [x]
       (cond
         (map? x)  (do (when (:op x) (conj! acc x))
                       (run! go (vals (dissoc x :env))))
         (coll? x) (run! go x)))
     x)
    (persistent! acc)))

;; --- the invariant ----------------------------------------------------------

(deftest test-every-node-is-reachable-by-following-children
  (let [asts (corpus-asts)
        hidden (for [ast asts
                     :let [reachable (java.util.IdentityHashMap.)]
                     :let [_ (run! #(.put reachable % true) (ast/nodes ast))]
                     node (op-maps ast)
                     :when (not (.containsKey reachable node))]
                 [(:op ast) (:op node) (:form node)])]
    (is (empty? hidden)
        (str "nodes held under a key their parent does not name in :children: "
             (pr-str (vec (take 5 hidden)))))))

(deftest test-every-declared-child-holds-a-node
  ;; The other direction. A :children key naming something absent, or holding a
  ;; form rather than a node, breaks a walk just as thoroughly - and breaks it
  ;; with a NullPointerException somewhere else, which is worse to read.
  (let [bad (for [ast (corpus-asts)
                  node (ast/nodes ast)
                  k    (:children node)
                  :let [v (get node k ::absent)]
                  :when (not (or (and (map? v) (:op v))
                                 (and (vector? v) (every? #(and (map? %) (:op %)) v))))]
              [(:op node) k (if (= v ::absent) ::absent (type v))])]
    (is (empty? bad) (pr-str (vec (take 5 bad))))))

(deftest test-the-corpus-reaches-every-op
  ;; What keeps the two tests above from being checked over almost every node type.
  (let [seen (into #{} (mapcat #(map :op (ast/nodes %))) (corpus-asts))]
    (testing "no op goes unexercised"
      (is (empty? (remove seen every-op))
          (str "not produced by the corpus: " (pr-str (sort (remove seen every-op))))))
    (testing "and every-op is the whole list"
      (is (empty? (remove every-op seen))
          (str "produced but not declared in every-op: "
               (pr-str (sort (remove every-op seen))))))))

(deftest test-a-walk-that-changes-nothing-changes-nothing
  ;; Rebuilding every node through transients has to be an identity, or a pass that
  ;; only looks at one node type still rewrites the AST around it.
  (doseq [ast (corpus-asts)]
    (is (= ast (ast/postwalk ast identity)))
    (is (= ast (ast/prewalk ast identity)))
    (is (= ast (ast/postwalk ast identity true)))))

;; --- the walk itself --------------------------------------------------------

(defn- one-ast []
  (let [cenv (h/core-env)]
    (h/analyze cenv '(let [a 1] (if a (+ a 2) 3)))))

(deftest test-nodes-is-depth-first-pre-order
  (let [ops (mapv :op (ast/nodes (one-ast)))]
    (is (= :let (first ops)))
    ;; the binding and its init come before the body, as they do in :children
    (is (< (.indexOf ops :binding) (.indexOf ops :if)))
    (is (= (count ops) (count (ast/nodes (one-ast)))))))

(deftest test-children-flattens-vector-slots
  (let [ast (one-ast)]
    ;; :let is [:bindings :body] - one vector slot and one node slot
    (is (= [:bindings :body] (mapv first (ast/children* ast))))
    (is (every? :op (ast/children ast)))
    ;; the body of a let is a :do, always - one statement is the one-element case
    (is (= [:binding :do] (mapv :op (ast/children ast))))))

(deftest test-a-walk-short-circuits-on-reduced
  ;; What a search uses: stop descending once the answer is in hand. The walk hands
  ;; back the AST, not the reduced - so a caller that wants the value carries it out
  ;; some other way, which is why this is a property of the WALK and not a find.
  (let [ast     (one-ast)
        visited (atom 0)
        found   (atom nil)
        ret     (ast/prewalk ast (fn [n]
                                   (swap! visited inc)
                                   (if (= :const (:op n))
                                     (do (reset! found (:form n)) (reduced n))
                                     n)))]
    (is (= 1 @found) "stopped at the first constant, which is the binding's init")
    (is (map? ret))
    (is (not (reduced? ret)))
    (is (< @visited (count (ast/nodes ast)))
        "short-circuiting has to visit fewer nodes than walking all of them")))

(deftest test-reversed-walks-children-last-to-first
  ;; What a backwards analysis needs - liveness, and the reachability half of a
  ;; dead-code pass. The order is observable and the result is not, so the test
  ;; records the order and then checks the AST came back unchanged.
  (let [ast   (one-ast)
        order (atom [])
        seen  #(do (swap! order conj (:op %)) %)
        fwd   (do (reset! order []) (ast/prewalk ast seen) @order)
        rev   (do (reset! order []) (ast/walk ast seen identity true) @order)]
    (is (= (set fwd) (set rev)) "the same nodes, either way")
    (is (not= fwd rev) "in a different order")
    (is (= :do (second rev)) "the body before the bindings")
    (is (= :binding (second fwd)) "and the bindings before the body")
    (is (= ast (ast/walk ast identity identity true)))))

(deftest test-update-children-replaces-in-both-slot-shapes
  ;; One node slot and one vector slot, updated in one call, and nothing else moved.
  (let [ast (one-ast)
        marked (ast/update-children ast #(assoc % ::seen true))]
    (is (every? ::seen (ast/children marked)))
    (is (= (:op ast) (:op marked)))
    (is (= 1 (count (:bindings marked))))
    (testing "and not recursively - update-children is one level"
      (is (not-any? ::seen (mapcat ast/children (ast/children marked)))))))
