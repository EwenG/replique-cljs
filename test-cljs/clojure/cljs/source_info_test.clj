;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Positions on every node, and the two things that make that hard.

  ONE: macroexpansion. What the reader read has a position; what a macro built has
  none, and most of a ClojureScript AST is the second kind. The pass answers that
  by pushing a position DOWN from the nearest enclosing form that had one, so the
  test that matters is not that some node has a line but that the nodes with no
  form of their own - (fn* ...), (let* ...), (js* ...) - have the line of the form
  the user actually wrote.

  TWO: the root. A top-level (defn f ...) arrives at the analyzer already expanded
  to (def f (cljs.core/fn ...)), which carries no metadata - so the position of the
  form the user typed survives only on the form the CALLER still holds. That is
  what `seed` is for, and the last test here is the one that says so by showing
  what happens without it.

  Needs neither node nor the ClojureScript jar: a position is decided entirely on
  this side."}
  clojure.cljs.source-info-test
  (:require [clojure.cljs.ast :as ast]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.source-info :as si]
            [clojure.cljs.test-harness :as h]
            [clojure.test :refer [deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

(def ^:private src
  "Positions are the point, so the layout is: `defn` on line 1, the let binding on
  line 2, the body on line 3, and a second top-level form on line 5."
  (str "(defn f [x]\n"                      ;; 1
       "  (let [y (+ x 1)]\n"               ;; 2
       "    (str y)))\n"                    ;; 3
       "\n"                                 ;; 4
       "(def answer (if (f 1) :yes :no))")) ;; 5

(defn- analysed
  "Every top-level form of `src`, analysed and given positions, seeded from the form
  the reader produced - which is what a driver has and a node does not."
  []
  (let [cenv (h/core-env)]
    (mapv (fn [form]
            (si/source-info (h/analyze cenv form)
                            (merge {:file "app/core.cljs"} (meta form))))
          (reader/read-forms cenv src))))

(defn- env-of [node] (select-keys (:env node) [:line :column :end-line :end-column :file]))

(defn- find-op
  "The first node with this :op, in depth-first order."
  [node op]
  (first (filter #(= op (:op %)) (ast/nodes node))))

;; --- every node, and a well-formed region ------------------------------------

(deftest test-every-node-knows-where-it-came-from
  (doseq [node (analysed)]
    (let [ns* (ast/nodes node)]
      (is (every? #(:line (:env %)) ns*)
          (str "nodes with no line: "
               (pr-str (mapv :op (remove #(:line (:env %)) ns*)))))
      (is (every? #(= "app/core.cljs" (:file (:env %))) ns*)))))

(deftest test-a-position-is-a-region-somebody-wrote
  ;; What "all four keys move together" buys. A :line taken from one form and an
  ;; :end-line inherited from its parent would usually still look plausible - and
  ;; would sometimes describe a region that ends before it starts.
  (doseq [node (analysed)
          n    (ast/nodes node)
          :let [{:keys [line column end-line end-column]} (:env n)]
          :when end-line]
    (is (or (> end-line line)
            (and (= end-line line) (>= end-column column)))
        (pr-str [(:op n) (:form n) (:env n)]))))

;; --- the rule ---------------------------------------------------------------

(deftest test-a-form-macroexpansion-invented-takes-its-parents-position
  (let [defn-node (first (analysed))
        let-node  (find-op defn-node :let)]
    (testing "the node's own form has no metadata at all"
      (is (= 'let* (first (:form let-node))))
      (is (nil? (:line (meta (:form let-node))))))
    (testing "and it is placed where the (defn ...) that expanded to it was written"
      (is (= 1 (:line (:env let-node)))))))

(deftest test-a-form-the-reader-read-keeps-its-own-position
  (let [defn-node (first (analysed))
        ;; the let's binding is `y`, a symbol on line 2 - the reader gave it a
        ;; position and it must not inherit line 1 from the defn above it
        y (->> (ast/nodes defn-node)
               (filter #(and (= :binding (:op %)) (= 'y (:form %))))
               first)]
    (is (some? y))
    (is (= 2 (:line (:env y))))
    (is (= 9 (:column (:env y))))))

(deftest test-a-second-top-level-form-is-not-placed-at-the-first
  (let [[_ answer] (analysed)]
    (is (= :def (:op answer)))
    (is (= 5 (:line (:env answer))))
    (testing "and its expansion-built children come with it"
      (is (every? #(= 5 (:line (:env %)))
                  (filter #(= :if (:op %)) (ast/nodes answer)))))))

;; --- what the pass does not touch -------------------------------------------

(defn- without-envs [node] (ast/prewalk node #(dissoc % :env)))

(deftest test-nothing-but-env-changes
  (let [cenv (h/core-env)
        form (first (reader/read-forms cenv src))
        node (h/analyze cenv form)]
    (is (= (without-envs node)
           (without-envs (si/source-info node (merge {:file "x.cljs"} (meta form))))))
    (testing "and the node count is the same, so nothing was dropped or duplicated"
      (is (= (count (ast/nodes node))
             (count (ast/nodes (si/source-info node {:file "x.cljs"}))))))))

(deftest test-running-it-twice-changes-nothing
  (doseq [node (analysed)]
    (is (= node (si/source-info node {:file "app/core.cljs"})))))

;; --- the seed ---------------------------------------------------------------

(deftest test-without-a-seed-a-macroexpanded-root-has-nowhere-to-inherit-from
  ;; The documented reason the second argument exists, stated as a contrast rather
  ;; than as a paragraph: analysing (defn f ...) gives a :def node whose form is the
  ;; expansion, so the pass alone cannot place it or anything on the spine below it.
  (let [cenv (h/core-env)
        form (first (reader/read-forms cenv src))
        node (h/analyze cenv form)
        seedless (si/source-info node)
        seeded   (si/source-info node (meta form))]
    (testing "the form the user wrote did have a position"
      (is (= 1 (:line (meta form)))))
    (testing "the node built from it does not"
      (is (nil? (:line (meta (:form node))))))
    (testing "so without a seed the root is unplaced"
      (is (nil? (:line (:env seedless)))))
    (testing "and with one it is, along with everything that inherits from it"
      (is (= 1 (:line (:env seeded))))
      (is (= 1 (:line (:env (find-op seeded :let))))))
    (testing "what the reader did read is placed either way"
      (is (= (env-of (find-op seedless :local))
             (env-of (find-op seeded :local)))))))
