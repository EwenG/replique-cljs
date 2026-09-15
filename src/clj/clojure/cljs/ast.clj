;   Copyright (c) Nicola Mometto, Rich Hickey & contributors. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Walking and updating an analyzer AST.

  VENDORED from clojure.tools.analyzer.ast 1.2.0, which runs on our nodes
  unmodified - because clojure.cljs.analyzer was written to tools.analyzer's node
  spec and not merely to something like it:

      :op        a keyword naming the node
      :form      what it was read from
      :env       the analysis environment
      :children  a vector of KEYS, each holding a node or a VECTOR of nodes

  The op names are tools.analyzer's own - :const :def :do :fn :fn-method :if
  :invoke :let :letfn :local :loop :map :new :quote :recur :set :set! :the-var
  :throw :try :var :vector :with-meta :binding :case-test :case-then :host-call
  :host-field - with ours added where the target differs: :js :js-var :js-array
  :js-object :goog-ns :goog-var :deftype :ns :qualified-method.

  WHY VENDORED AND NOT DEPENDED ON. tools.analyzer has no dependencies of its own,
  so the usual objection does not apply; the one that does is ours. This jar's
  artifactId is deliberately `clojure` so it can be substituted for
  org.clojure/clojure, whose entire runtime dependency list is spec.alpha and
  core.specs.alpha. A third entry would make the substitution stop being one.
  Same licence, and the same reasoning that vendored cljs/core.cljc.

  WHAT :children BUYS, and it is the whole reason to have this file: a pass does
  not need to know the node types. `postwalk` visits every node of a 100,000-node
  compile without a defmethod per op, and a node type added to the analyzer
  tomorrow is walked correctly the moment it declares its children. That property
  is only as good as the declaration, so ast_test checks it against a real
  analysis rather than trusting it - see the invariant stated there.

  TWO PROPERTIES WORTH KNOWING, because they are what you would not write yourself:

    - Every function here SHORT-CIRCUITS ON reduced. A search that has found what
      it wants stops descending, and `walk` hands the AST back rather than the
      reduced.
    - `reversed?` walks a node's children last-to-first, which is what a BACKWARDS
      analysis needs - liveness, and the reachability half of a dead-code pass.

  CHANGED FROM UPSTREAM. clojure.tools.analyzer.utils is not vendored with it:
  into!, rseqv and mapv' are the three functions this file used from there and
  they are private here. Two public functions are dropped rather than carried:
  `ast->eav`, which projects the AST for Datomic's Datalog, and `cycling`, which
  repeats a set of passes to a fixpoint - a pass combinator rather than a walker,
  and it belongs with the pass scheduler we did not take either.

  One more line is gone. Upstream excludes clojure.core/unreduced and defines its
  own, which is the same three forms - an exclusion from when tools.analyzer still
  supported Clojure 1.6, where clojure.core/unreduced did not exist yet. It does
  here.

  Nothing else is changed, and nothing here knows anything about ClojureScript."}
  clojure.cljs.ast)

;; --- the three helpers upstream keeps in tools.analyzer.utils ---------------

(defn- into!
  "Like into, but for transients."
  [to from]
  (reduce conj! to from))

(defn- rseqv
  "Same as (comp vec rseq)."
  [v]
  (vec (rseq v)))

(defn- mapv'
  "Like mapv, but short-circuits on reduced."
  [f v]
  (let [c (count v)]
    (loop [ret (transient []) i 0]
      (if (> c i)
        (let [val (f (nth v i))]
          (if (reduced? val)
            (reduced (persistent! (reduce conj! (conj! ret @val) (subvec v (inc i)))))
            (recur (conj! ret val) (inc i))))
        (persistent! ret)))))

;; --- reading a node's children ----------------------------------------------

(defn children*
  "Return a vector of vectors of the children node key and the children expression
   of the AST node, if it has any.
   The returned vector returns the children in the order as they appear in the
   :children field of the AST, and the children expressions may be either a node
   or a vector of nodes."
  [{:keys [children] :as ast}]
  (when children
    (mapv #(find ast %) children)))

(defn children
  "Return a vector of the children expression of the AST node, if it has any.
   The children expressions are kept in order and flattened so that the returning
   vector contains only nodes and not vectors of nodes."
  [ast]
  (persistent!
   (reduce (fn [acc [_ c]] ((if (vector? c) into! conj!) acc c))
           (transient []) (children* ast))))

;; --- updating a node's children ---------------------------------------------

;; return transient or reduced holding transient
(defn- -update-children
  [ast f r?]
  (let [fix (if r? rseqv identity)]
    (reduce (fn [ast [k v]]
              (let [multi (vector? v)
                    val (if multi (mapv' f (fix v)) (f v))]
                (if (reduced? val)
                  (reduced (reduced (assoc! ast k (if multi (fix @val) @val))))
                  (assoc! ast k (if multi (fix val) val)))))
            (transient ast)
            (fix (children* ast)))))

(defn update-children-reduced
  "Like update-children but returns a reduced holding the AST if f short-circuited."
  ([ast f] (update-children-reduced ast f false))
  ([ast f reversed?]
     (if (and (not (reduced? ast))
              (:children ast))
       (let [ret (-update-children ast f reversed?)]
         (if (reduced? ret)
           (reduced (persistent! @ret))
           (persistent! ret)))
       ast)))

(defn update-children
  "Applies `f` to each AST children node, replacing it with the returned value.
   If reversed? is not-nil, `pre` and `post` will be applied starting from the last
   children of the AST node to the first one.
   Short-circuits on reduced."
  ([ast f] (update-children ast f false))
  ([ast f reversed?]
     (unreduced (update-children-reduced ast f reversed?))))

;; --- walking ----------------------------------------------------------------

(defn walk
  "Walk the ast applying `pre` when entering the nodes, and `post` when exiting.
   Both functions must return a valid node since the returned value will replace
   the node in the AST which was given as input to the function.
   If reversed? is not-nil, `pre` and `post` will be applied starting from the last
   children of the AST node to the first one.
   Short-circuits on reduced."
  ([ast pre post]
     (walk ast pre post false))
  ([ast pre post reversed?]
     (unreduced
      ((fn walk [ast pre post reversed?]
         (let [walk #(walk % pre post reversed?)]
           (if (reduced? ast)
             ast
             (let [ret (update-children-reduced (pre ast) walk reversed?)]
               (if (reduced? ret)
                 ret
                 (post ret))))))
       ast pre post reversed?))))

(defn prewalk
  "Shorthand for (walk ast f identity)"
  [ast f]
  (walk ast f identity))

(defn postwalk
  "Shorthand for (walk ast identity f reversed?)"
  ([ast f]
     (postwalk ast f false))
  ([ast f reversed?]
     (walk ast identity f reversed?)))

(defn nodes
  "Returns a lazy-seq of all the nodes in the given AST, in depth-first pre-order."
  [ast]
  (lazy-seq
   (cons ast (mapcat nodes (children ast)))))
