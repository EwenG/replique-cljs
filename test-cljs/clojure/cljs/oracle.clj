;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "cljs.analyzer as an AST oracle.

  Loaded only when ClojureScript is on the classpath - see
  clojure.cljs.test-harness/cljs-analyzer?, which every caller checks first.

  What is compared is a PROJECTION of the node, not the node: its :op plus the
  keys named in its own :children. That is the part the two analyzers must agree
  on. Everything tag inference produces - :tag, :inferred-ret-tag, :numeric,
  :jsdoc - is outside the projection by design (doc/cljs-compiler.md §7), and
  including it would make every diff noise."}
  clojure.cljs.oracle
  (:require [clojure.cljs.test-harness :as h]))

(defn skeleton
  "The comparable projection of an AST node, ours or ClojureScript's."
  [node]
  (when (map? node)
    (into {:op (:op node)}
          (for [k (:children node)
                :let [v (get node k)]]
            [k (if (vector? v) (mapv skeleton v) (skeleton v))]))))

(defn cljs-analyzer
  "A function analysing a form with cljs.analyzer and projecting the result.

  Each call gets its own compiler environment, so forms analysed together see each
  other's defs and forms analysed apart do not. A plain atom, not
  cljs.env/default-compiler-env, which would drag in cljs.closure and the whole
  Closure compiler. :analyze-deps and :load-macros are off: there is nothing on
  disk to load, and a require would try."
  []
  (let [analyze   (resolve 'cljs.analyzer/analyze)
        empty-env (resolve 'cljs.analyzer/empty-env)
        compiler  (resolve 'cljs.env/*compiler*)
        warnings  (resolve 'cljs.analyzer/*cljs-warnings*)
        cenv      (atom {:options {}})]
    (fn [form]
      ;; the vars are bound directly rather than through with-compiler-env, which
      ;; is a macro and so cannot be reached by resolve
      (with-bindings {compiler cenv
                      (resolve 'cljs.analyzer/*cljs-ns*) 'cljs.user
                      (resolve 'cljs.analyzer/*analyze-deps*) false
                      (resolve 'cljs.analyzer/*load-macros*) false
                      ;; the oracle's warnings are not our test output
                      warnings (zipmap (keys @warnings) (repeat false))}
        (skeleton (analyze (empty-env) form))))))

(defn agree?
  "Do both analyzers project `form` the same way?

  `setup` forms are analysed first in both worlds, so a test can declare the vars
  it refers to - otherwise ClojureScript warns and synthesises a :var where we
  refuse the symbol outright, and the diff would be about that rather than about
  the form under test."
  [setup form]
  (let [theirs (cljs-analyzer)
        cenv   (h/fresh-env 'cljs.user)]
    (doseq [f setup]
      (theirs f)
      (h/analyze cenv f))
    (let [t (theirs form)
          o (skeleton (h/analyze cenv form))]
      (if (= t o)
        true
        {:form form :cljs-analyzer t :ours o}))))
