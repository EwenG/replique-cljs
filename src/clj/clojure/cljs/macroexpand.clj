;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Macroexpansion across the two worlds.

  A ClojureScript macro is an ordinary Clojure macro: a Var in a real JVM
  namespace, whose function runs at compile time and returns ClojureScript. So
  expansion asks two different worlds two different questions - which macro does
  this symbol name here (the macro-side view of the current ClojureScript
  namespace) and, once found, just call it (the JVM).

  Follows cljs.analyzer/macroexpand-1* (analyzer.cljc:4273) and get-expander*
  (:4203), which is the contract the M2 AST-diff oracle will be checked against.
  Two deliberate departures, both noted at their site below: no *ns* rebinding
  and no js* :js-op tagging.

  See doc/cljs-compiler.md M1."}
  clojure.cljs.macroexpand
  (:refer-clojure :exclude [macroexpand macroexpand-1])
  (:require [clojure.cljs.env :as env])
  (:import [clojure.lang Namespace NamespaceWorld Symbol Var]))

(def specials
  "cljs.analyzer/specials. A special form is never a macro call, whatever the
  symbol happens to name."
  '#{if def fn* do let* loop* letfn* throw try recur new set! ns deftype*
     defrecord* . js* & quote case* var ns*})

;; --- finding the macro -----------------------------------------------------

(defn- rewrite-ns
  [cenv sym]
  (get (:macro-ns-rewrites cenv) sym sym))

(defn- macro-namespace
  "The JVM namespace named by the namespace part of a qualified symbol, as seen
  from the current ClojureScript namespace. cljs.analyzer/get-expander-ns."
  ^Namespace [cenv nsym]
  (let [^Namespace view (env/macro-view cenv)
        ^Namespace cns  (.find ^NamespaceWorld (:world cenv) env/*current-ns*)]
    (or
     ;; (:require-macros [foo.macros :as m]) - the alias already names a JVM ns.
     ;;
     ;; REWRITTEN LIKE ANY OTHER NAME, which is the whole reason this branch takes
     ;; the alias apart again instead of returning it. get-expander-ns resolves an
     ;; alias to a NAME first and rewrites that, so (:require-macros [clojure.core
     ;; :as lang]) makes lang/for the cljs.core macro even though the alias itself
     ;; points at the JVM clojure.core - and cljs/ns_test.cljs writes exactly that
     ;; and expects (lang/for [x (range 5)] x) to be a seq. Without it clojure.core's
     ;; own `for` expands, and its expansion calls .nth on a cljs collection.
     ;;
     ;; A :REFER OFF THE SAME SPEC IS NOT REWRITTEN, which is not an oversight but
     ;; the same rule read the other way: only the namespace PART of a qualified
     ;; symbol goes through this, so :refer [when] off clojure.core refers the JVM
     ;; clojure.core/when, as it does in ClojureScript (get-expander* reaches
     ;; :rename-macros and :use-macros without consulting get-expander-ns).
     (some-> (.lookupAlias view nsym) .getName (->> (rewrite-ns cenv)) find-ns)
     ;; a runtime alias, whose target namespace may also carry macros of the same
     ;; name: (:require [foo :as f]) then (f/some-macro ...)
     (some-> cns (.lookupAlias nsym) .getName (->> (rewrite-ns cenv)) find-ns)
     ;; written out in full
     (find-ns (rewrite-ns cenv nsym)))))

(defn macro-var
  "The Var to expand `sym` with in `env`, or nil if it names no macro here.

  Locals hide macros, so this consults `env`, not only the worlds. So does
  (:refer-clojure :exclude [...]), which the ns form records and which suppresses
  the core fallback below for the names it lists - the only thing it can affect
  until cljs.core is vendored and core vars exist to be hidden as well."
  ^Var [cenv env sym]
  (when-not (contains? (:locals env) sym)
    (let [v (if-let [nsym (some-> (namespace sym) symbol)]
              (when-let [^Namespace mns (macro-namespace cenv nsym)]
                (.findInternedVar mns (symbol (name sym))))
              (or
               ;; (:refer-macros [...]) / :use-macros / :rename-macros
               (let [m (.getMapping (env/macro-view cenv) sym)]
                 (when (instance? Var m) m))
               ;; anything else unqualified falls through to the core macros,
               ;; unless this namespace excluded the name
               (when-not (env/excluded? cenv env/*current-ns* sym)
                 (when-let [^Namespace cns (some-> (:core-macros cenv) find-ns)]
                   (.findInternedVar cns sym)))))]
      (when (and v (.isMacro ^Var v))
        v))))

;; --- expanding -------------------------------------------------------------

(defn- host-sugar
  "(.foo x a) => (. x foo a), (Foo. a) => (new Foo a). Not macroexpansion, but
  cljs.analyzer does it here and the shapes have to match for the M2 oracle."
  [form op]
  (let [s (str op)]
    (cond
      (.startsWith s ".")
      (let [[target & args] (next form)]
        (with-meta (list* '. target (symbol (subs s 1)) args) (meta form)))

      (and (.endsWith s ".") (> (count s) 1))
      (with-meta (list* 'new (symbol (subs s 0 (dec (count s)))) (next form))
        (meta form))

      :else form)))

(defn macroexpand-1
  "Expand `form` once in `env`. Returns the form unchanged when there is nothing
  to expand - identical?, so callers can test for a fixed point.

  The macro is invoked exactly as Clojure invokes one: (apply @v form env args),
  so it receives &form and &env.

  Two departures from cljs.analyzer here. It binds *ns* to (create-ns *cljs-ns*)
  around the call, minting a JVM namespace named after a ClojureScript one - which
  is the collision NamespaceWorld exists to avoid, and which only matters to a
  macro that reaches for *ns* itself (cljs/core.cljc does so once). And it tags a
  js* expansion with :js-op / ::numeric metadata for the emitter's operator
  inference, which has nothing to consume it yet."
  [cenv env form]
  (if-not (seq? form)
    form
    (let [op (first form)]
      (cond
        (contains? specials op) form

        (symbol? op)
        (if-let [v (macro-var cenv env op)]
          ;; the one place *cenv* is bound. A macro's parameters are &form and
          ;; &env, so a macro that has to resolve a ClojureScript symbol -
          ;; defprotocol and its family, which turn one into a property name -
          ;; has no way to be handed the compile environment explicitly.
          (binding [env/*cenv* cenv]
            (apply @v form env (rest form)))
          (host-sugar form op))

        :else form))))

(defn macroexpand
  "Expand `form` until it stops changing at the top level, as clojure.core's
  macroexpand does. `limit` guards a macro that expands to itself."
  ([cenv env form] (macroexpand cenv env form 100))
  ([cenv env form limit]
   (loop [form form n 0]
     (when (> n limit)
       (throw (ex-info (str "macroexpand did not reach a fixed point after " limit
                            " expansions")
                       {:form form})))
     (let [form' (macroexpand-1 cenv env form)]
       (if (identical? form form')
         form
         (recur form' (inc n)))))))
