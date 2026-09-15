;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns cljs.spec.gen.alpha
  (:refer-clojure :exclude [delay])
  ;; ADAPTED (M6): clojure.cljs.names is this compiler's munger, and dynaload
  ;; below needs it to spell a property name.
  (:require [cljs.core :as c]
            [clojure.cljs.names :as comp]
            [clojure.string :as string]))

;; ADAPTED (M6). One line: the reference to the var this just found.
;;
;; Theirs writes the SYMBOL, tagged ::no-resolve so the analyzer will not object
;; to a var it cannot see, and gets the global path
;; clojure.test.check.generators.simple_type_printable - which works there because
;; a var IS that path. Here a var is a property of a namespace object
;; (doc/cljs-compiler.md 5.2) and the tag cannot help: the namespace is not
;; required, deliberately - the whole point of dynaload is to reach one that may
;; or may not have been loaded by somebody else - so there is no import and no
;; alias for it, and analysis refuses the name rather than inventing one.
;;
;; $ns(name)[prop] is the same reach the adapted exists? just made, and the two
;; have to agree: this line runs only when that one answered true.
(defmacro dynaload [[quote s]]
  `(cljs.spec.gen.alpha/LazyVar.
     (fn []
       (if (c/exists? ~s)
         ~(clojure.core/list 'js* "$ns(~{})[~{}]"
                             (namespace s) (comp/munge (name s)))
         (throw
           (js/Error.
             (str "Var " '~s " does not exist, "
                  (namespace '~s) " never required")))))
     nil))

(defmacro delay
  "given body that returns a generator, returns a
  generator that delegates to that, but delays
  creation until used."
  [& body]
  `(delay-impl (c/delay ~@body)))

(defmacro ^:skip-wiki lazy-combinator
  "Implementation macro, do not call directly."
  [s]
  (let [fqn (symbol "clojure.test.check.generators" (name s))
        doc (str "Lazy loaded version of " fqn)]
    `(let [g# (dynaload '~fqn)]
       (defn ~s
         ~doc
         [& ~'args]
         (apply @g# ~'args)))))

(defmacro ^:skip-wiki lazy-combinators
  "Implementation macro, do not call directly."
  [& syms]
  `(do
     ~@(map
         (fn [s] (list `lazy-combinator s))
         syms)))

(defmacro ^:skip-wiki lazy-prim
  "Implementation macro, do not call directly."
  [s]
  (let [fqn (symbol "clojure.test.check.generators" (name s))
        doc (str "Fn returning " fqn)]
    `(let [g# (dynaload '~fqn)]
       (defn ~s
         ~doc
         [& ~'args]
         @g#))))

(defmacro ^:skip-wiki lazy-prims
  "Implementation macro, do not call directly."
  [& syms]
  `(do
     ~@(map
         (fn [s] (list `lazy-prim s))
         syms)))