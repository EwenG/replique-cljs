;; Copyright (c) Rich Hickey. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file epl-v10.html at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns cljs.reader
  (:require [clojure.cljs.reader :as reader]))

(defmacro add-data-readers
  "ADAPTED (M6). The tags a USER registered, merged into the runtime reader's
  table: every entry of every data_readers.cljc on the classpath, as a tag symbol
  and a ClojureScript function that calls the reader the file named.

  Theirs reads the same map out of the compiler environment:

      (get @env/*compiler* :cljs.analyzer/data-readers)

  which cljs.closure/load-data-readers! puts there. Here the scan IS the registry
  - clojure.cljs.reader/user-data-readers, memoized on the classpath - so there is
  no compiler-environment key to read and cljs.env is dropped from the ns form
  rather than repointed, the same adaptation cljs/test.cljc got.

  THE CALL IS EMITTED, NOT THE FUNCTION. data_readers.cljc names a var by symbol,
  and that symbol is resolved twice against two different worlds: once here on the
  JVM, so a tag can be read while compiling, and once in the expansion below, so
  the same name means the ClojureScript var of the same name at runtime. The two
  are unrelated definitions that agree by convention, which is exactly what a tag
  registry is. Wrapping in (fn [x#] (f x#)) rather than passing f is theirs, and
  is what makes the name resolve where the expansion lands rather than here.

  ClojureScript tags the emitted symbol :cljs.analyzer/no-resolve, which turns off
  their undeclared-var warning; this compiler needs no such mark, because it
  requires the namespace a qualified name mentions (doc/cljs-compiler.md 5.28) and
  so the name is declared by the time it is emitted.

  The tags of the LANGUAGE are not here and belong to the caller's map: #js and
  #queue are compile-time tags - one hands back a marker type and the other an
  ordinary form - and cljs.reader defines its own runtime readers for them."
  [default-readers]
  (let [readers (into {}
                      (map (fn [[tag f]]
                             (let [sym (:sym (meta f))]
                               [`'~tag `(fn [x#] (~sym x#))])))
                      (reader/user-data-readers))]
    `(merge ~default-readers ~readers)))
