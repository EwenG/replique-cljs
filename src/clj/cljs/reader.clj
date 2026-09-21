;; Copyright (c) Rich Hickey. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file epl-v10.html at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns cljs.reader
  (:require [clojure.cljs.reader :as reader]
            [clojure.cljs.env :as env])
  (:import [clojure.lang Namespace]))

(defn- unusable
  "Why the ClojureScript var `sym` names cannot be called at run time, as a phrase
  to put after the symbol - or nil when it can be.

  A TAG HAS UP TO TWO READERS AND data_readers.cljc NAMES ONE SYMBOL. The reader
  that runs while COMPILING is a JVM function, found with find-var and called on
  the JVM (clojure.cljs.reader/user-data-readers). The reader that runs at RUN TIME
  is a ClojureScript var of the same name, in a namespace of the same name, in the
  other world entirely. Nothing makes those two exist together; they are unrelated
  definitions that agree by convention, which is what a tag registry is.

  So the convention is often not held, and the idiom that breaks it is the common
  one. flatland/ordered registers

      ordered/map #?(:clj  flatland.ordered.map/ordered-map-reader-clj
                     :cljs flatland.ordered.map/ordered-map-reader-cljs)

  and BOTH of those live in flatland/ordered/map.clj, because the :cljs one is a
  JVM function that returns a ClojureScript FORM:

      (defn ordered-map-reader-cljs [coll] `(ordered-map ~(vec coll)))

  That is correct, and it is exactly the reader this compiler wants while reading a
  source file. What it is not is something to call at run time, and `-cljs` in its
  name is the library saying so.

  ClojureScript emits the call anyway, marked :cljs.analyzer/no-resolve so that
  nothing checks the name, and the program gets `undefined is not a function` the
  first time anything reads that tag. Measured: on one real application that made
  236 of 414 namespaces fail to compile here, where the name IS checked - for a tag
  no file in it reads. doc/cljs-compiler.md 5.49."
  [cenv sym]
  (if-let [^Namespace ns (env/find-cljs-ns cenv (symbol (namespace sym)))]
    (when-not (.findInternedVar ns (symbol (name sym)))
      (str "- " (.getName ns) " defines no ClojureScript var of that name"))
    "- there is no ClojureScript namespace of that name here"))

(def ^:private reported
  "The [tag sym why] triples already warned about, so that a REPL requiring fifty
  namespaces does not hear the same four lines fifty times. clojure.cljs.output
  keeps one of these for the same purpose and says why at more length.

  Once per FACT rather than once per run: cljs.reader is compiled afresh by every
  run, and what it would say is the same each time. A classpath that changes
  changes the triple, so the new answer is still heard."
  (atom #{}))

(defn- report-dropped!
  "Say which tags will not be in the runtime table, as the compile that found out
  goes past. Nothing is said twice.

  A WARNING AND NOT AN ERROR, for report-missing-js!'s reason one world over: the
  tag still reads while compiling, so nothing about the program being compiled is
  wrong. What changes is (read-string \"#ordered/map []\") in the browser, which
  gets the answer it already has for a tag nobody registered - and that answer names
  the tag, which `undefined is not a function` does not."
  [dropped]
  (let [fresh (remove @reported dropped)]
    (when (seq fresh)
      (swap! reported into fresh)
      (binding [*out* *err*]
        (println (str "WARNING: " (count fresh) " data reader"
                      (when (< 1 (count fresh)) "s")
                      " will not be in cljs.reader's runtime table:"))
        (doseq [[tag sym why] fresh]
          (println (str "  #" tag "  ->  " sym " " why)))
        (println (str "  Each of those still reads while compiling, on the JVM."
                      " What will not work is reading one at run time, where the"
                      " tag is simply not registered."))))))

(defmacro add-data-readers
  "ADAPTED (M6). The tags a USER registered, merged into the runtime reader's
  table: every entry of every data_readers.cljc on the classpath, as a tag symbol
  and a ClojureScript function that calls the reader the file named.

  Theirs reads the same map out of the compiler environment:

      (get @env/*compiler* :cljs.analyzer/data-readers)

  which cljs.closure/load-data-readers! puts there. Here the scan IS the registry
  - clojure.cljs.reader/user-data-readers, memoized on the classpath - so there is
  no compiler-environment key to read.

  THE CALL IS EMITTED, NOT THE FUNCTION. data_readers.cljc names a var by symbol,
  and that symbol is resolved twice against two different worlds: once on the JVM,
  so a tag can be read while compiling, and once in the expansion below, so the
  same name means the ClojureScript var of the same name at run time. Wrapping in
  (fn [x#] (f x#)) rather than passing f is theirs, and is what makes the name
  resolve where the expansion lands rather than here.

  ONLY FOR THE TAGS WHOSE SECOND RESOLUTION FINDS SOMETHING (5.49). The two worlds
  agree by convention and the convention is often not held - `unusable` above has
  the case that made us look - so the table holds the tags whose ClojureScript var
  really exists, and `report-dropped!` names the rest. ClojureScript tags the
  emitted symbol :cljs.analyzer/no-resolve, which turns off its undeclared-var
  warning and is what lets a call to nothing through; this compiler needs no such
  mark, because it emits no call it cannot resolve.

  THE QUESTION IS ASKED WHEN cljs.reader COMPILES, and that is the right moment
  because the driver compiles every data-reader namespace before anything else
  (driver/seed-state). So a var that is going to exist already does.

  Outside a compile there is nothing to ask - env/*cenv* is bound around a macro
  call and nowhere else - and then every tag is kept, because \"cannot ask\" is not
  \"the var is absent\".

  The tags of the LANGUAGE are not here and belong to the caller's map: #js and
  #queue are compile-time tags - one hands back a marker type and the other an
  ordinary form - and cljs.reader defines its own runtime readers for them."
  [default-readers]
  (let [cenv    env/*cenv*
        entries (for [[tag f] (reader/user-data-readers)
                      :let    [sym (:sym (meta f))]]
                  [tag sym (when cenv (unusable cenv sym))])
        dropped (filter #(nth % 2) entries)]
    (when (seq dropped)
      (report-dropped! dropped))
    `(merge ~default-readers
            ~(into {}
                   (keep (fn [[tag sym why]]
                           (when-not why [`'~tag `(fn [x#] (~sym x#))])))
                   entries))))
