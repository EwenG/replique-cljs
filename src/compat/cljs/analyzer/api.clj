(ns ^{:doc "cljs.analyzer.api, under the name a library writes it.

  ClojureScript keeps two front doors onto its symbol table: cljs.analyzer, which
  is internal, and this one, which is documented. A macro namespace that wants to
  ask the compiler something is supposed to come through here, and several do -
  hx's useSmartEffect resolves every symbol in its body to work out the dependency
  vector React needs.

  This compiler answers those questions out of clojure.cljs.analyzer-api, which
  already implements exactly this namespace and says so in its own docstring. What
  was missing was the NAME: a macro namespace is ordinary Clojure, loaded by
  `require' off the classpath, so (:require [cljs.analyzer.api]) needs a file at
  cljs/analyzer/api.clj and nothing else will do. Without one the library does not
  half-work, it does not load at all - `Could not locate cljs/analyzer/api.cljc on
  classpath' - which is a sentence about a file rather than about a fork.

  THE DOCUMENTED DOOR IS THE ONLY ONE THAT COULD HAVE BEEN OPENED, and that is a
  fact about its shape rather than a preference. cljs.analyzer.api declares no
  dynamic var: thirty-one names, twenty-five functions, five macros and one plain
  value, and every var it surfaces - *cljs-file*, *cljs-ns*, *compiler* - it
  surfaces through a zero argument reader (current-file, current-ns,
  current-state). A function forwards. A DYNAMIC VAR CANNOT: a Var belongs to
  exactly one namespace and a qualified read finds only an INTERNED one, because
  Compiler.resolveIn goes to Namespace.findInternedVar, which refuses a var whose
  ns is not this one. `refer' does not help - the mapping is there, the ns check
  still fails. So a cljs.analyzer here could never have been more than a handful
  of functions around a set of vars it had no way to be, and a def of *cljs-file*
  would have been a SECOND var, bound by nothing, reading nil forever: a library
  that loaded, ran, and quietly recorded the wrong file. There is no such file.
  Code reaching through the internal door is asked to come through this one
  instead, which is a change of one symbol at the call site and the thing
  ClojureScript's own documentation has always said to do.

  SEVEN OF THE THIRTY-ONE, which is what clojure.cljs.analyzer-api carries: the
  six cljs/test.cljc asks for and current-file. A library reaching for an eighth
  gets `Unable to resolve symbol' naming the one it wanted, at the line that
  wanted it, which is the report to have - the alternative is a stub answering
  plausibly for a pass this compiler does not run.

  ClojureScript's versions take an optional compiler-state first argument. Ours do
  not, for the reason clojure.cljs.env's docstring gives - the state is
  clojure.cljs.env/*cenv* - so a caller passing one gets an arity error rather
  than a wrong answer.

  See doc/cljs-compiler.md 5.66."}
  cljs.analyzer.api
  (:refer-clojure :exclude [all-ns find-ns ns-interns ns-resolve resolve])
  (:require [clojure.cljs.analyzer-api :as api]))

(defn resolve
  "The var `sym' names in `env', as a map, or nil when there is none.

  NIL AND NOT A SYNTHESISED NAME, which is the difference between this and
  clojure.cljs.analyzer/resolve-var and the reason both exist. A caller asking
  whether a name is there - which is what everything through this door is doing -
  needs the answer to be no when it is no."
  [env sym]
  (api/resolve env sym))

(defn current-file
  "The file being analysed, or nil outside one.

  THE ANSWER cljs.analyzer/*cljs-file* USED TO GIVE, and the reason this namespace
  can be written at all: the var could not be forwarded, a function reading it
  can. A path under a source directory - my_lib/core.cljs - rather than the
  absolute one ClojureScript's driver hands its own var, so a caller that prints
  it sees a shorter string than it used to.

  There is no current-line to go with it. A macro wanting the line it is being
  expanded at reads (meta &form), which is where this compiler keeps it;
  ClojureScript reads the same metadata on the way to putting it in &env, and &env
  here does not carry it."
  []
  (api/current-file))

(defn get-options
  "The compiler options in force."
  []
  (api/get-options))

(defn all-ns
  "The names of every ClojureScript namespace this environment holds."
  []
  (api/all-ns))

(defn find-ns
  "The analysis map of the namespace called `sym', or nil."
  [sym]
  (api/find-ns sym))

(defn ns-resolve
  "The var named `sym' in the namespace `ns', as a map, or nil."
  [ns sym]
  (api/ns-resolve ns sym))

(defn ns-interns
  "The vars interned in `ns', as a map of name to var map."
  [ns]
  (api/ns-interns ns))
