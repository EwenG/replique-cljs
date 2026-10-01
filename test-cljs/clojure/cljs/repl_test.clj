;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The REPL, against a real node process.

  One runtime for the whole namespace, because starting one costs a process; each
  test compiles in a namespace of its own, so what one test defines is not what
  another test sees. That the namespaces stay apart is itself a claim about the
  registry, and one test says so directly.

  Skipped when node is not on PATH."}
  clojure.cljs.repl-test
  (:require [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.java.io :as io]
            [clojure.cljs.repl :as repl]
            [clojure.cljs.source-map :as sm]
            [clojure.cljs.test-harness :as h]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]])
  (:import [clojure.lang Namespace]
           [java.io StringReader StringWriter]))

(use-fixtures :each h/cursor)

(def ^:dynamic *runtime* nil)
(def ^:private program-out (StringWriter.))

(def ^:private runtime-dir
  "The directory the session's runtime fetches from. Named here rather than left to
  node-runtime's own temporary one because cljs.core has to be compiled INTO it: a
  script's prologue opens with await $CLJS.require(\"cljs.core\") since §5.12, and
  that reads a file off disk."
  (delay (h/temp-dir)))

(def ^:private core-cenv
  "The environment cljs.core was compiled in, kept rather than thrown away.

  Most tests here want a bare one - they are about the REPL's machinery and not
  about the standard library, and a bare environment is faster and says so. The R2
  history tests cannot: *1, *2, *3 and *e are cljs.core's vars, so a compile
  environment that has never analysed cljs.core has nowhere to put a value.

  Shared, with a fresh NAMESPACE per caller, for the reason test-harness/core-env
  is: building a second would mean analysing core.cljs again."
  (atom nil))

(use-fixtures :once
  (fn [f]
    (if h/node?
      (env/with-current-ns 'cljs.user
       (let [c (env/compile-env {:core-macros 'cljs.core})]
        (driver/compile-namespace! c 'cljs.core {:out-dir @runtime-dir})
        (reset! core-cenv c)
        (with-open [rt (repl/node-runtime {:dir @runtime-dir :out program-out})]
          (binding [*runtime* rt] (f)))))
      (f))))

(defn- cenv [ns-sym] (env/compile-env {:ns ns-sym}))

(defn- with-core
  "core-cenv, positioned in `ns-sym`."
  [ns-sym]
  (env/set-current-ns! ns-sym)
  @core-cenv)

(defn- values
  "The :value of each result of evaluating `src` in a namespace of its own."
  [ns-sym src]
  (mapv :value (repl/eval-src (cenv ns-sym) *runtime* src)))

(defn- core-values
  "values, in an environment that has cljs.core analysed."
  [ns-sym src]
  (mapv :value (repl/eval-src (with-core ns-sym) *runtime* src)))

;; --- the R0 oracle ----------------------------------------------------------

(h/deftest-when h/node? test-a-var-can-be-redefined-and-callers-see-the-new-one
  ;; doc/cljs-repl.md 9: the test that is the whole point of 3, and the reason a
  ;; var had to become a property of a namespace object rather than a
  ;; module-scoped binding. g calls f by reading a property, so redefining f is
  ;; visible to a g that was defined before it.
  (is (= ["#object[Function oracle$core$f]" "2"
          "#object[Function oracle$core$g]" "3"
          "#object[Function oracle$core$f]" "102"]
         (values 'oracle.core
                 "(def f (fn* ([x] (js* \"~{} + 1\" x))))
                  (f 1)
                  (def g (fn* ([x] (f (js* \"~{} + 1\" x)))))
                  (g 1)
                  (def f (fn* ([x] (js* \"~{} + 100\" x))))
                  (g 1)"))))

(h/deftest-when h/node? test-namespaces-are-separate-objects
  ;; Two namespaces defining the same name do not collide, and neither can see the
  ;; other: the registry is keyed by namespace name, and a var is a property of the
  ;; object found there.
  ;; one compile environment, its cursor moved between namespaces - which is what
  ;; in-ns will do when M3 brings it
  (let [c (cenv 'sep.a)
        v (fn [src] (mapv :value (repl/eval-src c *runtime* src)))]
    (is (= ["1"] (v "(def x 1)")))
    (env/set-current-ns! 'sep.b)
    (is (= ["2"] (v "(def x 2)")))
    (is (= ["2"] (v "x")))
    (env/set-current-ns! 'sep.a)
    (is (= ["1"] (v "x"))))
  ;; and the prologue really is per script, since each script is its own scope
  (is (str/includes? (repl/compile-form (cenv 'sep.a) 1) "$ns(\"sep.a\")")))

;; --- results ----------------------------------------------------------------

(h/deftest-when h/node? test-a-value-is-printed-where-it-lives
  ;; 8: printing happens in the runtime and the value travels as a string.
  ;;
  ;; SINCE §5.12 THAT PRINTER ASKS cljs.core FIRST, because a ClojureScript value
  ;; knows how to print itself and nothing in the prelude could do it as well. What
  ;; is left below is the fallback, for values cljs.core does not own: a number, a
  ;; string, a JavaScript array. undefined is not folded into nil, and ##Inf, ##NaN
  ;; and -0 keep their ClojureScript spellings.
  (is (= ["42" "\"hi\"" "true" "nil" "undefined" "##Inf" "##NaN" "-0"
          "#js [1 2]" "#js {:code 1}" ":kw" "[1 2]" "{:a 1}"]
         (values 'print.core
                 "42 \"hi\" true nil (js* \"undefined\") (js* \"1/0\")
                  (js* \"0/0\") (js* \"-0\") (js* \"[1, 2]\") (js* \"({code: 1})\")
                  :kw [1 2] {:a 1}"))))

(h/deftest-when h/node? test-a-result-says-what-it-was-printed-under
  ;; read AFTER the script ran, so the form that set! one of them answers with what
  ;; it set - and a later form is printed under it, by cljs.core's own printer
  (let [eval! (fn [src] (repl/eval-src (with-core 'params.core) *runtime* src))]
    (try
      (let [[set-r range-r] (eval! "(set! *print-length* 2) (range 5)")]
        (is (= {:print-length 2 :print-level nil :print-meta false} (:params set-r)))
        (is (= "(0 1 ...)" (:value range-r)))
        (is (= {:print-length 2 :print-level nil :print-meta false} (:params range-r))))
      (let [[r] (eval! "(set! *print-meta* true)")]
        (is (= true (:print-meta (:params r)))))
      (finally (eval! "(set! *print-length* nil) (set! *print-meta* false)")))))

(h/deftest-when h/node? test-a-runtime-error-comes-back-as-one
  (let [[r] (repl/eval-src (cenv 'err.core) *runtime*
                           "(throw (js* \"new Error(\\\"boom\\\")\"))")]
    (is (= :error (:status r)))
    (is (= "Error: boom" (:value r)))
    (is (str/includes? (:stacktrace r) "Error: boom")))
  ;; JavaScript lets you throw anything, and String() on an object says
  ;; "[object Object]" - which is why a non-Error goes through the printer
  (let [[r] (repl/eval-src (cenv 'err.core) *runtime*
                           "(js* \"(() => { throw {code: 42}; })()\")")]
    ;; #js {:code 42}, which is cljs.core's spelling of a JavaScript object and not
    ;; the prelude's - the printer hands anything cljs.core can print to pr-str
    (is (= [:error "#js {:code 42}"] [(:status r) (:value r)]))))

(h/deftest-when h/node? test-a-compile-error-says-which-side-it-happened-on
  (let [[r] (repl/eval-src (cenv 'err.core) *runtime* "(undefined-symbol)")]
    (is (= :error (:status r)))
    (is (= :compile (:phase r)))
    (is (str/includes? (:value r) "neither a local nor a var")))
  ;; and it does not end the conversation: the next form still evaluates
  (is (= ["7"] (values 'err.core "(js* \"7\")"))))

(h/deftest-when h/node? test-a-value-that-cannot-be-printed-does-not-lose-the-turn
  ;; A getter can throw. A REPL that dies while printing an answer it already has
  ;; is worse than one that says it could not print it.
  (is (= ["#object[unprintable nope]"]
         (values 'print.core
                 "(js* \"({ get boom() { throw new Error('nope'); } })\")")))
  ;; a cycle terminates, and so does something merely deep
  (is (= ["#js {\"self\" #object[circular]}"]
         (values 'print.core
                 "(js* \"(() => { const a = {}; a.self = a; return a; })()\")")))
  (let [deep (first (values 'print.core
                            "(js* \"(() => { let a = 1; for (let i = 0; i < 40; i++) a = [a]; return a; })()\")"))]
    (is (str/includes? deep "#js [...]"))
    (is (> 100 (count deep)))))

;; --- the wire ---------------------------------------------------------------

(h/deftest-when h/node? test-any-character-survives-the-round-trip
  ;; The JVM writes JSON and node writes EDN, so neither side parses the format it
  ;; is worst at. Both escape what would break the line framing - but only if the
  ;; escaping is right, and js* means emitted JavaScript can hold any character.
  (is (= ["\"a\\u0000b\""] (values 'wire.core "\"a\\u0000b\"")))
  (is (= ["\"tab\\there\""] (values 'wire.core "\"tab\\there\"")))
  ;; U+2028 is a line separator that neither format escapes and neither reader
  ;; treats as one, so it has to arrive intact in both directions
  (is (= ["3"] (values 'wire.core "(js* \"'x\\u2028y'.length\")")))
  (is (= [8232] (mapv int (str/replace (first (values 'wire.core "\"\\u2028\""))
                                       "\"" "")))))

(h/deftest-when h/node? test-the-runtime-s-own-output-reaches-the-user
  ;; Before M5 there is no *print-fn* and so no :print channel: the process's
  ;; stdout is that channel, pumped to wherever the runtime was told to write.
  (values 'out.core "(js* \"console.log('hello from the program'), 1\")")
  (is (loop [n 0]
        (cond (str/includes? (str program-out) "hello from the program") true
              (< 40 n) false
              :else (do (Thread/sleep 50) (recur (inc n)))))))

;; --- the loop ---------------------------------------------------------------

(h/deftest-when h/node? test-the-repl-loop-prints-a-prompt-and-a-value-per-form
  (let [out (StringWriter.)]
    (repl/repl (cenv 'loop.core) *runtime*
               {:in (StringReader. "(def z 5)\nz\n") :out out})
    (is (= "loop.core=> 5\nloop.core=> 5\nloop.core=> \n" (str out)))))

(h/deftest-when h/node? test-a-malformed-form-does-not-end-the-loop
  ;; read-one leaves the reader inside the form it could not read and declines to
  ;; choose a recovery; the loop's policy is clojure.main's - drop the rest of the
  ;; line, because a REPL user types one form per line.
  (let [out (StringWriter.)]
    (repl/repl (cenv 'loop.core) *runtime*
               {:in (StringReader. "1 ) 2\n3\n") :out out})
    ;; 1 was read, ) was refused, 2 died with the rest of its line, 3 survived
    (is (= (str "loop.core=> 1\n"
                "loop.core=> error (read): Unmatched delimiter: )\n"
                "loop.core=> 3\n"
                "loop.core=> \n")
           (str out)))))

;; --- the ns form at the REPL ------------------------------------------------

(h/deftest-when h/node? test-the-oracle-across-two-namespaces
  ;; doc/cljs-repl.md 9 asked for the caller to live in a SECOND namespace, and at
  ;; R0 it could not: analyze-symbol refused every qualified symbol. This is that
  ;; test. §3's claim is about when the property is read rather than about who
  ;; reads it, so the same-namespace version above already stood - but the version
  ;; the doc specified is the one a user would recognise as a REPL working.
  (let [c (cenv 'cljs.user)
        v (fn [src] (mapv :value (repl/eval-src c *runtime* src)))]
    (is (= ["nil" "#object[Function two$lib$f]"]
           (v "(ns two.lib) (def f (fn* ([x] (js* \"~{} + 1\" x))))")))
    (is (= ["nil" "#object[Function two$app$g]" "3"]
           (v "(ns two.app (:require [two.lib :as lib]))
               (def g (fn* ([x] (lib/f (js* \"~{} + 1\" x)))))
               (g 1)")))
    ;; f redefined from the namespace that owns it...
    (is (= ["nil" "#object[Function two$lib$f]"]
           (v "(ns two.lib) (def f (fn* ([x] (js* \"~{} + 100\" x))))")))
    ;; ...and g, defined in another namespace before that, calls the new one
    (is (= ["nil" "102"] (v "(ns two.app) (g 1)")))))

(h/deftest-when h/node? test-the-cursor-moves-and-the-prologue-follows-it
  (let [c (cenv 'cljs.user)]
    (repl/eval-src c *runtime* "(ns cursor.app (:require [cursor.lib :as l]))")
    (is (= 'cursor.app env/*current-ns*))
    ;; the script for the NEXT input names both namespaces, because a var in
    ;; either is a property of one of the objects it binds
    (let [js (repl/compile-form c '(js* "1"))]
      (is (str/includes? js "$ns(\"cursor.app\")"))
      (is (str/includes? js "$ns(\"cursor.lib\")"))
      ;; and every script re-requires, so a runtime restarted underneath the
      ;; session refetches instead of binding an empty namespace object
      (is (str/includes? js "await $CLJS.require(\"cursor.lib\")")))))

(h/deftest-when h/node? test-a-bad-ns-form-is-a-compile-error-and-the-repl-goes-on
  (let [c (cenv 'ns.errs)
        r (repl/eval-src c *runtime*
                         "(ns ns.errs (:require [nope.ns :refer [gone]]))
                          (js* \"41 + 1\")")]
    (is (= :error (:status (first r))))
    (is (= :compile (:phase (first r))))
    (is (str/includes? (:value (first r)) "Cannot refer gone"))
    ;; the cursor never moved, so the next form compiles where it was
    (is (= 'ns.errs env/*current-ns*))
    (is (= "42" (:value (second r))))))

(h/deftest-when h/node? test-set!-of-a-var-in-another-namespace
  ;; M2 recorded this as working the day cross-namespace references landed, on the
  ;; strength of a var being a property: assignment needs no more than a reference
  (let [c (cenv 'cljs.user)
        v (fn [src] (mapv :value (repl/eval-src c *runtime* src)))]
    (is (= ["nil" "7"] (v "(ns setter.lib) (def x 7)")))
    (is (= ["nil" "9" "9"]
           (v "(ns setter.app (:require [setter.lib :as s]))
               (set! s/x 9)
               s/x")))))

;; --- one world, two cursors -------------------------------------------------

(h/deftest-when h/node? test-a-repl-keeps-its-cursor-to-itself
  ;; doc/cljs-repl.md §10, taken: ONE compile environment per target, MANY REPLs on
  ;; it, each standing somewhere of its own. That is the split between a field and
  ;; a binding - the two worlds are fields of the environment, the cursor is
  ;; env/*current-ns* - and this is the half of it with a consequence you can see.
  ;;
  ;; A session moves its cursor by (in-ns ...) and by (ns ...); before R3 there is
  ;; one loop per process, so what stands in for the second session here is this
  ;; test itself, holding the same environment while the loop runs.
  (let [c   (cenv 'caller.here)
        out (StringWriter.)]
    (repl/repl c *runtime* {:ns 'session.one
                            :in  (StringReader. "(in-ns 'session.two)\n(def x 1)\n")
                            :out out})
    ;; it started where it was told rather than where its caller was ...
    (is (str/starts-with? (str out) "session.one=> "))
    ;; ... it moved ...
    (is (str/includes? (str out) "session.two=> "))
    ;; ... and the caller did not move with it, though there is one environment
    (is (= 'caller.here env/*current-ns*))
    ;; and the var it defined is in the world the caller is holding: a cursor is
    ;; per session, a symbol table is not
    (is (some? (.findInternedVar ^Namespace (env/cljs-ns c 'session.two) 'x)))))

;; --- R1: loading ------------------------------------------------------------
;;
;; A runtime of its own per test, unlike everything above: a reload test has to
;; start from a runtime holding nothing, and it needs the output directory the
;; driver compiles into to be the one that runtime fetches from.

(defn- with-project*
  [sources f]
  (let [src (h/write-sources! sources)
        out (h/temp-dir)]
    (try
      (with-open [rt (repl/node-runtime {:dir out :out program-out})]
        (f {:cenv (env/compile-env {:ns 'cljs.user})
            :rt   rt
            :src  src
            :opts {:out-dir out :source-paths [src]}}))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(defn- vals-in
  [{:keys [cenv rt opts]} src]
  (mapv :value (repl/eval-src cenv rt src opts)))

(defn- edit!
  [{:keys [src]} ns-sym text]
  (h/write-sources! src {ns-sym text}))

(def ^:private two-files
  '{my-lib.core "(ns my-lib.core)
                 (def helper (fn* ([x] (js* \"~{} * 2\" x))))"
    app.core    "(ns app.core (:require [my-lib.core :as lib]))
                 (def use-it (fn* ([] (lib/helper 21))))"})

(h/deftest-when h/node? test-r1-oracle-a-two-file-program-reloaded-both-ways
  ;; doc/cljs-repl.md 9. Reloading the DEPENDENCY and having the dependent pick it
  ;; up is the half that only works because a var is a property: use-it was
  ;; compiled before helper was redefined, and calls it by reading a property of a
  ;; namespace object that outlives both versions.
  (with-project*
   two-files
   (fn [p]
     (is (= ["nil" "42"] (vals-in p "(require '[app.core :as a]) (a/use-it)")))

     ;; the dependency, reloaded: the dependent sees the new definition without
     ;; being recompiled or reloaded itself
     (edit! p 'my-lib.core
            "(ns my-lib.core) (def helper (fn* ([x] (js* \"~{} * 3\" x))))")
     (is (= ["nil" "63"] (vals-in p "(require 'my-lib.core :reload) (a/use-it)")))

     ;; and the dependent, reloaded: it still finds the dependency, which the
     ;; runtime already holds, so nothing is fetched
     (edit! p 'app.core
            "(ns app.core (:require [my-lib.core :as lib]))
             (def use-it (fn* ([] (lib/helper 100))))")
     (is (= ["nil" "300"] (vals-in p "(require 'app.core :reload) (a/use-it)"))))))

(h/deftest-when h/node? test-remove-var-undefines-one-var
  ;; A def deleted from a source file is NOT removed by reloading that file - which
  ;; defs vanished is a question about provenance, and the whole-file sweep that
  ;; answers it properly is doc/cljs-repl.md 7.3, still to come. remove-var needs no
  ;; model because you named the var, and it is what Replique offers meanwhile.
  (with-project*
   '{lib.core  "(ns lib.core) (def kept 1) (def doomed 99)"
     user.core "(ns user.core (:require [lib.core :refer [doomed]]))"}
   (fn [p]
     (is (= ["nil" "99"] (vals-in p "(require '[lib.core :as l]) l/doomed")))
     (is (= ["nil" "nil" "99"]
            (vals-in p "(require 'user.core) (in-ns 'user.core) doomed")))
     (is (= ["nil" "nil"]
            (vals-in p "(in-ns 'cljs.user) (remove-var 'lib.core/doomed)")))

     ;; gone from the namespace that defined it
     (let [r (first (repl/eval-src (:cenv p) (:rt p) "l/doomed" (:opts p)))]
       (is (= :compile (:phase r)))
       (is (str/includes? (:value r) "No such var")))
     ;; and from the namespace that REFERRED it, which is the half a var-by-var
     ;; removal is easy to get wrong: the mapping there holds the same Var, and
     ;; leaving it would let the deleted name go on resolving
     (let [r (last (repl/eval-src (:cenv p) (:rt p) "(in-ns 'user.core) doomed"
                                  (:opts p)))]
       (is (str/includes? (:value r) "neither a local nor a var")))

     ;; and gone from the runtime, which is what makes a call to it fail rather
     ;; than run the version you thought you had deleted
     (is (= ["nil" "true" "1"]
            (vals-in p "(in-ns 'cljs.user)
                        (js* \"globalThis.$CLJS.ns(\\\"lib.core\\\").doomed === undefined\")
                        l/kept")))

     ;; a name that is not there says so, rather than quietly doing nothing
     (is (str/includes?
          (:value (first (repl/eval-src (:cenv p) (:rt p) "(remove-var 'lib.core/nope)"
                                        (:opts p))))
          "No such var: lib.core/nope"))
     (is (str/includes?
          (:value (first (repl/eval-src (:cenv p) (:rt p) "(remove-var 'unqualified)"
                                        (:opts p))))
          "needs a qualified symbol")))))

(h/deftest-when h/node? test-require-without-a-flag-does-not-reload
  ;; plain require ships a question rather than a body - the runtime answers it
  ;; from what it holds - so an edited file is compiled to disk but the running
  ;; definition stands, which is what require means in Clojure too
  (with-project*
   two-files
   (fn [p]
     (is (= ["nil" "42"] (vals-in p "(require '[app.core :as a]) (a/use-it)")))
     (edit! p 'my-lib.core
            "(ns my-lib.core) (def helper (fn* ([x] (js* \"~{} * 3\" x))))")
     (is (= ["nil" "42"] (vals-in p "(require 'my-lib.core) (a/use-it)")))
     (is (= ["nil" "63"] (vals-in p "(require 'my-lib.core :reload) (a/use-it)"))))))

(h/deftest-when h/node? test-reload-all-ships-the-whole-graph
  (with-project*
   two-files
   (fn [p]
     (is (= ["nil" "42"] (vals-in p "(require '[app.core :as a]) (a/use-it)")))
     ;; only the dependency is edited, and app.core is the namespace reloaded -
     ;; :reload would ship app.core's body alone, where :reload-all ships
     ;; my-lib.core's too, in dependency order
     (edit! p 'my-lib.core
            "(ns my-lib.core) (def helper (fn* ([x] (js* \"~{} * 5\" x))))")
     ;; :reload first, to show the two differ: app.core's body re-runs, but its
     ;; prologue only ASKS for my-lib.core, which the runtime already holds
     (is (= ["nil" "42"] (vals-in p "(require 'app.core :reload) (a/use-it)")))
     (is (= ["nil" "105"] (vals-in p "(require 'app.core :reload-all) (a/use-it)"))))))

(h/deftest-when h/node? test-load-file-is-always-forced
  (with-project*
   two-files
   (fn [p]
     (is (= ["nil" "42"] (vals-in p "(require '[app.core :as a]) (a/use-it)")))
     (edit! p 'my-lib.core
            "(ns my-lib.core) (def helper (fn* ([x] (js* \"~{} * 4\" x))))")
     (let [path (str (io/file (:src p) "my_lib/core.cljs"))]
       (is (= ["nil" "84"] (vals-in p (str "(load-file \"" path "\") (a/use-it)"))))))))

(h/deftest-when h/node? test-in-ns-moves-the-cursor-and-require-does-not
  (with-project*
   two-files
   (fn [{:keys [cenv] :as p}]
     (vals-in p "(require '[my-lib.core :as lib])")
     ;; compiling a file runs its ns form, which moves the cursor by design - so
     ;; without the driver putting it back, a require silently moved the user
     (is (= 'cljs.user env/*current-ns*))
     (vals-in p "(in-ns 'my-lib.core)")
     (is (= 'my-lib.core env/*current-ns*))
     ;; and in-ns reaches a namespace the session made up, with no file anywhere
     (vals-in p "(in-ns 'invented.here)")
     (is (= 'invented.here env/*current-ns*))
     (is (= ["7"] (vals-in p "(def x 7)")))
     (let [r (first (repl/eval-src cenv (:rt p) "(in-ns \"nope\")" (:opts p)))]
       (is (str/includes? (:value r) "in-ns takes an unqualified symbol"))))))

(h/deftest-when h/node? test-a-shipped-body-registers-its-module-too
  ;; The hole this closes is quiet, and it takes three steps to open: reload a
  ;; namespace the runtime does not yet hold, so its BODY defines it and no file is
  ;; ever fetched; redefine something in it at the REPL; then load a namespace that
  ;; imports it. That third step is a static import, which consults the ES module
  ;; system's registry rather than $CLJS.loaded - and the module is not in it, so
  ;; the file is fetched and evaluated over the top, reverting the REPL definition.
  ;; A shipped body therefore requires itself first: only a fetch registers the URL.
  (with-project*
   two-files
   (fn [p]
     (is (= ["nil"] (vals-in p "(require 'my-lib.core :reload)")))
     (is (= ["nil" "#object[Function my_lib$core$helper]" "1005"]
            (vals-in p "(in-ns 'my-lib.core)
                        (def helper (fn* ([x] (js* \"~{} + 1000\" x))))
                        (helper 5)")))
     (is (= ["nil" "nil"] (vals-in p "(in-ns 'cljs.user) (require '[app.core :as a])")))
     ;; the REPL's definition stands, and app.core - compiled against the file -
     ;; calls it
     (is (= ["nil" "1005"] (vals-in p "(in-ns 'my-lib.core) (helper 5)")))
     (is (= ["nil" "1021"] (vals-in p "(in-ns 'cljs.user) (a/use-it)"))))))

(h/deftest-when h/node? test-a-cold-reload-runs-the-body-once
  ;; A namespace body is not only definitions - it can have top-level effects, and
  ;; those are the reason the shipped body is SKIPPED when the module has to be
  ;; fetched. Fetching runs the file; running the body as well would run them a
  ;; second time. The two paths are exclusive, and this counts.
  (with-project*
   '{effects.core "(ns effects.core)
                   (js* \"globalThis.__hits = (globalThis.__hits || 0) + 1\")
                   (def n (fn* ([] (js* \"globalThis.__hits\"))))"}
   (fn [p]
     ;; cold, and asked for with :reload - the module is fetched, the body skipped
     (is (= ["nil" "1"] (vals-in p "(require '[effects.core :as e] :reload) (e/n)")))
     ;; warm: the module system will not evaluate that file again, so the body is
     ;; the only way to re-run it, and it runs exactly once more
     (is (= ["nil" "2"] (vals-in p "(require 'effects.core :reload) (e/n)")))
     (is (= ["nil" "3"] (vals-in p "(require 'effects.core :reload) (e/n)")))
     ;; and plain require re-runs nothing at all
     (is (= ["nil" "3"] (vals-in p "(require 'effects.core) (e/n)"))))))

;; --- the whole REPL, from one call ---------------------------------------------

(h/deftest-when h/node? test-node-repl-starts-with-cljs-core-loaded
  ;; Everything above drives eval-src against a runtime the fixture prepared. This
  ;; drives node-repl, which prepares its own - and preparing it is the part worth
  ;; testing, because since §5.12 a REPL that has not compiled cljs.core into its
  ;; output directory cannot evaluate a keyword, let alone call a core function.
  ;;
  ;; It also pins :core-macros defaulting to cljs.core (env/compile-env): a REPL
  ;; that cannot expand defn is not one.
  ;;
  ;; ON A BARE THREAD, AND THAT IS THE POINT OF THE THREAD. env/*current-ns* moves
  ;; by set!, which needs a binding to move; h/cursor gives every test one, and a
  ;; user calling (repl/node-repl) from a plain Clojure REPL has none - so node-repl
  ;; has to establish its own. When it did not, that call threw "Can't
  ;; change/establish root binding" on the first line while this test, wrapped in
  ;; the fixture's binding, passed. A future would convey the caller's bindings and
  ;; hide it again; a Thread conveys none, which is the situation being tested.
  (let [out   (StringWriter.)
        threw (atom nil)
        t     (Thread.
               #(try
                  (repl/node-repl {:in  (StringReader. "(defn twice [x] (* 2 x))
                                          (twice 21)
                                          {:a [1 2] :b :c}
                                          (reduce + (map inc (range 4)))")
                                   :out out
                                   :program-out program-out})
                  (catch Throwable e (reset! threw e))))]
    (.start t)
    (.join t 180000)
    (is (nil? @threw) (some-> ^Throwable @threw .getMessage))
    (let [s (str out)]
      ;; a macro expanded, a var was defined and called
      (is (str/includes? s "42") s)
      ;; real ClojureScript data, printed by cljs.core through the runtime's printer
      (is (str/includes? s "{:a [1 2], :b :c}") s)
      ;; and an unqualified core name resolved, which is the refer half
      (is (str/includes? s "10") s))))

(h/deftest-when h/node? test-a-repl-input-does-not-pin-an-arity
  ;; §5.33. A file is compiled with static arity dispatch: (two 1 2) becomes
  ;; two.cljs$core$IFn$_invoke$arity$2(1, 2), which is faster and which names an
  ;; arity. A REPL input is not, and this is the reason - the input typed three
  ;; lines ago has to keep working after a redefinition that changes the shape,
  ;; and an ordinary fn carries no arity properties at all.
  ;;
  ;; The same line ClojureScript draws with *cljs-static-fns*.
  ;; the first value is nil rather than the function because a multi-arity defn
  ;; expands to a def followed by the set!s that hang the arities on it
  (is (= ["nil" "2"
          "#object[Function oracle$sd$g]" "2"
          "#object[Function oracle$sd$two]" "20"]
         (values 'oracle.sd
                 "(defn two ([x] x) ([x y] y))
                  (two 1 2)
                  (defn g [] (two 1 2))
                  (g)
                  (def two (fn* ([x y] (js* \"~{} * 10\" y))))
                  (g)")))

  ;; and the spelling itself, so the reason is checked and not only its effect
  (let [c (cenv 'oracle.sd2)]
    (repl/eval-src c *runtime* "(defn two ([x] x) ([x y] y))")
    (is (str/includes? (repl/compile-form c '(two 1 2)) "two.call(null, (1), (2))"))))

;; --- R2: the history vars ---------------------------------------------------
;;
;; *1, *2 and *3 are assigned by the compiled form (repl/remembering) and *e by the
;; runtime's catch, which is the only thing that can see a throw. One runtime serves
;; this whole namespace, so cljs.core/*1 is shared across these tests the way it is
;; shared across a session - which is why each of them establishes every value it
;; asserts on rather than assuming what it inherited.

(h/deftest-when h/node? test-the-repl-remembers-the-last-three-values
  (is (= ["3" "40" "\"ab\"" "[\"ab\" 40 3]"]
         (core-values 'star.history
                 "(+ 1 2)
                  (* 10 4)
                  (str \"a\" \"b\")
                  [*1 *2 *3]"))))

(h/deftest-when h/node? test-looking-at-the-history-does-not-rewrite-it
  ;; ClojureScript's own choice (cljs.repl/wrap-fn): the four history vars are not
  ;; wrapped, so reading *2 does not make it *1. Without it the history would move
  ;; every time it was looked at, which is the one thing a history must not do.
  (is (= [":a" ":b" ":b" ":a" "[:b :a]"]
         (core-values 'star.looking
                 "(identity :a)
                  (identity :b)
                  *1
                  *2
                  [*1 *2]"))))

(h/deftest-when h/node? test-an-ns-form-does-not-shift-the-history
  ;; Also ClojureScript's list. require, load-file, in-ns and remove-var need no
  ;; entry because they are REPL specials here and never reach a compiler at all.
  (is (= [":before" "nil" ":before"]
         (core-values 'star.moving
                 "(identity :before)
                  (ns star.moved)
                  *1"))))

(h/deftest-when h/node? test-the-last-exception-is-the-value-that-was-thrown
  ;; The point of setting *e from the catch rather than from the result: the result
  ;; is a string on its way to the JVM, and (ex-data *e) needs the object.
  (let [rs (repl/eval-src (with-core 'star.thrown) *runtime*
                          "(throw (ex-info \"boom\" {:a 1}))
                           (ex-message *e)
                           (ex-data *e)")]
    (is (= :error (:status (first rs))) (pr-str (first rs)))
    (is (= ["\"boom\"" "{:a 1}"] (mapv :value (rest rs))))))

(h/deftest-when h/node? test-a-form-that-throws-leaves-the-value-history-alone
  ;; The assignments are the last thing the form does, so a throw never reaches
  ;; them - which is what makes *1 still usable in the input that diagnoses the
  ;; failure.
  (let [rs (repl/eval-src (with-core 'star.kept) *runtime*
                          "(identity :kept)
                           (throw (js/Error. \"x\"))
                           *1")]
    (is (= [:success :error :success] (mapv :status rs)))
    (is (= ":kept" (:value (last rs))))))

;; --- R2: //# sourceURL ------------------------------------------------------

(h/deftest-when h/node? test-a-repl-input-is-named-and-never-renamed-onto
  ;; doc/cljs-output-layout.md §4's second rule, and the opposite of the first: a
  ;; reloaded namespace body is a new version of a file that exists, so it takes
  ;; that file's URL; a typed form is not a version of anything, so it takes a name
  ;; nothing has used before. Reusing one name for a succession of different
  ;; programs is precisely what makes a debugger show the wrong source.
  (let [url  #(last (str/split-lines (repl/compile-form (with-core 'url.core) %)))
        urls (mapv url ['(+ 1 1) '(+ 2 2) '(+ 3 3)])]
    (is (every? #(re-matches #"//# sourceURL=repl/url\.core/\d+\.js" %) urls)
        (pr-str urls))
    (is (= 3 (count (distinct urls))) (pr-str urls))
    (testing "and they are under repl/, where neither the driver nor the goog subset writes"
      (is (not-any? #(str/includes? % "=ns/") urls)))))

(h/deftest-when h/node? test-a-stack-trace-names-the-input-it-came-from
  ;; What the URL is for, and the first half of R2's symbolicated stacks: without
  ;; it V8 calls an eval'd script <anonymous> and spells the frame as an offset into
  ;; runtime.js, which names the machinery rather than the mistake.
  (let [r (first (repl/eval-src (with-core 'stack.core) *runtime*
                                "(throw (js/Error. \"named\"))"))]
    (is (= :error (:status r)))
    (is (re-find #"repl/stack\.core/\d+\.js" (:stacktrace r))
        (:stacktrace r))))

(h/deftest-when h/node? test-a-stack-trace-is-read-back-as-clojurescript
  ;; R2's headline, end to end and with nothing stubbed: a real file compiled by
  ;; the driver, a real throw in node, V8's own stack string, and the .js.map the
  ;; driver wrote beside the module (§5.43) read back on the JVM (§5.45).
  ;;
  ;; Down to the column, which is worth pinning rather than loosening: 4:10 is the
  ;; (js/Error. ...) inside the throw and 7:4 is the `boom` of (boom x). A
  ;; generated line's position is the INNERMOST node that claimed it, so a call is
  ;; reported at the symbol in head position rather than at the paren - line
  ;; accurate, column indicative, which is what a stack frame needs.
  (let [src (io/file @runtime-dir "src")]
    (.mkdirs (io/file src "stackmap"))
    (spit (io/file src "stackmap" "core.cljs")
          (str "(ns stackmap.core)\n\n"
               "(defn boom [x]\n"
               "  (throw (js/Error. (str \"boom \" x))))\n\n"
               "(defn outer [x]\n"
               "  (boom x))\n"))
    (let [opts {:out-dir @runtime-dir :source-paths [(str src)]}
          c    (with-core 'stackmap.repl)
          _    (repl/eval-src c *runtime* "(require '[stackmap.core :as s])" opts)
          r    (first (repl/eval-src c *runtime* "(s/outer 41)" opts))
          fs   (str/split-lines (:stacktrace r))]
      (is (= [:error "Error: boom 41"] [(:status r) (:value r)]))
      (is (= ["    at stackmap.core/boom (stackmap/core.cljs:4:10)"
              "    at stackmap.core/outer (stackmap/core.cljs:7:4)"]
             (take 2 fs))
          (:stacktrace r))
      (testing "and the form that was typed is mapped too, since §5.46"
        ;; column 2 of its one line is the `s/outer` of (s/outer 41) - the same rule
        ;; as above, the innermost node that claimed the generated line
        (is (= 3 (count fs)))
        (is (re-matches #"\s*at eval \(repl/stackmap\.repl/\d+\.cljs:1:2\)" (last fs))
            (last fs)))
      (testing "and node's internals and the runtime's own frames are gone"
        (is (not-any? #(str/includes? % "node:") fs))
        (is (not-any? #(str/includes? % "runtime") fs)))
      (testing "the JavaScript one is kept, because the mapping is the thing you doubt"
        (is (str/includes? (:js-stacktrace r) "ns/stackmap/core.js:"))
        (is (str/includes? (:js-stacktrace r) "Error: boom 41"))))))

(h/deftest-when h/node? test-a-form-typed-at-the-repl-carries-its-own-map
  ;; doc/cljs-repl.md R2's last item (§5.46). A typed form is not on disk, so the
  ;; only copy of its source is the characters the reader consumed - which is why
  ;; clojure.cljs.reader/read-one+text exists and why the map embeds them.
  ;;
  ;; THE FORMS ARE TYPED AFTER OTHERS, in one stream, so the reader's line number is
  ;; well past one by the time the interesting form is read. Everything below is in
  ;; the FORM's coordinates, which is the whole of the arithmetic.
  (let [opts {:out-dir @runtime-dir}
        c    (with-core 'rmap.core)
        _    (repl/eval-src c *runtime*
                            (str "(def a 1)\n(def b 2)\n(def c 3)\n\n"
                                 "(defn boom [x]\n"
                                 "  (throw (js/Error. (str \"b\" x))))\n")
                            opts)
        r    (first (repl/eval-src c *runtime* "(boom 7)" opts))
        frame (first (str/split-lines (:stacktrace r)))
        file  (second (re-find #"\(([^:]+):(\d+):(\d+)\)" frame))
        [_ _ line column] (re-find #"\(([^:]+):(\d+):(\d+)\)" frame)]
    (is (= :error (:status r)))
    (testing "the frame names the input the function was typed in, as ClojureScript"
      (is (re-matches #"repl/rmap\.core/\d+\.cljs" file) frame)
      ;; line 2 of the two-line defn, not line 6 of the stream it arrived in
      (is (= ["2" "10"] [line column]) frame))
    (testing "the map is on disk beside the script, where the script says it is"
      (let [base (subs file 0 (- (count file) (count ".cljs")))
            f    (io/file @runtime-dir (str base ".js.map"))
            m    (sm/decode (slurp f))]
        (is (.isFile f) (str f))
        (is (= [(str base ".cljs")] (:sources m)))
        (testing "and it embeds exactly what was typed, with nothing in front of it"
          (is (= "(defn boom [x]\n  (throw (js/Error. (str \"b\" x))))"
                 (sm/source-text m (str base ".cljs")))))
        (testing "and no position it holds is outside that text"
          (let [n (count (str/split-lines (sm/source-text m (str base ".cljs"))))]
            (is (every? #(<= 1 (:line %) n)
                        (keep #(sm/position m (inc %))
                              (range (count (:lines m))))))))))))

(h/deftest-when h/node? test-a-repl-input-names-its-map-only-when-it-has-one
  ;; the map is written where the script is evaluated from, so a REPL with no
  ;; :out-dir - clojure.cljs.repl/need-out-dir!, a real configuration - compiles
  ;; exactly what it compiled before §5.46: a script with a sourceURL and no map
  (let [c (with-core 'nomap.core)]
    (testing "with nowhere to write one"
      (let [js (repl/compile-form c '(+ 1 1) "(+ 1 1)" nil)]
        (is (str/includes? js "//# sourceURL=repl/nomap.core/"))
        (is (not (str/includes? js "sourceMappingURL")))))
    (testing "with nothing to put in one"
      ;; a form that was built rather than read has no text, which is most of what
      ;; a test does - and every caller of compile-form before this one
      (let [js (repl/compile-form c '(+ 1 1))]
        (is (not (str/includes? js "sourceMappingURL")))))
    (testing "and with both, the name is bare so it resolves against the script's own URL"
      (let [js (repl/compile-form c '(+ 1 1) "(+ 1 1)" {:out-dir @runtime-dir})]
        (is (re-find #"\n//# sourceMappingURL=\d+\.js\.map\n" js) js)))))

(h/deftest-when h/node? test-reload-ships-the-bodies-among-the-targets-and-no-others
  ;; :reload takes the named namespaces' bodies off the tail of what was compiled,
  ;; and how many to take is HOW MANY OF THE TARGETS HAVE A BODY - not how many
  ;; targets there were. A target can compile nothing at all and still be a target:
  ;; a JavaScript module named by a bare symbol (§5.53), or a Closure file on the
  ;; classpath (§5.52). Counting those in reaches one namespace too far down the
  ;; tail and re-runs a dependency nobody asked to reload - here my-lib.core, whose
  ;; source has been edited underneath.
  (with-project*
   two-files
   (fn [{:keys [opts] :as p}]
     ;; the bundler's output, so that requiring the package loads something
     (let [f (io/file (:out-dir opts) "npm/greeter.js")]
       (.mkdirs (.getParentFile f))
       (spit f "export const n = 1;\n"))
     (is (= ["nil" "42"] (vals-in p "(require '[app.core :as a]) (a/use-it)")))
     (edit! p 'my-lib.core
            "(ns my-lib.core) (def helper (fn* ([x] (js* \"~{} * 5\" x))))")
     ;; two targets, one body. app.core's body re-runs; my-lib.core's does not,
     ;; so the answer is still 42 - the same thing :reload means on its own.
     (is (= ["nil" "42"]
            (vals-in p "(require 'app.core '[greeter :as g] :reload) (a/use-it)")))
     ;; and :reload-all still ships the whole graph, which is the contrast
     (is (= ["nil" "105"] (vals-in p "(require 'app.core :reload-all) (a/use-it)"))))))

;; --- errors no turn owns, and callers who give up ---------------------------
;;
;; Two things that look unrelated and share a mechanism: the socket has a reader of
;; its own now (see node-runtime), which is what lets a message arriving while
;; nothing is being evaluated be acted on at once, and what lets a caller stop
;; waiting without leaving a half-read line behind.

(defn- waited-for
  "`program-out` once it contains `s`, or nil after two seconds. Output travels on
  its own thread, so a test that looked once would be asking before the answer."
  [s]
  (loop [n 0]
    (cond (str/includes? (str program-out) s) (str program-out)
          (< 40 n) nil
          :else (do (Thread/sleep 50) (recur (inc n))))))

(h/deftest-when h/node? test-an-error-no-turn-owns-is-reported-and-the-runtime-lives
  ;; The form that scheduled the timer answered long ago, so there is nobody to
  ;; return the throw to: it goes where the runtime's output goes. And the runtime
  ;; is still there afterwards, which under node's own default it would not be -
  ;; an uncaught exception ends the process, and the next form you typed would
  ;; report a broken connection rather than the mistake that broke it.
  (values 'stray.core "(js/setTimeout (fn [] (throw (js/Error. \"a stray throw\"))) 10)")
  (is (waited-for ";; uncaught error: Error: a stray throw") (str program-out))
  (is (= ["7"] (values 'stray.core "(+ 3 4)"))))

(h/deftest-when h/node? test-a-promise-nobody-caught-is-reported-too
  ;; The other half, and it needs its own handler: a rejection is not an exception.
  ;; The promise is created and dropped rather than returned, because a returned one
  ;; is awaited by the turn (§5) and so is caught after all - that one comes back as
  ;; an ordinary error result.
  (values 'stray.core
          "(js* \"(function(){ Promise.reject(new Error('a dropped promise')); return 1; })()\")")
  (is (waited-for ";; uncaught error: Error: a dropped promise") (str program-out)))

(h/deftest-when h/node? test-the-runtime-can-print-while-nothing-is-being-evaluated
  ;; What the socket's own reader bought. The turn that scheduled this ended before
  ;; the timer fired, and nothing is evaluated afterwards: a transport that read
  ;; only inside -evaluate would hold the line until somebody typed again.
  (values 'idle.core "(js/setTimeout (fn [] (js/console.log \"said while idle\")) 200)")
  (is (waited-for "said while idle") (str program-out)))

(h/deftest-when h/node? test-what-the-program-notifies-reaches-who-asked-to-be-told
  ;; The third thing a runtime can do besides answering and printing, and it goes
  ;; to a listener of its own rather than to the output: what it says is for
  ;; whoever asked the runtime to say it - an editor watching an atom.
  (let [out (h/temp-dir)
        heard (promise)]
    (try
      (with-open [rt (repl/node-runtime {:dir out :out program-out
                                         :on-notify #(deliver heard %)})]
        (is (= "true" (:value (repl/evaluate-within
                               rt "(async function(){ return $CLJS.notify('{:changed [3]}'); })()"
                               15000))))
        (is (= "{:changed [3]}" (deref heard 5000 ::nothing)))
        (testing "and none of it is printed"
          (is (not (str/includes? (str program-out) ":changed")))))
      (finally (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-caller-that-gives-up-says-which-way-it-gave-up
  ;; The distinction IJsDeadline exists for, and the two sentences are different
  ;; facts: the first call's script is running in the runtime, the second's never
  ;; got in front of it. Only the first leaves anything behind.
  (let [wedge "(async function(){ const s = Date.now(); while (Date.now() - s < 3000) {} return 111; })()"
        first-r (repl/evaluate-within *runtime* wedge 300)
        busy-r  (repl/evaluate-within *runtime* "(async function(){ return 1; })()" 200)]
    (is (= :error (:status first-r)))
    (is (str/includes? (:value first-r) "did not answer within 300ms") (:value first-r))
    (is (= :error (:status busy-r)))
    (is (str/includes? (:value busy-r) "busy for the whole 200ms") (:value busy-r))
    ;; AND THE ABANDONED ANSWER GOES NOWHERE. It is still coming - nothing can stop
    ;; JavaScript - and the next evaluation must not be handed it: 111 is what the
    ;; wedge returns and 14 is what was asked for.
    (is (= ["14"] (values 'gaveup.core "(+ 7 7)")))))

(h/deftest-when h/node? test-a-bounded-call-that-fits-is-an-ordinary-evaluation
  (is (= {:status :success :value "99"}
         (select-keys (repl/evaluate-within *runtime* "(async function(){ return 99; })()" 15000)
                      [:status :value]))))

(deftest test-a-runtime-that-cannot-be-asked-to-give-up-says-so
  ;; Rather than a JVM-side timer around -evaluate, which would bound the wait and
  ;; not the queue - see evaluate-within.
  (let [rt (reify repl/IJsRuntime (-evaluate [_ _] {:status :success :value "1"}))
        r  (repl/evaluate-within rt "1" 10)]
    (is (= :error (:status r)))
    (is (str/includes? (:value r) "IJsDeadline") (:value r))))

(h/deftest-when h/node? test-a-bounded-broadcast-on-a-single-runtime-is-that-runtime
  ;; Node implements IJsDeadline and NOT IJsRuntimes, and asking it for every
  ;; runtime it has is asking it for itself - which is the reason
  ;; -evaluate-all-within is a method of the deadline protocol rather than of the
  ;; fan-out one. Put the other way round, node would have to answer a refusal to
  ;; a question it can answer perfectly well.
  (is (= {:status :success :value "99"}
         (select-keys (repl/evaluate-all-within *runtime* "(async function(){ return 99; })()" 15000)
                      [:status :value]))))

(deftest test-a-runtime-that-can-spread-a-script-but-not-give-up-is-refused-as-well
  ;; The near miss evaluate-all-within is written against: this runtime CAN reach
  ;; every page, so falling back to broadcast! would look like the obliging thing
  ;; to do - and it would answer an ask that named a bound by ignoring the bound,
  ;; which is how a tooling caller ends up hung behind a page that is asleep.
  (let [rt (reify
             repl/IJsRuntime
             (-evaluate [_ _] {:status :success :value "1"})
             repl/IJsRuntimes
             (-evaluate-all [_ _] {:status :success :value "1"})
             (-pages [_] [])
             (-select-page! [_ _] false))
        r  (repl/evaluate-all-within rt "1" 10)]
    (is (= :error (:status r)))
    (is (str/includes? (:value r) "IJsDeadline") (:value r))))

(deftest test-a-broadcast-form-reaches-every-page-and-an-evaluated-one-only-one
  ;; What a render hook is for: the reload went to every page, so the redraw has
  ;; to as well - while a form typed at the prompt still has one answer.
  (let [sent (atom [])
        rt   (reify
               repl/IJsRuntime
               (-evaluate [_ _] (swap! sent conj :one) {:status :success :value "1"})
               repl/IJsRuntimes
               (-evaluate-all [_ _] (swap! sent conj :all) {:status :success :value "2"})
               (-pages [_] [])
               (-select-page! [_ _] false))]
    (is (= "2" (:value (repl/broadcast-form (cenv 'broadcast.a) rt '(+ 1 2)))))
    (is (= "1" (:value (repl/eval-form (cenv 'broadcast.b) rt '(+ 1 2)))))
    (is (= [:all :one] @sent))))

(deftest test-a-broadcast-form-on-a-single-runtime-is-an-evaluation
  (let [rt (reify repl/IJsRuntime (-evaluate [_ _] {:status :success :value "3"}))]
    (is (= "3" (:value (repl/broadcast-form (cenv 'broadcast.c) rt '(+ 1 2)))))))

;; --- starting on a namespace ------------------------------------------------

(h/deftest-when h/node? test-a-repl-started-on-a-namespace-has-it-loaded
  ;; Replique's (cljs-repl 'my.app), and the half its ensure-compiled could not
  ;; do: the program is in the RUNTIME before the first prompt, so the first
  ;; thing you ask about it answers without a require you had to remember.
  (with-project*
   two-files
   (fn [{:keys [cenv rt opts]}]
     (let [out (StringWriter.)]
       (repl/repl cenv rt (merge opts {:ns 'main.here :main 'app.core
                                       :in (StringReader. "(app.core/use-it)\n")
                                       :out out}))
       ;; nothing above the first prompt: there was no form, so there is no value
       (is (= "main.here=> 42\nmain.here=> \n" (str out)))))))

(h/deftest-when h/node? test-a-main-that-will-not-load-is-said-before-the-first-prompt
  ;; And has to be: a REPL whose :main silently did nothing is one standing in a
  ;; program that is not loaded.
  (with-project*
   two-files
   (fn [{:keys [cenv rt opts]}]
     (let [out (StringWriter.)]
       (repl/repl cenv rt (merge opts {:ns 'main.bad :main 'no.such.program
                                       :in (StringReader. "(+ 1 2)\n")
                                       :out out}))
       (is (str/starts-with? (str out) "error") (str out))
       ;; named as the file it looked for, which is what the compile knows
       (is (str/includes? (str out) "no/such/program.cljs") (str out))
       (is (str/includes? (str out) "main.bad=> 3\n")
           "and the repl is a repl anyway")))))
