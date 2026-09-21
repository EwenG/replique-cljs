;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.cljs.npm-test
  "A string require: (:require [\"react\" :as React]) - doc/cljs-npm.md.

  Three things want checking, and they are independent:

    - the ns form GRAMMAR: what a string spec may say, what it may not, and that
      none of it reaches the namespace machinery a symbol spec drives;
    - RESOLUTION: an alias names the module object, a :refer and a :default name
      exports, and each sits in the right place among the other ways a bare name
      can already mean something;
    - the two PROLOGUES: a module imports what a script awaits, both bind the same
      name, and the file behind it is fetched and called under node."
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.cljs.names :as names]
            [clojure.cljs.output :as output]
            [clojure.cljs.repl :as repl]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]])
  (:import [java.io File]))

(use-fixtures :each h/cursor)

(defn- ns-env
  "A fresh environment holding `ns-form`, positioned in the namespace it declares."
  [ns-form]
  (let [cenv (h/fresh-env 'app.core)]
    (h/analyze cenv ns-form)
    cenv))

(def ^:private program-out
  "Where a node runtime's own output goes, so that a program printing something
  does not print it into the test report."
  (java.io.StringWriter.))

(defn- node
  "Run `f` under node. Its trimmed stdout, or \"THREW: <message>\"."
  [^File f]
  (let [{:keys [out err exit]} (sh/sh "node" (.getPath f))]
    (if (zero? exit) (str/trim out) (str "THREW: " (str/trim err)))))

;; --- the grammar ------------------------------------------------------------

(deftest test-a-string-is-a-module-and-a-symbol-is-a-namespace
  ;; the one place the two worlds are told apart, and the whole of how: a
  ;; namespace name is a symbol everywhere in Clojure, so a string in that
  ;; position can only mean the other thing
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React]
                                             [goog.object :as gobj])))]
    (is (= ["react"] (env/js-requires cenv 'app.core)))
    ;; {alias [specifier path]} - the path is the $ sugar, and nil here
    (is (= '{React ["react" nil]} (env/js-aliases cenv 'app.core)))
    ;; and NOT in the namespace requires, which is the separation the model rests
    ;; on: a module has no Namespace, no vars and no place in the compile graph
    (is (= '#{cljs.core goog.object} (env/requires cenv 'app.core)))
    (is (nil? (env/find-cljs-ns cenv (symbol "react")))))
  ;; a bare string requires the module for its effect and names nothing
  (let [cenv (ns-env '(ns app.core (:require ["a-side-effect"])))]
    (is (= ["a-side-effect"] (env/js-requires cenv 'app.core)))
    (is (= {} (env/js-aliases cenv 'app.core)))
    (is (= {} (env/js-refers cenv 'app.core)))))

(deftest test-the-three-options-are-shadows-three
  (let [cenv (ns-env '(ns app.core
                        (:require ["react" :as React :refer [useState useEffect]]
                                  ["date-fns/sub" :default sub]
                                  ["@visx/scale" :refer [scaleLinear]
                                                 :rename {scaleLinear linear}])))]
    (is (= ["@visx/scale" "date-fns/sub" "react"] (env/js-requires cenv 'app.core)))
    (is (= '{React ["react" nil]} (env/js-aliases cenv 'app.core)))
    ;; {name [specifier export]} - and :default is a :refer of the export called
    ;; `default`, which is what it is in JavaScript too
    (is (= '{useState  ["react" "useState"]
             useEffect ["react" "useEffect"]
             sub       ["date-fns/sub" "default"]
             ;; a rename moves the NAME and leaves the export where it was
             linear    ["@visx/scale" "scaleLinear"]}
           (env/js-refers cenv 'app.core)))))

(deftest test-a-dollar-names-a-path-into-the-module
  ;; shadow-cljs's other spelling of :default, and of a property path besides. The
  ;; three options above apply to whatever the SPECIFIER named, and a specifier is
  ;; free to have named a property rather than the module itself.
  (let [cenv (ns-env '(ns app.core
                        (:require ["date-fns/sub$default" :as sub]
                                  ;; the same module, once with a path and once
                                  ;; without - and ONE import between them, because
                                  ;; the path is no part of any file name
                                  ["date-fns/sub" :as whole]
                                  ["a$b.c" :refer [d] :default e])))]
    (is (= ["a" "date-fns/sub"] (env/js-requires cenv 'app.core)))
    (is (= '{sub   ["date-fns/sub" "default"]
             whole ["date-fns/sub" nil]}
           (env/js-aliases cenv 'app.core)))
    ;; and every option reads from where the $ pointed, :default included
    (is (= '{d ["a" "b.c.d"] e ["a" "b.c.default"]}
           (env/js-refers cenv 'app.core)))))

(deftest test-the-split-is-at-the-first-dollar
  ;; shadow-cljs's rule (a split with a limit of 2) rather than ClojureScript's,
  ;; whose lib&sublib regex is greedy and takes the LAST. The two agree on every
  ;; specifier with one $ in it and disagree on a$b$c, where the second $ can only
  ;; be part of the property name: $ is legal in a JavaScript name and not in a
  ;; package name, so the first one is the one that can be the delimiter.
  (let [cenv (ns-env '(ns app.core (:require ["a$b$c" :as x])))]
    (is (= ["a"] (env/js-requires cenv 'app.core)))
    (is (= '{x ["a" "b$c"]} (env/js-aliases cenv 'app.core)))))

(deftest test-what-a-string-spec-refuses
  ;; each of these means nothing rather than being unsupported, and the message
  ;; says which thing it would have meant
  (are [form re] (re-find re (or (h/message #(h/analyze (h/fresh-env 'app.core) form))
                                 ""))
    '(ns app.core (:use ["react" :only [x]]))          #"Cannot :use"
    '(ns app.core (:require ["react" :as-alias R]))    #"Cannot :as-alias"
    '(ns app.core (:require ["react" :include-macros true])) #"Unsupported option"
    '(ns app.core (:require ["react" :refer-macros [x]]))    #"Unsupported option"
    '(ns app.core (:require ["react" :refer "useState"]))    #":refer takes a vector"
    '(ns app.core (:require ["react" :rename {a b}]))        #":rename names a"
    ;; and the specifier itself, checked where the ns form is read rather than at
    ;; emission - by the very function that turns it into a file
    '(ns app.core (:require ["./beside.js" :as b]))    #"names a path rather than a package"
    '(ns app.core (:require ["" :as b]))               #"empty name"
    ;; an export that could not be a property of anything
    '(ns app.core (:require ["react" :refer [a.b]]))   #"not a name there"
    ;; and the $ sugar's half of the same question
    '(ns app.core (:require ["a$" :as x]))             #"nothing after it"
    '(ns app.core (:require ["$b" :as x]))             #"no module before it"
    '(ns app.core (:require ["a$b..c" :as x]))         #"not a name in JavaScript"
    ;; NOT munged, where a :refer of the symbol b-c would be: a specifier is a
    ;; string, and a string in an ns form is the host's spelling throughout
    '(ns app.core (:require ["a$b-c" :as x]))          #"spelled the way JavaScript"))

(deftest test-one-name-cannot-mean-two-things
  ;; a Namespace refuses a second target for an alias it holds, and cannot see a
  ;; module's - so both directions are asked, and neither is silent
  (is (re-find #"already names a JavaScript module"
               (h/message #(h/analyze (h/fresh-env 'app.core)
                                      '(ns app.core (:require ["react" :as R]
                                                              [app.other :as R]))))))
  (is (re-find #"already names a namespace"
               (h/message #(h/analyze (h/fresh-env 'app.core)
                                      '(ns app.core (:require [app.other :as R]
                                                              ["react" :as R])))))))

(deftest test-a-module-is-not-a-dependency
  ;; what the driver asks before it can analyse a file. A specifier in here would
  ;; send it looking for react.cljs on the source path - which is goog's reason,
  ;; one world over
  (is (= '[app.other]
         (ana/ns-form-deps '(ns app.core (:require ["react" :as R]
                                                   ["@visx/scale" :refer [x]]
                                                   [goog.object :as gobj]
                                                   [app.other :as o]))))))

(deftest test-a-declaration-replaces
  ;; an ns form declares rather than accumulates, so deleting a string require
  ;; from a file has to take the import out of the module - the same rule
  ;; clear-ns-declaration! applies to every other thing an ns form establishes
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React])))]
    (is (= ["react"] (env/js-requires cenv 'app.core)))
    (h/analyze cenv '(ns app.core (:require ["preact" :as React])))
    (is (= ["preact"] (env/js-requires cenv 'app.core)))
    (is (= '{React ["preact" nil]} (env/js-aliases cenv 'app.core)))))

(deftest test-a-repl-require-adds-one
  ;; (require '["react" :as React]) typed at a REPL: the same planning, adding to
  ;; what the namespace has rather than replacing it
  (let [cenv (ns-env '(ns app.core (:require ["preact" :as P])))]
    (ana/require-libs! cenv '[["react" :as React :refer [useState]]])
    (is (= ["preact" "react"] (env/js-requires cenv 'app.core)))
    (is (= '{P ["preact" nil] React ["react" nil]} (env/js-aliases cenv 'app.core)))))

;; --- resolution -------------------------------------------------------------

(defn- emitted
  "The JavaScript one form compiles to in `cenv`, as an expression."
  [cenv form]
  (names/with-name-scope
    (str (emitter/emit-top (h/analyze cenv form) identity))))

(deftest test-an-alias-names-the-module-object
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React])))]
    ;; the module itself is a value - a program passing one along has written
    ;; exactly that
    (is (= "react$js" (emitted cenv 'React)))
    ;; an export of it, read and called. Called as a METHOD, keeping the receiver:
    ;; a package bundled from CommonJS is a rewritten object literal, and a
    ;; function on it may well read `this`
    (is (= "react$js.createElement" (emitted cenv 'React/createElement)))
    (is (= "react$js.createElement(\"div\")"
           (emitted cenv '(React/createElement "div"))))
    ;; a dot in the NAME half splits a value from its properties, as it does for a
    ;; namespace: there is no export called Children.map
    (is (= "react$js.Children.map" (emitted cenv 'React/Children.map)))
    ;; and the export is spelled the HOST's way, because the name is JavaScript's
    (is (= "react$js.some_fn" (emitted cenv 'React/some-fn)))))

(deftest test-a-dollar-alias-names-what-the-path-points-at
  (let [cenv (ns-env '(ns app.core (:require ["date-fns/sub$default" :as sub]
                                             ["lib$a.b" :as deep])))]
    ;; the value the path points at - which is what every one of the 33 such
    ;; requires in one real application is for, a $default read and then called
    (is (= "date_fns$SLASH$sub$js.default" (emitted cenv 'sub)))
    (is (= "date_fns$SLASH$sub$js.default(\"x\")" (emitted cenv '(sub "x"))))
    ;; and it is a place to read names out of besides, so the alias goes on being
    ;; an alias: the path only moves where the reading starts
    (is (= "date_fns$SLASH$sub$js.default.foo" (emitted cenv 'sub/foo)))
    (is (= "lib$js.a.b.c" (emitted cenv 'deep/c)))
    ;; a dot in the NAME half still splits a value from its properties
    (is (= "lib$js.a.b.c.d" (emitted cenv 'deep/c.d)))))

(deftest test-a-refer-is-a-bare-name
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React
                                              :refer [useState]]
                                             ["lib" :default plain])))]
    (is (= "react$js.useState" (emitted cenv 'useState)))
    ;; :default is the export called `default`, which is a reserved word and a
    ;; perfectly good property name
    (is (= "lib$js.default" (emitted cenv 'plain)))
    ;; one module, one binding: the :as and the :refer are two names for things
    ;; reached through the same object
    (is (= ["lib" "react"] (env/js-requires cenv 'app.core)))))

(deftest test-a-js-refer-sits-where-a-refer-sits
  ;; below anything this namespace defines, and ABOVE the implicit refer of
  ;; cljs.core. Without the second half a :refer of a name core also has would
  ;; silently resolve to core's.
  (let [cenv (h/core-env 'app.refers)]
    (h/analyze cenv '(ns app.refers (:require ["lib" :refer [count take]])))
    (is (= "lib$js.count" (emitted cenv 'count)))
    (is (= "lib$js.take" (emitted cenv 'take)))
    ;; a def of the same name in this namespace wins, exactly as it wins over a
    ;; :refer of a var
    (h/analyze cenv '(def count 1))
    (is (= "app$refers$ns.count" (emitted cenv 'count)))))

(deftest test-an-alias-is-not-a-namespace
  ;; the aliased name is a module, so ::React/foo and a require of it are not
  ;; things - what IS a thing is every reading above, and nothing else changed
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React])))]
    (is (nil? (env/resolve-ns cenv 'React)))
    (is (empty? (.getAliases ^clojure.lang.Namespace (env/cljs-ns cenv 'app.core))))))

;; --- the two prologues ------------------------------------------------------

(deftest test-a-module-imports-what-a-script-awaits
  ;; doc/cljs-repl.md §4: one body, two prologues, and they have to bind the same
  ;; name or the body between them is not the same text
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React]
                                             ["@visx/scale" :refer [scaleLinear]])))]
    (is (= ["import * as $CIRCA$visx$SLASH$scale$js from \"../../npm/@visx/scale.js\";"
            "import * as react$js from \"../../npm/react.js\";"]
           (mapv #(emitter/js-import (names/js-alias %)
                                     (output/specifier 'app.core (output/js->path %)))
                 (env/js-requires cenv 'app.core))))
    (let [script (emitter/script-prologue 'app.core '#{cljs.core}
                                          (env/js-requires cenv 'app.core))]
      ;; one line per specifier either way, which is what keeps a body at the same
      ;; line number in the module and in the script that reloads it
      (is (= 2 (count (filter #(str/includes? % "requireJs") script))))
      (is (some #{"const react$js = await $CLJS.requireJs(\"react\");"} script)))))

(deftest test-a-module-is-imported-once-however-many-names-it-gave
  ;; :as and :refer of one specifier are one import, because both are properties
  ;; of the one object it binds
  (let [cenv (ns-env '(ns app.core
                        (:require ["react" :as React :refer [useState]]
                                  ["react" :refer [useEffect]])))]
    (is (= ["react"] (env/js-requires cenv 'app.core)))))

;; --- end to end -------------------------------------------------------------

(def ^:private npm-tree
  "The npm/ tree a bundler would build, as {path source}. Written by hand here,
  which is the point: this compiler does not build it and must not need to - what
  it owns is the NAME each specifier is filed under."
  {"npm/greeter.js"      (str "export function hello(x) { return \"hello \" + x; }\n"
                              "export function shout(x) { return x.toUpperCase(); }\n")
   "npm/greeter/loud.js" "export default function (x) { return x + \"!\"; }\n"
   "npm/@scope/pkg.js"   "export const answer = 42;\n"})

(defn- write-npm!
  [^File dir]
  (doseq [[path src] npm-tree]
    (let [f (io/file dir path)]
      (.mkdirs (.getParentFile f))
      (spit f src))))

(h/deftest-when h/node? test-one-body-runs-both-ways
  ;; doc/cljs-repl.md §4 as an experiment rather than an argument: the same source,
  ;; compiled once as a module and once as a script, gives the same answer. The
  ;; module reaches the package by a relative import and the script by
  ;; $CLJS.requireJs, and nothing between them differs.
  (h/write-npm! {"pkg" "export const n = 7;\nexport default function (x) { return x * 2; }\n"})
  (let [src "(ns app.both (:require [\"pkg\" :as p :refer [n] :default twice]))
             (str (twice n) \"-\" p.n)"]
    ;; core-env rather than fresh-env: str is a cljs.core var, and the two paths
    ;; are being compared rather than cljs.core's absence
    (is (= "14-7" (h/output (h/core-env 'app.both) src)))
    (is (= "14-7" (h/script-output (h/core-env 'app.both2) src)))))

(deftest test-an-export-cannot-be-assigned
  ;; not a rule of this compiler's: an ES module's exports are read-only bindings
  ;; where they are imported, so the assignment would be a TypeError in the host
  (let [cenv (ns-env '(ns app.core (:require ["react" :as React])))]
    (is (re-find #"read-only"
                 (h/message #(h/analyze cenv '(set! React/foo 1)))))))

(h/deftest-when h/node? test-a-module-fetches-its-packages-and-calls-them
  ;; Through every piece at once, on the module path: a namespace requiring three
  ;; specifiers with all three options, compiled by the driver, imported by node.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core
                             (:require [\"greeter\" :as g :refer [shout]]
                                       [\"greeter/loud\" :default loud]
                                       [\"greeter/loud$default\" :as loud2]
                                       [\"@scope/pkg\" :refer [answer]]))
                           (defn run []
                             (str (g/hello \"a\") \"|\" (shout \"b\") \"|\"
                                  (loud \"c\") \"|\" (loud2 \"d\") \"|\" answer))"})
        out (h/temp-dir)]
    (try
      (let [cenv   (env/compile-env {:ns 'cljs.user})
            ;; under h/warnings because npm/ is written BELOW, after the compile
            ;; that reports what has to go in it - which is the real order, and
            ;; the warning it produces is the next test's subject rather than this
            ;; one's
            box    (atom nil)
            _      (h/warnings
                    #(reset! box (driver/compile-namespace!
                                  cenv 'probe.core
                                  {:out-dir out :source-paths [src]})))
            result @box
            entry  (io/file out "check.mjs")]
        ;; what a bundler has to build, reported rather than acted on - and THREE
        ;; of them for four specs, because the $ spelling and the :default one name
        ;; the same module and share its one import
        (is (= ["@scope/pkg" "greeter" "greeter/loud"] (:js-requires result)))
        ;; and nothing was looked for on the source path: a specifier is not a
        ;; namespace, so the graph the driver walked holds only these two
        (is (= '[cljs.core probe.core] (:compiled result)))
        (write-npm! out)
        (spit entry (str "import { ns as $ns } from \"./runtime.js\";\n"
                         "import \"./ns/probe/core.js\";\n"
                         "console.log($ns(\"probe.core\").run());\n"))
        (is (= "hello a|B|c!|d!|42" (node entry))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-the-script-path-fetches-them-too
  ;; The same three options through the REPL's path, where an import declaration
  ;; is not allowed at all: $CLJS.requireJs returns the module namespace object
  ;; that `import * as` would have bound, and the body is identical.
  (let [out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})]
        (env/with-current-ns 'cljs.user
          (driver/compile-namespace! cenv 'cljs.core {:out-dir out})
          (write-npm! out)
          (let [scripts [(repl/compile-form
                          cenv '(ns app.core (:require ["greeter" :as g
                                                        :refer [shout]]
                                                       ["greeter/loud"
                                                        :default loud])))
                         (repl/compile-form
                          cenv '(str (g/hello "a") "|" (shout "b") "|" (loud "c")))]
                drive  (io/file out "drive.mjs")]
            (spit drive (str "import \"./runtime.js\";\n"
                             (str/join
                              "" (map #(str "console.log(await $CLJS.evaluate("
                                            (pr-str %) "));\n")
                                      scripts))))
            (is (= ["{:status :success :value \"nil\"}"
                    "{:status :success :value \"\\\"hello a|B|c!\\\"\"}"]
                   (str/split-lines (node drive)))))))
      (finally (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-repl-session-requires-a-package
  ;; (require '["greeter" :as g]) typed at a real REPL, against a real node
  ;; runtime. The require itself ships nothing - there is no namespace to fetch and
  ;; nothing for the runtime to decide - and the NEXT form's prologue awaits the
  ;; module, which is the whole of how a string require reaches a running program.
  (let [src (h/write-sources! '{app.core "(ns app.core) (def n 1)"})
        out (h/temp-dir)]
    (try
      (with-open [rt (repl/node-runtime {:dir out :out program-out})]
        (let [cenv (env/compile-env {:ns 'cljs.user})
              opts {:out-dir out :source-paths [src]}]
          ;; the bundler's output, put there while the session is running: nothing
          ;; on the JVM side had to exist before the ns form named it
          (write-npm! out)
          ;; three inputs: the require, a name reached through the alias, and one
          ;; the same spec referred. No cljs.core in this session and none needed -
          ;; a string require compiles nothing at all
          (is (= ["nil" "nil" "\"hello a\"" "\"B\""]
                 (mapv :value
                       (repl/eval-src
                        cenv rt
                        ;; one ordinary require first, which is what puts
                        ;; cljs.core on disk for the prologue to fetch
                        "(require 'app.core)
                         (require '[\"greeter\" :as g :refer [shout]])
                         (g/hello \"a\")
                         (shout \"b\")"
                        opts))))
          ;; AND THE OTHER HALF OF THE REPORT, which only a session reaches. A
          ;; string require compiles nothing, so the driver never runs for one -
          ;; these are the two places that can say a package is not there while
          ;; the user is still looking at what they typed.
          (is (str/includes?
               (h/warnings
                #(repl/eval-src cenv rt "(require '[\"nope\" :as n])" opts))
               "npm/nope.js"))
          (is (str/includes?
               (h/warnings
                #(repl/eval-src cenv rt "(ns app.other (:require [\"nope2\" :as n]))"
                                opts))
               "npm/nope2.js"))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(deftest test-the-report-says-what-the-bundler-still-owes
  ;; The one question about npm/ this compiler can answer: not whether a package
  ;; exists - that is the bundler's resolution to do - but whether the file we
  ;; NAMED is on disk. On a first build into a fresh directory the answer is all of
  ;; them, because this run is what produced the list.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core (:require [\"greeter\" :as g]
                                                    [\"@scope/pkg\" :as p]))
                           (defn run [] [g/hello p/answer])"})
        out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})
            box  (atom nil)
            said (h/warnings
                  #(reset! box (driver/compile-namespace!
                                cenv 'probe.core
                                {:out-dir out :source-paths [src]})))]
        (is (= ["@scope/pkg" "greeter"] (:js-missing @box)))
        ;; the specifier AND the path it will be looked for at, because the second
        ;; is what the bundler has to be told and it is not the first
        (is (str/includes? said "npm/greeter.js"))
        (is (str/includes? said "npm/@scope/pkg.js"))
        ;; now the bundler runs, and the same compile says nothing is owed
        (write-npm! out)
        (spit (io/file out (output/js->path "@scope/pkg")) "export const answer = 1;\n")
        (let [again (h/warnings
                     #(reset! box (driver/compile-namespace!
                                   cenv 'probe.core
                                   {:out-dir out :source-paths [src]})))]
          (is (= [] (:js-missing @box)))
          (is (= "" again))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(deftest test-a-missing-module-is-named-once
  ;; A REPL evaluating form after form in a namespace whose package is not there
  ;; should be told once, not once a form - so the report remembers what it has
  ;; said about a directory.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core (:require [\"greeter\" :as g]))
                           (defn run [] g/hello)"})
        out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})
            opts {:out-dir out :source-paths [src]}
            once (h/warnings #(driver/compile-namespace! cenv 'probe.core opts))
            twice (h/warnings #(driver/compile-namespace! cenv 'probe.core opts))]
        (is (str/includes? once "greeter"))
        (is (= "" twice))
        ;; the ANSWER is still the answer, though - only the warning is once
        (is (= ["greeter"] (output/missing-js out ["greeter"]))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-package-that-is-not-there
  ;; The one thing this compiler cannot check: npm/ is built by a bundler, and a
  ;; specifier nothing built is a 404 at load rather than an error at compile
  ;; time. It has to be a good 404 - the name it could not find, not a line of
  ;; emitted code - so this pins what the failure actually looks like.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core (:require [\"nowhere\" :as n]))
                           (defn run [] (n/f))"})
        out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})
            box  (atom nil)
            said (h/warnings
                  #(reset! box (driver/compile-namespace!
                                cenv 'probe.core
                                {:out-dir out :source-paths [src]})))]
        ;; it COMPILES: the bundle is built from this list, so refusing to compile
        ;; until the bundle exists would be a cycle with no way in
        (is (= ["nowhere"] (:js-requires @box)))
        ;; and it says so on the way out, naming the path it will look for - which
        ;; is what the 404 below is worth avoiding
        (is (= ["nowhere"] (:js-missing @box)))
        (is (str/includes? said "npm/nowhere.js"))
        (spit (io/file out "check.mjs")
              "import \"./ns/probe/core.js\";\nconsole.log(\"ran\");\n")
        (let [said (node (io/file out "check.mjs"))]
          (is (str/includes? said "THREW"))
          (is (str/includes? said "npm/nowhere.js"))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

;; --- shadow's other spelling: a package named by a bare symbol ----------------
;;
;; doc/cljs-compiler.md §5.53. (:require [react :as React]) is what a project
;; written against shadow-cljs says where upstream says ["react" :as React], and
;; nosco-gamma says both in ONE ns form. The symbol spelling is REWRITTEN into the
;; string one at plan-require, so everything above this line is what is being
;; tested a second time here - which is the point of doing it that way.

(deftest test-a-bare-symbol-can-name-a-package
  (let [cenv (ns-env '(ns app.core (:require [react :as React]
                                             [clipboard-polyfill]
                                             [app.other :as o])))]
    (is (= ["clipboard-polyfill" "react"] (env/js-requires cenv 'app.core)))
    ;; THE SYMBOL IS ITSELF A NAME FOR THE MODULE, as a namespace's own name always
    ;; is - so clipboard-polyfill/write resolves with no :as asked for at all, and
    ;; react/createElement resolves beside React/createElement
    (is (= '{React             ["react" nil]
             react             ["react" nil]
             clipboard-polyfill ["clipboard-polyfill" nil]}
           (env/js-aliases cenv 'app.core)))
    ;; and none of them is a namespace, which is the separation the model rests on
    (is (= '#{cljs.core app.other} (env/requires cenv 'app.core)))
    (is (nil? (env/find-cljs-ns cenv 'react)))))

(deftest test-one-name-for-the-module-when-as-asks-for-that-name
  ;; :as react on the symbol react is one name, not two, and not refused as a
  ;; collision with itself.
  ;;
  ;; A GUARD WITH NO DEFEAT BEHIND IT. The two names are recorded into a map under
  ;; the same key, so nothing this compiler does could make it come out otherwise -
  ;; which is why plan-require no longer has a branch for it.
  (let [cenv (ns-env '(ns app.core (:require [react :as react])))]
    (is (= '{react ["react" nil]} (env/js-aliases cenv 'app.core)))))

(deftest test-a-symbol-module-takes-the-same-options
  ;; the same three, because it is the same function underneath
  (let [cenv (ns-env '(ns app.core
                        (:require [react :refer [useState useEffect]
                                   :rename {useEffect effect}]
                                  [preact :default p])))]
    (is (= ["preact" "react"] (env/js-requires cenv 'app.core)))
    (is (= '{useState ["react" "useState"]
             effect   ["react" "useEffect"]
             p        ["preact" "default"]}
           (env/js-refers cenv 'app.core)))))

(deftest test-a-dot-is-the-answer-no
  ;; The whole of what keeps `Could not locate` as the error for a namespace that
  ;; is missing. A dot is what a namespace name is made of; a package whose name
  ;; has one can always be written as a string instead.
  (are [sym expected] (= expected (output/symbol-specifier sym))
    'react              "react"
    'clipboard-polyfill "clipboard-polyfill"
    'prosemirror-state  "prosemirror-state"
    'app.core           nil
    'cljs.core          nil
    ;; a real package name, and the string spelling is how it is written here
    'sse.js             nil
    ;; not a simple symbol, so not a bare name at all
    'x/y                nil
    ;; the $ sugar is a string's, and js->path refuses it - one function decides
    ;; what a specifier may be, however it was spelled
    'foo$bar            nil)
  ;; and a dotted name is a namespace to the driver, whatever is or is not behind it
  (is (= '[a.b] (ana/ns-form-deps '(ns app.core (:require [a.b :as b]))))))

(deftest test-a-symbol-module-is-a-dependency-and-a-string-is-not
  ;; The one place the two spellings differ, and it is not an oversight. A STRING
  ;; can never be a namespace, so ns-form-deps can drop it knowing nothing else. A
  ;; SYMBOL might be - a one-segment name is a legal namespace - and what decides
  ;; is whether a source exists, which is a fact about the driver's source paths
  ;; and not about the form. So it is handed over and the driver settles it
  ;; (driver/ensure!), which is exactly what makes a source win.
  ;; in the order written, which is what ns-form-deps promises
  (is (= '[react app.other]
         (ana/ns-form-deps '(ns app.core (:require ["preact" :as P]
                                                   [react :as R]
                                                   [goog.object :as gobj]
                                                   [app.other :as o]))))))

(h/deftest-when h/node? test-a-source-beats-a-package-of-the-same-name
  ;; A one-segment name is a legal namespace, so the package reading is the LAST
  ;; answer and not the first. util.cljs is on the source path and `util` means it.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{util     "(ns util) (def origin \"clojurescript\")"
               app.core "(ns app.core (:require [util :as u :refer [origin]]))
                         (js* \"console.log(~{})\" u/origin)
                         (js* \"console.log(~{})\" origin)"})
        out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})
            res  (driver/compile-namespace! cenv 'app.core
                                            {:out-dir out :source-paths [src]})]
        (is (= '[cljs.core util app.core] (:compiled res)))
        ;; nothing was reported to the bundler, because nothing named a package
        (is (= [] (:js-requires res)))
        (is (= "clojurescript\nclojurescript" (node (File. out "ns/app/core.js")))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-closure-file-beats-a-package-of-the-same-name
  ;; And so does the other kind of file. widgetjs.js is a Closure provide on the
  ;; classpath (§5.52); a file that is actually there beats a package that may or
  ;; may not be in somebody's node_modules.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{app.core "(ns app.core (:require [widgetjs :as w]))
                         (js* \"console.log(~{})\" w/origin)"})
        out (h/temp-dir)]
    (try
      (let [cenv (env/compile-env {:ns 'cljs.user})
            res  (driver/compile-namespace! cenv 'app.core
                                            {:out-dir out :source-paths [src]})]
        (is (= [] (:js-requires res)))
        (is (.isFile (File. out "ns/widgetjs.js")))
        (is (= "closure" (node (File. out "ns/app/core.js")))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-symbol-module-fetches-its-package-and-calls-it
  ;; Through every piece at once, the way the string spelling is tested above: a
  ;; namespace whose ns form names packages by bare symbols, compiled by the
  ;; driver, imported by node and called.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core
                             (:require [greeter :as g :refer [shout]]
                                       [clipboard-polyfill]))
                           (js* \"console.log(~{})\" (g/hello \"a\"))
                           (js* \"console.log(~{})\" (shout \"b\"))
                           (js* \"console.log(~{})\" (clipboard-polyfill/write \"c\"))"})
        out (h/temp-dir)]
    (try
      ;; the bundler's output first, so the run has nothing to report as owed
      (doseq [[path text] {"npm/greeter.js"
                           (str "export function hello(x) { return \"hello \" + x; }\n"
                                "export function shout(x) { return x.toUpperCase(); }\n")
                           "npm/clipboard-polyfill.js"
                           "export function write(x) { return \"wrote \" + x; }\n"}]
        (let [f (io/file out path)]
          (.mkdirs (.getParentFile f))
          (spit f text)))
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'probe.core
                                 {:out-dir out :source-paths [src]})
      ;; ONE import per specifier, whichever way it was spelled
      (let [text (slurp (File. out "ns/probe/core.js"))]
        (is (str/includes? text "import * as greeter$js from \"../../npm/greeter.js\""))
        (is (str/includes? text
                           "import * as clipboard_polyfill$js from \"../../npm/clipboard-polyfill.js\"")))
      (is (= "hello a\nB\nwrote c" (node (File. out "ns/probe/core.js"))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-a-repl-require-of-a-symbol-package-fetches-it
  ;; (require '[greeter :as g]) typed at a real REPL. What is shipped is
  ;; $CLJS.requireJs and not $CLJS.require - the second would compute ./ns/greeter.js
  ;; and 404 - and the next form reaches the module through its own prologue.
  (let [src (h/write-sources! '{app.core "(ns app.core) (def n 1)"})
        out (h/temp-dir)]
    (try
      (with-open [rt (repl/node-runtime {:dir out :out program-out})]
        (let [cenv (env/compile-env {:ns 'cljs.user})
              opts {:out-dir out :source-paths [src]}]
          (write-npm! out)
          (is (= ["nil" "nil" "\"hello a\"" "\"B\""]
                 (mapv :value
                       (repl/eval-src
                        cenv rt
                        "(require 'app.core)
                         (require '[greeter :as g :refer [shout]])
                         (g/hello \"a\")
                         (shout \"b\")"
                        opts))))
          ;; and the report reaches a session typing the symbol spelling too
          (is (str/includes?
               (h/warnings
                #(repl/eval-src cenv rt "(require '[nope3 :as n])" opts))
               "npm/nope3.js"))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))
