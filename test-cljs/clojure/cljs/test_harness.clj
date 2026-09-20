;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Shared machinery for the ClojureScript front end's tests.

  Two prerequisites, neither needed to build Clojure itself, so both are optional
  and a missing one skips the tests that want it rather than failing them:

    node                  to run emitted JavaScript (clojure.cljs.emitter-test)
    the ClojureScript jar to analyse the same form with cljs.analyzer and diff the
                          two ASTs (clojure.cljs.oracle-test)

  Run everything with `mvn -o test`, which puts ClojureScript on the test
  classpath; see doc/cljs-compiler.md §6."}
  clojure.cljs.test-harness
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.names :as names]
            [clojure.cljs.output :as output]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.repl :as repl]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [deftest]])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; --- prerequisites ----------------------------------------------------------

(def node?
  "Is there a node on PATH to run emitted JavaScript with?"
  (try (zero? (:exit (sh/sh "node" "--version")))
       (catch Exception _ false)))

(def cljs-analyzer?
  "Is ClojureScript on the classpath, so cljs.analyzer can be the AST oracle?

  Note which cljs.core this loads since M5: OURS. src/clj/cljs/core.cljc shadows
  the jar's (doc/cljs-compiler.md §5.6), so when cljs.analyzer expands a macro
  during an oracle comparison it now expands it the same way we do. That narrows
  the diff to analysis, which is what the oracle is for - but it does mean an
  oracle test can no longer pin an expansion ClojureScript's core.cljc produces
  and ours does not."
  (try (require 'cljs.core)      ; get-expander* NPEs without it - see the doc
       (require 'cljs.analyzer)
       (require 'cljs.env)
       true
       (catch Throwable _ false)))

(defmacro deftest-when
  "clojure.test/deftest, but the test is defined only when `pred` holds at load
  time. A missing prerequisite skips these tests; it never fails them."
  [pred nm & body]
  `(when ~pred (deftest ~nm ~@body)))

;; --- a program on disk ------------------------------------------------------

(defn temp-dir
  "A temporary directory, removed when the JVM exits if a test forgets to."
  ^File []
  (doto (.toFile (Files/createTempDirectory "cljs" (into-array FileAttribute [])))
    (.deleteOnExit)))

(defn delete-tree!
  [^File f]
  (run! #(.delete ^File %) (reverse (file-seq f))))

(defn write-sources!
  "`sources` is {namespace source}, written at the munged path the driver looks at -
  so a test does not restate the rule it is testing."
  ([sources] (write-sources! (temp-dir) sources))
  ([^File dir sources]
   (doseq [[ns-sym src] sources]
     (let [f (io/file dir (driver/ns->source-path ns-sym ".cljs"))]
       (.mkdirs (.getParentFile f))
       (spit f src)))
   dir))

;; --- compiling --------------------------------------------------------------

(defn cursor
  "A clojure.test fixture giving each test a cursor of its own:

    (use-fixtures :each h/cursor)

  clojure.cljs.env/*current-ns* is a dynamic var, so moving it - which fresh-env,
  core-env, an (ns ...) form and in-ns all do - is a set!, and a set! needs a
  binding to move. Every test namespace that compiles anything wants this; the
  production entry points (driver/compile!, repl/repl) establish their own.

  Per test rather than per namespace, so a test that ends somewhere unexpected
  cannot hand that to the next one."
  [f]
  (env/with-current-ns env/*current-ns* (f)))

(defn fresh-env
  "A compile environment of its own, so tests cannot see each other's defs.

  Positions the cursor too, which is a set! - so this needs the `cursor` fixture."
  ([] (fresh-env 'app.core))
  ([ns-sym] (env/compile-env {:ns ns-sym})))

(defn analyze
  "The AST of one form, in a fresh environment unless one is given."
  ([form] (analyze (fresh-env) form))
  ([cenv form] (ana/analyze-top cenv (env/analysis-env cenv) form)))

(defn js
  "ClojureScript source `src` (any number of top-level forms) as one JavaScript
  program. The last form's value is passed to console.log, which is how a test
  observes it."
  ([src] (js (fresh-env) src))
  ([cenv src]
   ;; ONE name scope around every form: they all land in one JavaScript scope, so
   ;; two forms binding the same local must not both emit `let x__1`.
   (names/with-name-scope
     (let [aenv  (env/analysis-env cenv)
           forms (reader/read-forms cenv src)
           top   (fn [form] (ana/analyze-top cenv aenv form))
           ;; analysed before the prologue is asked for: an (ns ...) among these
           ;; forms moves the cursor, and the prologue names what the body names
           body  (conj (mapv #(emitter/emit-top (top %)) (butlast forms))
                       (emitter/emit-top (top (last forms))
                                         #(str "console.log(" % ");")))
           nsym  env/*current-ns*]
       (str/join "\n" (into (emitter/ns-prologue nsym (env/requires cenv nsym))
                            body))))))

(defn script
  "The same source as the unit a REPL evaluates (doc/cljs-repl.md \u00a75): one async
  IIFE, whose value is the last form's.

  Where `js` builds a module and observes through console.log, this returns the
  value the way the REPL will - so the two differ in the destination of the last
  form, and in nothing else."
  ([src] (script (fresh-env) src))
  ([cenv src]
   (names/with-name-scope
     (let [aenv  (env/analysis-env cenv)
           forms (reader/read-forms cenv src)
           top   (fn [form] (ana/analyze-top cenv aenv form))
           head  (into [] (mapcat #(emitter/emit-top-lines (top %))) (butlast forms))
           tail  (emitter/emit-top-lines (top (last forms)) emitter/return-value)
           nsym  env/*current-ns*]
       (emitter/script
        (into (emitter/script-prologue nsym (env/requires cenv nsym))
              (into head tail)))))))

;; --- running ----------------------------------------------------------------

(def ^:private error-line #"^[A-Za-z]*Error: (.*)$")

(def ^:private runtime-dir
  "A directory holding runtime.js, plus the package.json that makes node read a
  .js file in it as an ES module rather than as CommonJS. Built once and reused:
  it is the same two files every time, and a compiled program is only ever run
  beside them.

  This is the shape an output directory has - modules importing runtime.js by a
  relative path - so the tests exercise the import M3 will emit, not a copy of the
  runtime pasted into each program. Written by clojure.cljs.repl/write-runtime!,
  which is what a REPL runs a runtime beside, so there is one description of that
  directory rather than two that can drift."
  (delay
    (let [d (.toFile (Files/createTempDirectory "cljs-runtime" (into-array FileAttribute [])))]
      (.deleteOnExit d)
      (repl/write-runtime! d)
      (run! #(.deleteOnExit ^File %) (.listFiles d))
      d)))

(defn- node
  "Run `f` under node. Its trimmed stdout, or \"THREW: <message>\" if it threw."
  [^File f]
  (let [{:keys [out err exit]} (sh/sh "node" (.getPath f))]
    (if (zero? exit)
      (str/trim out)
      (str "THREW: " (or (first (keep #(second (re-matches error-line %))
                                      (str/split-lines err)))
                         (str/trim err))))))

(declare core-module)

(defn run-js
  "Run a JavaScript program under node as a module, beside the runtime it imports -
  the shape a compiled namespace has on disk.

  cljs.core is on disk beside it, because since §5.12 every compiled module opens
  with an import of it - so there is no longer a configuration in which emitted code
  runs without it, and a test that pretended otherwise would be testing a shape the
  compiler no longer emits."
  [program]
  (let [_ @core-module
        f (File/createTempFile "cljs" ".js" @runtime-dir)]
    (try
      (spit f (str (emitter/runtime-import "./runtime.js") "\n"
                   ;; the import a real module opens with, spelled here because
                   ;; `program` is a BODY - driver/module-text is what puts the
                   ;; imports on a module, and these tests do not go through it
                   "import \"./" (output/ns->path 'cljs.core) "\";\n"
                   program "\n"))
      (node f)
      (finally (.delete f)))))

(defn run-scripts
  "Evaluate `programs` in one runtime, in order, the way a REPL session does: the
  prelude is loaded once, and each script arrives as text and is eval'd. Each
  value - a script is an expression yielding a promise - is awaited and printed,
  so the result is one line per program.

  Each text is read from a file rather than embedded in the driver, so that nothing
  between the emitter and node re-escapes it. eval is called indirectly, through a
  binding, because that is what evaluates in global scope rather than in the
  driver's: a REPL's script must not be able to see the harness around it."
  [programs]
  (let [_      @core-module
        srcs   (mapv (fn [p]
                       (let [f (File/createTempFile "form" ".txt" @runtime-dir)]
                         (spit f p)
                         f))
                     programs)
        driver (File/createTempFile "driver" ".js" @runtime-dir)]
    (try
      (spit driver (str "import \"./runtime.js\";\n"
                        "import { readFileSync } from \"node:fs\";\n"
                        "const $eval = eval;\n"
                        "for (const n of ["
                        (str/join ", " (map #(str "\"./" (.getName ^File %) "\"") srcs))
                        "]) {\n"
                        "  console.log(await $eval("
                        "readFileSync(new URL(n, import.meta.url), \"utf8\")));\n"
                        "}\n"))
      (node driver)
      (finally (run! #(.delete ^File %) (conj srcs driver))))))

(defn run-script
  "run-scripts for one script."
  [program]
  (run-scripts [program]))

(defn write-module!
  "Compile `src` - one namespace, its ns form and all - and write it into the
  runtime directory at the path the layout gives it, opening with the import a
  module opens with.

  A hand-cranked stand-in for the compilation driver that M3's second half brings,
  and enough to test the half of $CLJS.require that fetches: a script can only
  require a namespace it does not already hold if that namespace is on disk, at the
  path runtime.js computes from its name."
  [cenv src]
  (names/with-name-scope
    (let [aenv (env/analysis-env cenv)
          body (mapv #(emitter/emit-top (ana/analyze-top cenv aenv %))
                     (reader/read-forms cenv src))
          nsym env/*current-ns*
          f    (File. ^File @runtime-dir ^String (output/ns->path nsym))]
      (.mkdirs (.getParentFile f))
      (.deleteOnExit f)
      (spit f (str/join "\n"
                        (into [(emitter/runtime-import
                                (output/specifier nsym output/prelude-name))]
                              (into (emitter/ns-prologue nsym
                                                         (env/requires cenv nsym))
                                    body))))
      f)))

(def core-module
  "cljs.core, compiled and written into the runtime directory, and the compile
  environment it was compiled in: {:file f :cenv cenv}.

  Both halves are needed and for different reasons. The FILE is what a program run
  beside it imports, so that its vectors and keywords are real objects. The CENV is
  what makes cljs.core's vars resolvable at all - a fresh environment has an empty
  cljs.core, so (pr-str x) in a test would not compile. core-env below hands out a
  namespace inside it.

  Built once per JVM and shared, because it costs about two seconds and is the same
  file every time. Every other module the tests write is hand-cranked by
  write-module! above; this one goes through driver/module-text, because cljs.core
  is the file whose imports and prologue we most want to be the real ones.

  The prelude is written a second time here, over the runtime.js that runtime-dir
  already put there: identical text, and the two Closure files that are always
  written. The REST of the Closure tree is ensured afterwards, from what cljs.core
  turned out to require - this is the one place that writes a module without going
  through the driver, so it is the one place that has to do the driver's job of
  making a module's goog imports resolve (clojure.cljs.output/ensure-goog!).

  EVERY form, and no skipping. This held a pinned set of the two forms that did not
  compile - a fixture quietly tolerating a third would make every test using it
  weaker without saying so - and §5.11 emptied it, so a failure now simply throws
  and takes the tests with it."
  (delay
    (let [cenv (env/compile-env {:ns 'cljs.core :core-macros 'cljs.core})
          f    (File. ^File @runtime-dir ^String (output/ns->path 'cljs.core))
          EOF  (Object.)]
      (output/write-prelude! @runtime-dir)
      (with-open [r (io/reader (io/file "src/clj/cljs/core.cljs"))]
        (let [rdr  (reader/push-back-reader r)
              aenv (env/analysis-env cenv)]
          (names/with-name-scope
            (let [body (binding [ana/*cljs-warnings* {:undeclared-var false}]
                         (loop [acc []]
                           (let [form (reader/read-one cenv rdr EOF)]
                             (if (identical? form EOF)
                               acc
                               (recur (conj acc (emitter/emit-top
                                                 (ana/analyze-top cenv aenv form))))))))]
              (.mkdirs (.getParentFile f))
              (.deleteOnExit f)
              (spit f (#'driver/module-text cenv 'cljs.core body))
              (output/ensure-goog! @runtime-dir (env/requires cenv 'cljs.core))))))
      {:file f :cenv cenv})))

(def ^:private core-env-counter (atom 0))

(defn core-env
  "A compile environment whose cljs.core is COMPILED, positioned in a namespace of
  its own.

  One environment is shared by every caller - building a second would mean
  compiling core.cljs again - so the isolation fresh-env gives by starting over is
  given here by a fresh NAMESPACE instead: two tests cannot see each other's defs
  because they are not defining into the same place."
  ([] (core-env (symbol (str "app.t" (swap! core-env-counter inc)))))
  ([ns-sym]
   (env/set-current-ns! ns-sym)
   ^clojure.cljs.env.CompileEnv (:cenv @core-module)))

(defn run-with-core
  "run-js. Kept as a name because it says what a test means, and because it was the
  only way to get cljs.core beside a program until §5.12 made it the only way there
  is."
  [program]
  (run-js program))

(defn output-with-core
  "`output`, against a compiled cljs.core: compile `src` in an environment that
  holds cljs.core's vars - which is what run-js can no longer supply on its own,
  since a compile environment is not a directory."
  ([src] (output-with-core (core-env) src))
  ([cenv src] (run-js (js cenv src))))

(defn output
  "Compile `src` and run it: the value of its last top-level form, as node prints
  it. The one-call form of js + run-js, and what most emitter tests use."
  ([src] (output (fresh-env) src))
  ([cenv src] (run-js (js cenv src))))

(defn script-output
  "`output` through the REPL's path instead of the module's: same source, same
  printed value, arrived at by evaluating a script rather than importing a module."
  ([src] (script-output (fresh-env) src))
  ([cenv src] (run-script (script cenv src))))

(defn session
  "Several REPL inputs against ONE compile environment: a script per input.

  Each gets its own name scope, because each is its own JavaScript scope - which is
  the arrangement doc/cljs-repl.md \u00a75 relies on when it lets the analyzer restart
  local numbering at every top-level form."
  ([srcs] (session (fresh-env) srcs))
  ([cenv srcs] (mapv #(script cenv %) srcs)))

(defn session-output
  "Evaluate `srcs` in one runtime, in order: what each printed, one string per
  input. A value that prints on more than one line would not survive this, so
  tests using it want single-line values."
  ([srcs] (session-output (fresh-env) srcs))
  ([cenv srcs] (str/split-lines (run-scripts (session cenv srcs)))))

;; --- assertions -------------------------------------------------------------

(defn message
  "The message of the exception `f` throws, or nil if it returns."
  [f]
  (try (f) nil (catch Exception e (.getMessage e))))

(defn warnings
  "Everything `f` reported as a warning, as one string - empty when it reported
  none.

  clojure.cljs.analyzer/warning prints to *err*, so this is both how a test that
  cares about a warning sees it and how every other test keeps it off the console."
  [f]
  (let [w (java.io.StringWriter.)]
    (binding [*err* w] (f))
    (str w)))

;; --- reading a source map back ----------------------------------------------
;;
;; A SECOND IMPLEMENTATION of base64 VLQ, written from the Source Map v3
;; specification rather than from clojure.cljs.source-map. Nothing here calls the
;; encoder, so a test that decodes a map is testing the map and not the symmetry
;; of one function with itself - which is all an assertion against an encoded
;; string constant would test.

(def ^:private vlq-digits
  "The alphabet VLQ values are spelled in."
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

(defn vlq-values
  "Every signed value in one VLQ-encoded segment.

  Five bits per digit, least significant first, the sixth bit set while more
  follow, and the SIGN IN THE LOW BIT of the assembled value."
  [s]
  (loop [cs (seq s), shift 0, acc 0, out []]
    (if-not cs
      out
      (let [d    (str/index-of vlq-digits (str (first cs)))
            more (pos? (bit-and d 0x20))
            acc  (+ acc (bit-shift-left (bit-and d 0x1f) shift))]
        (if more
          (recur (next cs) (+ shift 5) acc out)
          (recur (next cs) 0 0 (conj out (if (odd? acc)
                                           (- (bit-shift-right acc 1))
                                           (bit-shift-right acc 1)))))))))

(defn- unescape
  "One JSON string literal, and where it ends: [text end-index].

  Scanned rather than split on, because a source path holds a ] and a
  ClojureScript file holds every character there is - so a regex for the array
  around these stops in the middle of one. Written out rather than borrowed from a
  reader because EDN and JSON do not agree about escapes (\\b and \\f are JSON's and
  not EDN's), and the point of this file is not to trust the other side."
  [^String lit ^long from]
  (let [sb (StringBuilder.)]
    (loop [i (inc from)]
      (let [c (.charAt lit i)]
        (cond
          (= c \") [(.toString sb) (inc i)]
          (= c \\) (let [e (.charAt lit (inc i))]
                    (case e
                      \" (do (.append sb \") (recur (+ i 2)))
                      \\ (do (.append sb \\) (recur (+ i 2)))
                      \n (do (.append sb \newline) (recur (+ i 2)))
                      \r (do (.append sb \return) (recur (+ i 2)))
                      \t (do (.append sb \tab) (recur (+ i 2)))
                      \b (do (.append sb \backspace) (recur (+ i 2)))
                      \f (do (.append sb \formfeed) (recur (+ i 2)))
                      \u (do (.append sb (char (Integer/parseInt (subs lit (+ i 2) (+ i 6)) 16)))
                             (recur (+ i 6)))))
          :else (do (.append sb c) (recur (inc i))))))))

(defn- string-array
  "The array of strings `key` names, with null read as nil."
  [^String json ^String key]
  (let [open (+ (.indexOf json (str \" key "\":[")) (count key) 4)]
    (loop [i open, out []]
      (let [c (.charAt json i)]
        (case c
          \] out
          \" (let [[s j] (unescape json i)] (recur j (conj out s)))
          \n (recur (+ i 4) (conj out nil))         ; null
          (recur (inc i) out))))))                   ; , and whitespace

(defn map-sources
  "The `sources` array of an encoded map."
  [json]
  (string-array json "sources"))

(defn map-content
  "The `sourcesContent` entry for `source`, as text."
  [json source]
  (let [i (.indexOf ^java.util.List (map-sources json) source)]
    (when-not (neg? i)
      (nth (string-array json "sourcesContent") i))))

(defn map-positions
  "An encoded map as one entry per generated line: nil where the line is unmapped,
  and [source line column] - 1-based, as a person reads them - where it is not.

  The deltas are cumulative across the whole FILE rather than per line, which is
  the part of the format worth decoding rather than eyeballing."
  [json]
  (let [sources  (map-sources json)
        mappings (second (re-find #"\"mappings\":\"([^\"]*)\"" json))]
    (loop [ls (str/split mappings #";" -1), s 0, l 0, c 0, out []]
      (if-not (seq ls)
        out
        (let [line (first ls)]
          (if (str/blank? line)
            (recur (next ls) s l c (conj out nil))
            (let [[_ ds dl dc] (vlq-values (first (str/split line #",")))
                  s (+ s ds), l (+ l dl), c (+ c dc)]
              (recur (next ls) s l c (conj out [(nth sources s) (inc l) (inc c)])))))))))
