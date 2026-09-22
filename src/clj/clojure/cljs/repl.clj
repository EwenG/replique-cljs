;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "A ClojureScript REPL. doc/cljs-repl.md R0 and R1.

  Read one form, compile it to the evaluation unit of §5, hand the text to a
  runtime, print what comes back. The compiler's half of this was already built:
  CompileEnv is the persistent state, the reader resolves in the target's symbol
  table, and a var is a property of a namespace object - so a second definition
  lands where the first one was, which is the whole reason a REPL is possible here
  at all.

  What this namespace adds is small on purpose:

    IJsRuntime   one method, because loading is an expression rather than a
                 protocol method (§6.1)
    node-runtime the R0 host: node dialled on a socket, no HTTP anywhere
    repl         read-eval-print over clojure.cljs.reader/read-one
    the specials require, load-file, in-ns, remove-var and pages, recognised in head
                 position of an input and never reaching the compiler

  ONE LOOP, TWO TRANSPORTS. `repl` does not know which runtime it is talking to,
  and that is what makes clojure.cljs.browser a server rather than a second REPL:
  browser-repl is browser-runtime and this loop over one directory, the way
  node-repl is node-runtime and this loop. Sessions and their invalidation
  semantics live over there, because a refresh - which can strip a runtime out from
  under an in-flight evaluation - is a thing only that transport can have (§6).

  R2 so far: pr-str landed with M5 - runtime.js offers every object to
  cljs.core/pr-str before printing it as JavaScript - and *1/*2/*3 and *e land
  here, the first three in the compiled form (see remembering) and *e in the
  runtime's catch, which is the only thing that can see a throw.

  AND STACKS ARE SYMBOLICATED, which is the last of R2's headline items and took
  no runtime surface at all: the driver writes a .js.map beside every module
  (§5.43) and clojure.cljs.stacktrace reads one back (§5.45), so a frame that said
  ns/demo/core.js:9:10 says demo/core.cljs:5:12 by the time it is printed. See
  symbolicated, below - the one thing this namespace adds is the output directory,
  because that is where the maps are.

  INCLUDING A FORM TYPED HERE (§5.46), which needed the one thing a REPL has and a
  file does not have to be given: the characters that were read. compile-form takes
  them and writes a map beside the script, so a frame in a typed form names the form
  and the line within it. R2 is closed."}
  clojure.cljs.repl
  (:require [clojure.cljs.analyzer :as ana]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.emitter :as emitter]
            [clojure.cljs.env :as env]
            [clojure.cljs.goog :as cgoog]
            [clojure.cljs.names :as names]
            [clojure.cljs.npm :as npm]
            [clojure.cljs.source-info :as si]
            [clojure.cljs.source-map :as sm]
            [clojure.cljs.stacktrace :as stacktrace]
            [clojure.cljs.output :as output]
            [clojure.cljs.reader :as reader]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io BufferedReader File InputStreamReader OutputStreamWriter
            PushbackReader Writer]
           [java.net InetAddress ServerSocket Socket]
           [java.nio.charset StandardCharsets]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; --- the runtime ------------------------------------------------------------

(defprotocol IJsRuntime
  (-evaluate [this js]
    "Evaluate the script `js` and return {:status :success/:error :value \"...\"},
    :value being what the RUNTIME printed - a string, because printing happens
    where the value is (doc/cljs-repl.md §8). An error carries :stacktrace too.

    One method. Loading is an ordinary expression inside the script (§5), so
    there is nothing else a runtime has to be asked to do."))

(defprotocol IJsRuntimes
  "A runtime that may be more than one runtime - the browser transport, where
  several pages can hold a socket at the same time. OPTIONAL: node implements
  IJsRuntime alone, and everything below works on either.

  It exists for one distinction, which is the whole of the fan-out design:
  LOADING IS NOT EVALUATION. A require, a load-file or a remove-var is idempotent
  and has no interesting value - it answers nil wherever it runs - and what you
  want from it is that every page you have open picks up the new code. An
  ordinary form has a value, and a value needs one answer rather than a set of
  them differing by which page's clock or random seed produced it.

  So ship! broadcasts and eval-src does not, and that is decided here rather than
  in the transport."
  (-evaluate-all [this js]
    "Evaluate `js` in every connected runtime, and answer as -evaluate does for
    the one an ordinary evaluation would have gone to.

    What the others answered is the runtime's business, not the REPL's - a tab
    left open from yesterday failing to load something must not be the reason
    your require reports a failure. A runtime that wants to say so writes it to
    its own output.")
  (-pages [this]
    "Who is connected, oldest first: a vector of {:id :name :target?}. :id names
    the page for -select-page! and never means two pages in one session; :name is
    a guess at what it is, for a human choosing between them.")
  (-select-page! [this id]
    "Point evaluation at the page called `id`. False if there is no such page.

    It moves where the NEXT evaluation goes and disturbs nothing in flight."))

(defn- broadcast!
  "-evaluate-all where the runtime has it, -evaluate where it does not."
  [runtime js]
  (if (satisfies? IJsRuntimes runtime)
    (-evaluate-all runtime js)
    (-evaluate runtime js)))

;; --- compiling one input ----------------------------------------------------

(defn- root-message
  "The message of the deepest cause.

  The reader wraps, and a wrapper's message is the inner exception's class name
  followed by its text - so the useful half of `Unmatched delimiter: )` arrives
  behind `java.lang.RuntimeException: `, which is noise in front of a REPL user."
  [^Throwable e]
  (let [^Throwable root (loop [^Throwable e e]
                          (if-let [c (.getCause e)] (recur c) e))]
    (or (.getMessage root) (str root))))

(def ^:private no-history
  "Forms whose value does not become *1.

  ClojureScript's own list (cljs.repl/wrap-fn, 1.12.145:659), minus the entries
  that never reach a compiler here because they are REPL specials - require,
  load-file, in-ns and remove-var do their work on the JVM and answer nil-result,
  so they cannot shift a history they never produce a value for.

  What is left is `ns`, which IS an ordinary form here, and the four history vars
  themselves: reading *2 must not make it *1, or looking at the history would
  rewrite it."
  '#{ns *1 *2 *3 *e})

(defn- remembering
  "`form`, wrapped so that its value lands in *1 and pushes the two before it down.

  IN THE FORM, not in the runtime, which is ClojureScript's own answer
  (cljs.repl/wrap-fn) and the right one for a reason worth stating: *1 is a
  ClojureScript var holding a ClojureScript value, so assigning it is ordinary
  compiled code - §5.2 makes it a property assignment on the namespace object -
  and it needs no runtime surface, no munged name spelled in JavaScript and no
  second implementation for the browser.

  *e is NOT here, and the asymmetry is forced rather than chosen: a form that
  throws runs nothing after it, so the only place that can see the throw is the
  runtime's own catch. See runtime.js.

  The binding is not in scope inside `form` - it is the init of the let that binds
  it - so the name cannot capture anything the user wrote.

  QUALIFIED, where ClojureScript writes *1: cljs.core/*1 cannot be taken away by
  a (:refer-clojure :exclude [*1]) or by a namespace that defines its own, and §5.2
  makes the qualified form the same property assignment the unqualified one would
  have been.

  NO HISTORY WITHOUT cljs.core, which is a real configuration rather than a
  defensive check: the vars are cljs.core's, so a compile environment that has not
  analysed it has nowhere to put a value - and a REPL with no :out-dir is exactly
  that environment (see need-out-dir!). It gets its values printed and no history,
  which is better than every input failing to compile."
  [cenv form]
  (if (or (contains? no-history (if (seq? form) (first form) form))
          (not (env/core-name? cenv '*1)))
    form
    (let [ret (gensym "ret")]
      (list 'let [ret form]
            (list 'set! 'cljs.core/*3 'cljs.core/*2)
            (list 'set! 'cljs.core/*2 'cljs.core/*1)
            (list 'set! 'cljs.core/*1 ret)
            ret))))

(def ^:private input-counter (atom 0))

(defn- input-name
  "The base name of one REPL input's files: repl/<ns>/<n>.

  Three things hang off it and they have to agree - the script's //# sourceURL is
  <base>.js, its map is <base>.js.map, and the source the map embeds is labelled
  <base>.cljs - so it is minted once rather than three times.

  Under repl/ so it cannot collide with ns/ - what the driver writes - or with
  goog-subset/. A directory per namespace because that is what a sources panel
  shows as a tree, and the namespace is the thing a user is looking for in it."
  [ns-sym]
  (str "repl/" ns-sym "/" (swap! input-counter inc)))

(defn- rebased
  "`positions`, moved out of the reader's coordinates and into the text's.

  THE READER COUNTS THE SESSION AND THE MAP COUNTS THE FORM. A REPL holds one
  LineNumberingPushbackReader across every input, so the hundredth form is at line
  one hundred and something - while the text that map embeds is that form alone,
  whose first line is line one. So every position moves by where the text starts,
  and only positions on the text's FIRST line move by a column too, because only
  that line can begin anywhere but column one (clojure.cljs.reader/read-one+text).

  Nothing is dropped: a position outside the form cannot arise, since every one of
  them came from metadata the reader hung on a piece of this form."
  [positions ^long line ^long column]
  (mapv (fn [p]
          (when (:line p)
            (let [l (long (:line p))]
              (assoc p
                     :line   (inc (- l line))
                     :column (if (= l line)
                               (inc (- (long (or (:column p) 1)) column))
                               (or (:column p) 1))))))
        positions))

(defn- write-input-map!
  "Write the map for one REPL input beside where its script says it is.

  ON DISK, rather than in the //# sourceMappingURL as a data: URL - which
  clojure.cljs.source-map/data-url exists for and which would also work - and the
  reason is that §5.42 already gave the input a URL under repl/ that pointed at
  nothing. Making that URL real costs a file and buys two things: a browser can
  fetch the map by path like any other, and clojure.cljs.stacktrace needs no
  concept of a map that is not beside a file, so it reads a typed form's map with
  the code that already reads a module's.

  No write-if-changed! here, as the driver has: every input has a name no input has
  had before, so there is never anything to compare against."
  [out-dir base json]
  (let [f (io/file out-dir (str base ".js.map"))]
    (.mkdirs (.getParentFile f))
    (spit f json)))

(defn compile-form
  "One REPL input as the script to evaluate.

  The namespace prologue goes in every script, not just the first: each script is
  its own JavaScript scope, so the binding has to be remade - and remaking it is
  free, because $ns returns the object that is already there.

  It is built AFTER analysis, from the cursor and the requires analysis left
  behind, because an (ns ...) input moves both: the script that carries the ns form
  is already the new namespace's, and the prologue has to name what its own body
  names. The input's own NAME waits for the same reason - an (ns foo) input belongs
  to foo and not to wherever it was typed.

  NO STATIC ARITY DISPATCH, and nothing here has to say so any more. A static call
  site names an arity the var has TODAY, and the next input is free to redefine the
  var without it - so an expression typed here would stop meaning what it says.
  This used to bind emitter/*static-dispatch* false, because it was true for files;
  it is false everywhere now (§5.44), so a REPL input and a file agree, which is
  what a reloadable file needed all along.

  THE VALUE IS REMEMBERED ON THE WAY PAST, which is the other thing a REPL input
  is compiled with that a file is not - see remembering above.

  A FRESH URL EVERY TIME, which is the second of doc/cljs-output-layout.md §4's two
  rules and the opposite of the first. A reloaded namespace body is a new version of
  a file that already exists, so it carries that file's URL (driver/body-script). A
  typed form is not a version of anything - it is a different program each time -
  and reusing one name for a succession of different programs is what makes a
  debugger show the wrong source. So each gets its own, under a directory that can
  collide with neither tree: repl/<ns>/<n>.js.

  The number is per JVM rather than per session, which is all the property needs:
  the URLs have to differ from each other, not to start at one.

  AND A MAP BESIDE IT, when the caller has the form's text and somewhere to put it
  (§5.46). That is the one thing a typed form needs that a file does not: a file's
  source is on disk and a map can embed it from there, while a REPL input exists
  only as the characters that were read - which is why clojure.cljs.reader hands
  them back. Without either, this is exactly what it was before: a script with a
  //# sourceURL and no map."
  ([cenv form] (compile-form cenv form nil nil))
  ([cenv form text opts]
   (binding [cgoog/*closure-library* (cgoog/library-option opts)]
    (names/with-name-scope
     (let [m     (meta form)
           node  (ana/analyze-top cenv (env/analysis-env cenv) (remembering cenv form))
           nsym  env/*current-ns*
           base  (input-name nsym)
           map?  (boolean (and text (:out-dir opts) (:line m)))
           label (str base ".cljs")
           node  (cond-> node map? (si/source-info (assoc m :file label)))
           body  (emitter/emit-top-lines node emitter/return-value)
           reqs  (env/requires cenv nsym)
           ;; The prologue below spells a goog require as an await $CLJS.require,
           ;; which fetches it from the output directory by path - so the file has
           ;; to be there. A require typed at a REPL compiles no ClojureScript at
           ;; all when what it names is a goog namespace, so the driver's own call
           ;; never happens and this is the only one that can.
           _     (when (:out-dir opts) (output/ensure-goog! cenv (:out-dir opts) reqs))
           ;; and the same courtesy for the other tree, which used to be a
           ;; sentence and is now a build: a string require this namespace made
           ;; spells an await $CLJS.requireJs, and a module nothing has built is a
           ;; 404 one line later. clojure.cljs.npm builds it if it can and says so
           ;; if it cannot, once per directory and specifier - so a session in a
           ;; namespace whose package is missing is told once rather than once a
           ;; form, and a session whose package CAN be built is not told at all.
           _     (when (:out-dir opts)
                   (npm/ensure-js! (:out-dir opts) (env/js-requires cenv nsym) opts))
           chunk (emitter/script
                  (into (emitter/script-prologue nsym reqs
                                                 (env/js-requires cenv nsym))
                        body)
                  (str base ".js")
                  ;; a bare name, so it resolves against the script's own URL the
                  ;; way a module's does against the module's (driver/map-name)
                  (when map? (str (peek (str/split base #"/")) ".js.map")))]
       (when map?
         (write-input-map!
          (:out-dir opts) base
          (sm/encode {:file      (str (peek (str/split base #"/")) ".js")
                      :positions (rebased (sm/line-positions chunk)
                                          (:line m) (or (:column m) 1))
                      :content   {label text}})))
       (sm/text chunk))))))

(def nil-result
  "What a form evaluated for its effect on the JVM comes back as. The REPL specials
  below all return this: their work happened here, and the value of (require 'foo)
  is nil in Clojure too."
  {:status :success :value "nil"})

;; --- the REPL specials ------------------------------------------------------
;;
;; require, load-file and in-ns are not ClojureScript forms and never reach the
;; compiler: they are things the REPL does, recognised in head position of an
;; input, as cljs.repl recognises them. Everything they need was built for M3 -
;; each is a driver call, an analyzer call and a script - which is doc/cljs-repl.md
;; R1 being small because R0 and M3 were not.

(defn- unquoted
  "(require 'foo) reaches here as (require (quote foo)), because a REPL input is
  read before anything decides it is special."
  [x]
  (if (and (seq? x) (= 'quote (first x))) (second x) x))

(defn- need-out-dir!
  [opts what]
  (when-not (:out-dir opts)
    (throw (ex-info (str what " needs an output directory to compile into: start"
                         " the REPL with :out-dir, or use node-repl, which makes"
                         " one and runs a runtime beside it.")
                    {})))
  opts)

(defn- ship!
  "Evaluate each of `scripts` in order, stopping at the first failure and returning
  it - or nil_result when they all succeed.

  THIS IS THE BROADCAST PATH. Everything that reaches here is a load - require,
  load-file, remove-var - which is idempotent, answers nil, and is the thing you
  want every page you have open to receive. See IJsRuntimes."
  [runtime scripts]
  (or (some (fn [script]
              (let [r (broadcast! runtime script)]
                (when (= :error (:status r)) r)))
            scripts)
      nil-result))

(defn- require-script
  "A script that asks the runtime to load `ns-syms` if it does not have them, and to
  fetch the JavaScript modules `specifiers`.

  This is what plain require ships, and shipping a QUESTION rather than a body is
  what keeps the JVM from modelling the runtime's state (doc/cljs-repl.md 7.2): the
  runtime knows what it holds, so it decides whether to fetch. A JVM-side record of
  what this session has shipped would be wrong the moment a browser was refreshed.

  A MODULE IS FETCHED BY THE OTHER FUNCTION, and not because npm/ is a different
  directory: $CLJS.require consults `loaded`, which is about namespaces this
  session may have redefined, and a module has no such state - the module system's
  own one-evaluation-per-URL is the whole of it. Nothing is bound here, unlike the
  script prologue's requireJs: the value is not wanted, only the loading, and the
  next form evaluated in this namespace binds it for itself."
  [ns-syms specifiers]
  (emitter/script (-> (mapv #(str "await $CLJS.require(\"" % "\");") ns-syms)
                      (into (map #(str "await $CLJS.requireJs(\"" % "\");"))
                            specifiers))))

(defn- ordered-scripts
  "The [ns script] pairs of every namespace compiled for `targets`, in dependency
  order, each appearing once."
  [cenv opts targets]
  (first (reduce (fn [[acc seen] [nsym script]]
                   (if (seen nsym)
                     [acc seen]
                     [(conj acc script) (conj seen nsym)]))
                 [[] #{}]
                 (mapcat #(:scripts (driver/compile-namespace! cenv % opts))
                         targets))))

(defn- do-require
  "(require 'foo.bar), (require '[foo.bar :as f :refer [x]]), with a trailing
  :reload or :reload-all.

  Three steps, and the order between them is the whole of it: COMPILE the
  namespaces, so their vars exist to be referred; APPLY the specs to the current
  namespace, adding rather than replacing, which is what makes this not an ns form;
  then SHIP.

  What is shipped is what the flags choose. Plain require ships a question - the
  runtime fetches from disk what it does not have. :reload ships the named
  namespaces' bodies, which re-runs them whatever the runtime already holds.
  :reload-all ships every body in the graph, in dependency order."
  [cenv runtime opts args]
  (need-out-dir! opts "require")
  (let [args    (map unquoted args)
        flags   (set (filter keyword? args))
        specs   (vec (remove keyword? args))
        targets (ana/ns-form-deps (list* 'ns 'repl [(cons :require specs)]))
        scripts (ordered-scripts cenv opts targets)
        ;; WHAT EACH TARGET TURNED OUT TO BE, asked after compiling and not before,
        ;; because that is when the answer exists: a name with a source is now
        ;; declared, and one without is whatever driver/ensure! settled on. Three
        ;; kinds, and each is shipped differently - a namespace has a body and is
        ;; fetched with $CLJS.require, a Closure file has no body and is fetched
        ;; the same way (it is written under ns/ like any other), and a JavaScript
        ;; module is fetched with $CLJS.requireJs from npm/.
        modules (filterv #(ana/js-module-ns? cenv %) targets)
        fetched (filterv (complement (set modules)) targets)
        ;; only the namespaces with a body of their own, which is what :reload
        ;; takes from the tail of `scripts` - a target that compiled nothing put
        ;; nothing there to take
        bodies  (filterv #(env/declared? cenv %) targets)]
    (ana/require-libs! cenv specs)
    ;; A STRING REQUIRE COMPILES NOTHING, so the driver never runs for one and
    ;; this is the only place that can build it - or say why not - while the user
    ;; is still looking at what they typed. That is the whole of how
    ;; (require '["react" :as R]) at a REPL fetches react. Asked of the whole
    ;; namespace rather than of these specs alone, because the build is keyed on
    ;; the list anyway and the question is the same one.
    (npm/ensure-js! (:out-dir opts) (env/js-requires cenv env/*current-ns*) opts)
    (ship! runtime
           (cond
             (:reload-all flags) scripts
             (:reload flags)     (take-last (count bodies) scripts)
             :else               [(require-script fetched modules)]))))

(defn- do-load-file
  "(load-file \"path/to/foo.cljs\") - compile that file, whatever namespace it
  declares, and run its body.

  Always forced, which is what distinguishes it from require: you asked for this
  file. The sweep rides along in the body's own prologue, so a def deleted from the
  file is deleted from the runtime in the same script that redefines the rest."
  [cenv runtime opts args]
  (need-out-dir! opts "load-file")
  (let [r (driver/compile-file! cenv (unquoted (first args)) opts)]
    (ship! runtime [(second (last (:scripts r)))])))

(defn- do-in-ns
  "(in-ns 'foo) - move the cursor, creating the namespace if it is new.

  Declared as it is created, so that the driver treats it as a namespace that
  exists rather than demanding a source file for it. Nothing is shipped: a
  namespace object is made by whatever first assigns to it."
  [cenv _runtime _opts args]
  (let [nsym (unquoted (first args))]
    (when-not (and (symbol? nsym) (nil? (namespace nsym)))
      (throw (ex-info (str "in-ns takes an unqualified symbol, got " (pr-str nsym))
                      {:form nsym})))
    (names/ns-alias nsym)
    (env/declare-ns! cenv nsym)
    (env/set-current-ns! nsym)
    nil-result))

(defn- do-remove-var
  "(remove-var 'app.core/x) - undefine one var, here and in the runtime.

  What Replique offers under the same name, and for the same reason: a def deleted
  from a source file is not removed by reloading that file, so a REPL session
  accumulates definitions its source no longer has - and the one that bites is a
  function you deleted and can still call. A whole-file sweep is the eventual
  answer (doc/cljs-repl.md 7.3) and wants an analysis model to say which defs
  vanished; this needs no model, because you named the var.

  Two halves, and both are needed. Here, the var stops resolving - in the namespace
  that defined it and in every namespace that referred it. There, the property
  stops existing, which is what makes a call to it fail rather than run the version
  you thought you had deleted."
  [cenv runtime opts args]
  (let [qsym (unquoted (first args))
        _    (env/remove-var! cenv qsym)
        ns-sym (symbol (namespace qsym))]
    (ship! runtime
           [(emitter/script
             (into (emitter/ns-prologue ns-sym)
                   [(emitter/delete-var ns-sym (symbol (name qsym)))]))])))

(defn- pages-text
  [pages]
  (if (empty? pages)
    "No page is connected."
    (str/join "\n"
              (for [{:keys [id name target?]} pages]
                ;; the star is the only column that matters and it is the one you
                ;; read first, so it goes on the left rather than in a note below
                (str (if target? "* " "  ") id "  " name)))))

(defn- do-pages
  "(pages) - who is connected, and which of them an ordinary form is evaluated in.
  (pages 2) - make page 2 that one.

  THE ONE SPECIAL THAT IS NOT ABOUT NAMESPACES, and it exists because a socket let
  more than one page connect at a time (doc/cljs-repl.md 6.3). A load already goes
  to all of them; this is how you say which one a VALUE should come from - the
  page you are looking at rather than the tab you opened last.

  A runtime that cannot have more than one page says so instead of failing: node
  is one runtime, and asking it which page to use is a reasonable question with a
  short answer."
  [_cenv runtime _opts args]
  (let [id (first args)]
    (cond
      (not (satisfies? IJsRuntimes runtime))
      {:status :success :value "This runtime has one page and it is that one."}

      (and (some? id) (not (integer? id)))
      {:status :error :phase :compile
       :value  (str "(pages " (pr-str id) ") - a page is named by a number."
                    " (pages) lists them.")}

      (and (some? id) (not (-select-page! runtime id)))
      {:status :error :phase :compile
       :value  (str "There is no page " id ". (pages) lists them.")}

      :else
      {:status :success :value (pages-text (-pages runtime))})))

(def ^:private specials
  {'require    do-require
   'load-file  do-load-file
   'in-ns      do-in-ns
   'remove-var do-remove-var
   'pages      do-pages})

(defn- symbolicated
  "`result`, with its stack trace read back as ClojureScript
  (clojure.cljs.stacktrace) and the JavaScript one kept beside it.

  HERE, because this is where a result and the output directory are in the same
  place: the maps are files the driver wrote into it, so a REPL with no :out-dir -
  which is a real configuration, see need-out-dir! - has nothing to read and gets
  the stack it was given.

  :js-stacktrace is not a fallback. It is the answer when the mapping itself is
  what you doubt, which is the one question the mapped stack cannot be asked."
  [opts result]
  (if-let [stack (and (:out-dir opts) (:stacktrace result))]
    (assoc result
           :stacktrace    (stacktrace/trace (:out-dir opts) stack)
           :js-stacktrace stack)
    result))

(defn eval-form
  "Compile `form` and evaluate it in `runtime`, or run it here if it is one of the
  REPL specials above.

  A failure on this side of the wire comes back in the same shape as one from the
  other side, with :phase saying which: a REPL user wants to see what went wrong,
  not to find out which process noticed.

  `opts` carries :out-dir and :source-paths, which the specials need - and which
  symbolicated needs too, since a stack is read back against the directory the
  modules were compiled into.

  `text` is the source of `form` as it was typed (clojure.cljs.reader/read-one+text)
  and is what lets the input carry a map of its own (§5.46). Optional, because a
  form that was built rather than read has no text and still has to be evaluable -
  which is most of what a test does."
  ([cenv runtime form] (eval-form cenv runtime form nil nil))
  ([cenv runtime form opts] (eval-form cenv runtime form opts nil))
  ([cenv runtime form opts text]
   (let [special (and (seq? form) (seq form) (get specials (first form)))]
     (try
       (symbolicated
        opts
        (if special
          (special cenv runtime opts (rest form))
          (-evaluate runtime (compile-form cenv form text opts))))
       (catch Exception e
         {:status :error :phase :compile :value (root-message e)})))))

(defn eval-src
  "Every form of `src`, evaluated in order: the result of each. What a test uses,
  and what a file loaded by hand goes through."
  ([cenv runtime src] (eval-src cenv runtime src nil))
  ([cenv runtime src opts]
   (let [rdr (reader/push-back-reader src)
         eof (Object.)]
     (loop [results []]
       (let [[form text] (reader/read-one+text cenv rdr eof)]
         (if (identical? form eof)
           results
           (recur (conj results (eval-form cenv runtime form opts text)))))))))

;; --- the node runtime -------------------------------------------------------

(def ^:private node-resource
  "The node transport, beside runtime.js on the classpath. A separate file because
  the browser replaces this one and keeps the other (doc/cljs-repl.md §6)."
  "clojure/cljs/runtime_node.js")

(defn write-runtime!
  "What a node runtime is run beside: an output root (clojure.cljs.output -
  runtime.js and the package.json that makes node read a .js file under it as an
  ES module) plus the node transport, which is this host's and not the layout's."
  [dir]
  (let [dir (output/write-prelude! dir)]
    (spit (File. dir "runtime_node.js") (slurp (io/resource node-resource)))
    dir))

(def ^:private json-string
  "`s` as a JSON string literal.

  The JVM writes JSON and node writes EDN, so neither side has to parse the format
  it is worst at: node has JSON.parse built in, the JVM has clojure.edn.

  clojure.cljs.source-map's, because a source map needs the same escaping for the
  same reason - it embeds whole ClojureScript files - and this side sends emitted
  JavaScript, which js* lets hold any character at all, control characters
  included."
  sm/json-string)

(defn- pump!
  "Copy `in` to `out` on a thread of its own, for as long as it lasts.

  This is where a runtime's own output goes - console.log from evaluated code, and
  anything node says about itself. Before M5 there is no *print-fn* and so no
  :print channel (§8); the process's stdout is that channel, which means program
  output and values interleave by arrival rather than by turn."
  [in ^Writer out]
  (doto (Thread. #(with-open [^BufferedReader r (io/reader in)]
                    (loop []
                      (when-let [line (.readLine r)]
                        (locking out (.write out (str line "\n")) (.flush out))
                        (recur))))
                 "cljs-runtime-output")
    (.setDaemon true)
    (.start)))

(defn- temp-dir ^File []
  (.toFile (Files/createTempDirectory "cljs-repl" (into-array FileAttribute []))))

(defn- delete-tree! [^File f]
  (when (.isDirectory f)
    (run! delete-tree! (.listFiles f)))
  (.delete f))

(defn node-runtime
  "Start a node runtime and wait for it to dial back.

  The JVM listens and node connects, not the other way round: the socket exists
  before the process does, so there is no port to configure and no race to lose.

    :dir     where the prelude is written and node is run - a temp directory by
             default, and at R1 the output directory the modules go in
    :out     where the runtime's own output is copied, default *out*
    :timeout ms to wait for node to dial back, default 15000

  Closeable, and closing it closes the socket, which is how the node process
  learns the session is over.

  One evaluation at a time: the wire matches answers to questions by position,
  having asked only one. A REPL is that shape anyway; a caller that wants two must
  serialize them."
  ([] (node-runtime nil))
  ([{:keys [dir out timeout] :or {out *out* timeout 15000}}]
   ;; a directory we made is ours to remove; one we were handed is not
   (let [^File own (when-not dir (temp-dir))
         ^File dir (write-runtime! (or dir own))
         server    (doto (ServerSocket. 0 1 (InetAddress/getByName "127.0.0.1"))
                     (.setSoTimeout timeout))
         proc      (try
                     (-> (ProcessBuilder. ["node" "runtime_node.js"
                                           (str (.getLocalPort server))])
                         (.directory dir)
                         (.redirectErrorStream true)
                         (.start))
                     (catch java.io.IOException e
                       (.close server)
                       (when own (delete-tree! own))
                       (throw (ex-info (str "Could not start node: " (ex-message e)
                                            ". A ClojureScript REPL needs node on"
                                            " PATH.")
                                       {:dir (str dir)} e))))]
     (pump! (.getInputStream proc) out)
     (let [close-all (fn []
                       (.destroy proc)
                       (.close server)
                       (when own (delete-tree! own)))
           ^Socket sock (try (.accept server)
                             (catch Exception e
                               (close-all)
                               (throw (ex-info (str "The node runtime did not connect"
                                                    " within " timeout "ms.")
                                               {:dir (str dir)} e))))
           in  (BufferedReader. (InputStreamReader. (.getInputStream sock)
                                                    StandardCharsets/UTF_8))
           w   (OutputStreamWriter. (.getOutputStream sock) StandardCharsets/UTF_8)
           bye (fn [] (.close sock) (close-all))]
       ;; the hello is what says the prelude loaded; without it the first failure
       ;; would be reported against whatever form the user happened to type first
       (let [hello (.readLine in)]
         (when-not (= "{:type :ready}" hello)
           (bye)
           (throw (ex-info "The node runtime did not say it was ready."
                           {:got hello :dir (str dir)}))))
       (reify
         IJsRuntime
         (-evaluate [_ js]
           (doto w (.write ^String (json-string js)) (.write "\n") (.flush))
           (if-let [line (.readLine in)]
             (try
               (edn/read-string line)
               (catch Exception e
                 {:status :error :phase :transport
                  :value  (str "Unreadable result: " (ex-message e))
                  :got    line}))
             {:status :error :phase :transport
              :value  "The runtime disconnected."}))
         java.io.Closeable
         (close [_] (bye)))))))

;; --- read, eval, print, loop ------------------------------------------------

(def ^:private EOF (Object.))
(def ^:private AGAIN (Object.))

(defn- skip-line!
  "Discard the rest of the current line. A malformed form leaves the reader inside
  it (clojure.cljs.reader/read-one), and this is the recovery policy the reader
  declines to choose: the same one clojure.main takes, because a REPL user types
  one form per line and expects the bad one to be gone."
  [^PushbackReader rdr]
  (loop []
    (let [c (.read rdr)]
      (when-not (or (== c -1) (== c (int \newline)))
        (recur)))))

(defn- print-result! [^Writer out {:keys [status value stacktrace phase]}]
  (.write out (str (when (= :error status)
                     (str "error" (when phase (str " (" (name phase) ")")) ": "))
                   value "\n"))
  (when (and (= :error status) stacktrace (not= "" stacktrace))
    (.write out (str stacktrace "\n")))
  (.flush out))

(defn repl
  "Read, evaluate, print, loop, against `runtime`, until the input runs out.

    :ns            the namespace to start in, default wherever the caller is
    :in            what to read from, default *in*
    :out           where to print, default *out*
    :out-dir       the compiled output directory - the SAME one the runtime fetches
                   modules from, or require would compile where nothing looks
    :source-paths  where .cljs files are found, default the classpath directories

  The last two are what require, load-file and :reload need, and nothing else does;
  node-repl below fills them in.

  THE CURSOR IS THIS LOOP'S, not the compile environment's (env/*current-ns*): a
  second REPL on the same environment sees the same vars and keeps its own idea of
  where it is standing, and an (ns ...) or (in-ns ...) typed here moves that and
  nothing outside it.

  Reading one form at a time is the point: a form that moves the namespace cursor
  has to take effect before the next form is read, which is why read-one exists
  and read-forms will not do."
  ([cenv runtime] (repl cenv runtime nil))
  ([cenv runtime {:keys [ns in out] :or {in *in* out *out*} :as opts}]
   (env/with-current-ns (or ns env/*current-ns*)
    (let [rdr        (reader/push-back-reader in)
          ^Writer wr out
          eval-opts  (select-keys opts [:out-dir :source-paths])]
      ;; cljs.core BEFORE the first prompt. Every script this REPL ships opens with
      ;; `await $CLJS.require("cljs.core")` - every namespace requires it, said or
      ;; not (env/requires) - and that require reads a file off disk, so something
      ;; has to have compiled it there. Doing it here rather than lazily means the
      ;; first form a user types is not the one that pays two seconds for it.
      ;;
      ;; Only when there is somewhere to put it. A REPL with no :out-dir cannot
      ;; require anything at all (need-out-dir!), and now cannot have cljs.core
      ;; either - it is the prelude and nothing else, which is a real configuration
      ;; while a compiler is being built and a poor one to hand a user.
      (when (:out-dir opts)
        (driver/compile-namespace! cenv 'cljs.core eval-opts))
      (loop []
        (doto wr (.write (str env/*current-ns* "=> ")) (.flush))
        (let [[form text] (try
                            (reader/read-one+text cenv rdr EOF)
                            (catch Exception e
                              (print-result! wr {:status :error :phase :read
                                                 :value  (root-message e)})
                              (skip-line! rdr)
                              [AGAIN nil]))]
          (cond
            (identical? form EOF)   (doto wr (.write "\n") (.flush))
            (identical? form AGAIN) (recur)
            :else (do (print-result! wr (eval-form cenv runtime form eval-opts text))
                      (recur)))))))))

(defn node-repl
  "A ClojureScript REPL on node: an output directory, a runtime beside it, and the
  loop over both. Blocks until the input runs out.

    :dir           the output directory - a temporary one, removed on exit, if none
                   is given
    :source-paths  where .cljs files are found, default the classpath directories
    :ns            the namespace to start in, default cljs.user
    :in :out       as repl takes them
    :program-out   where the runtime's own output goes, default :out

  One call, because the two halves have to agree about one directory: the driver
  compiles into it and the runtime fetches out of it, and a require would silently
  compile somewhere nothing looks if they differed. Wiring them by hand is still
  available - this is node-runtime and repl, in that order, over one directory."
  ([] (node-repl nil))
  ([{:keys [dir source-paths ns in out program-out]
     :or   {ns 'cljs.user in *in* out *out*}}]
   ;; THE CURSOR IS ESTABLISHED HERE, before anything that moves it. env/compile-env
   ;; positions itself with set-current-ns!, which is a set! and so needs a binding
   ;; to move - and this is the outermost thing a caller runs, so this is where the
   ;; binding belongs. Without it, the very first call into this namespace from a
   ;; plain REPL throws "Can't change/establish root binding".
   (env/with-current-ns ns
     (let [^File own (when-not dir (temp-dir))
           ^File d   (io/file (or dir own))
           ;; :core-macros, because cljs.core is vendored now and a REPL that cannot
           ;; expand defn is not one
           cenv      (env/compile-env {:ns ns :core-macros 'cljs.core})]
       (try
         (with-open [rt (node-runtime {:dir d :out (or program-out out)})]
           (repl cenv rt {:ns ns :in in :out out
                          :out-dir d :source-paths source-paths}))
         (finally (when own (delete-tree! own))))))))
