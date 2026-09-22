;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The output layout: what file a namespace becomes, and how one file
  names another.

      <out>/package.json      {\"type\": \"module\"}
      <out>/runtime.js        the prelude
      <out>/ns/app/core.js    app.core
      <out>/ns/my-lib/core.js my-lib.core   - NOT my_lib
      <out>/npm/react.js      the module (:require [\"react\" :as React]) names

  Three decisions, taken in doc/cljs-output-layout.md and each of them load-bearing
  somewhere:

  NESTED, mirroring the namespace. Flat (ns/app.core.js) would make every specifier
  a constant and save the arithmetic below, which is its whole case; a directory of
  several hundred dotted filenames once cljs.core and the goog subset land is the
  case against, and it wins.

  RELATIVE specifiers, always. The same emitted module is resolved by node from the
  filesystem on a cold start and by a browser from a URL, and relative is the only
  form both read the same way: an absolute /runtime.js is the server root in one and
  the filesystem root in the other, and a bare specifier needs an import map in the
  browser AND a package.json :imports entry in node.

  UNMUNGED. cljs.util/ns->relpath sends my-lib.core to my_lib/core.cljs because a
  JVM package name cannot hold a hyphen; nothing loads an emitted .js through a
  classloader, so that reason does not reach here. Dropping the munge means the
  JavaScript side needs no munge either - urlFor in runtime.js is a dot-to-slash
  replace rather than a second implementation of an injective function - and it
  makes the path injective because . -> / is, rather than because a namespace
  segment may not contain _. A stated divergence from every other ClojureScript
  tool's output tree, alongside letfn*.

  Note what does NOT change: clojure.cljs.names/ns-alias still munges, because
  my_lib$core$ns has to be a JavaScript identifier and a filename does not. Same
  namespace, two spellings, two constraints.

  There is a second implementation of ns->path, and there has to be: $CLJS.require
  computes a URL from a name with nothing to ask the JVM (doc/cljs-repl.md 7.2), so
  runtime.js states the same rule in JavaScript. output-test runs the two against
  each other rather than trusting them to stay in step.

  ONE OF THOSE TREES IS NOT WRITTEN HERE. npm/ is built by esbuild out of
  node_modules, one file per specifier, and clojure.cljs.npm is what schedules it.
  What THIS namespace owns is the NAME each specifier is filed under (js->path),
  which the compiler emits imports against and which the bundler is told rather
  than asked - so the mapping has exactly one statement on the JVM side however
  the tree gets built. See doc/cljs-npm.md.

  Nothing durable records a path - no deps file, no manifest, no load-time ordering
  on the JVM (7.3) - so changing the layout makes an output directory stale rather
  than wrong. It is known here and in runtime.js, and nowhere else."}
  clojure.cljs.output
  (:require [clojure.cljs.env :as env]
            [clojure.cljs.goog :as goog]
            [clojure.cljs.names :as names]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io File]))

(def ns-dir
  "The directory emitted namespaces live under, so that nothing emitted can land on
  a prelude file. The collision is not hypothetical and not avoidable by choosing
  well: `runtime` is a legal one-segment namespace name, and a one-segment name has
  no directory to sit in, so it wants runtime.js under every scheme. Separating the
  two trees is the only thing that rules it out - and it leaves the prelude free to
  grow a second and third file later.

  Named for $ns, which is what the objects in it are called."
  "ns")

(defn ns->path
  "The output file for a namespace, relative to the output root: app.core ->
  ns/app/core.js, and goog.math.Long -> goog-subset/goog/math/Long.js.

  ns-alias is called for its preconditions rather than its value - a namespace with
  an empty segment (a.b., which would want a file named .js) or one that cannot
  spell a JavaScript name is refused there, before any path is computed."
  [ns-sym]
  (names/ns-alias ns-sym)
  (if (goog/goog-ns? ns-sym)
    ;; goog does not live under ns-dir: it is not compiled from ClojureScript and
    ;; nothing emitted can be named goog.*, which goog-ns? reserves. The rule
    ;; INSIDE its tree is this same one, which is what lets runtime.js's urlFor
    ;; state both branches without a manifest.
    (goog/ns->path (str ns-sym))
    (str ns-dir "/" (str/replace (str ns-sym) "." "/") ".js")))

(def js-dir
  "The directory a JavaScript module a string require names is fetched from, beside
  ns-dir and the goog tree.

  ITS CONTENTS ARE NOT EMITTED. Everything else under an output root is emitted
  by this compiler; this one is BUNDLED - esbuild reads node_modules and writes one
  file per specifier, scheduled by clojure.cljs.npm - and all that is owned here is
  the NAME each specifier is filed under, which is js->path below and which the
  bundler is told rather than asked. doc/cljs-advanced.md 3 is why it is that way
  round: no bundler is vendored and none is mandatory, so what crosses the line is
  a mapping and a list, whoever ends up running the tool over them."
  "npm")

(defn js->path
  "The file a string require names, relative to the output root: \"react\" ->
  npm/react.js, \"@visx/scale\" -> npm/@visx/scale.js.

  THE SPECIFIER IS THE PATH, with .js appended and nothing escaped. That is what
  makes it injective without a table - distinct specifiers differ somewhere, and
  appending a constant to each keeps them differing - and it is also what makes
  the mapping legible in a stack trace and computable in JavaScript, where
  runtime.js states it a second time (urlForJs) for the script path.

  A sub-path becomes a sub-directory, so react-dom/client is npm/react-dom/client.js
  and every date-fns locale lands under npm/date-fns/locale. A scope keeps its @.

  THE .js IS APPENDED UNCONDITIONALLY, so \"sse.js\" - a real package - is
  npm/sse.js.js. Skipping it for a specifier that already ends in .js would be the
  collision this function exists not to have: \"sse\" and \"sse.js\" are two
  packages, and both would then be npm/sse.js.

  What is refused is what could not be a file under this root, or could be the
  wrong one: a relative or absolute specifier (a different feature - a file beside
  the source rather than a package), a . or .. segment, an empty segment, a
  trailing slash, a $ (the sugar for a property path, which the analyzer has
  already split off - see below), and anything a URL cannot carry unescaped.
  js-alias is called for its preconditions besides, so a specifier that cannot be
  a JavaScript name is refused here rather than at emission - exactly as ns->path
  calls ns-alias.

  Two specifiers differing only in case would be one file on macOS, as two
  namespaces would (doc/cljs-output-layout.md 4). Not detected here: npm names
  are lower-case by policy, so the collision this rules out for namespaces has no
  way to arise - and if one ever does, the check is the same one."
  [specifier]
  (let [bad (fn [why]
              (throw (ex-info (str "Bad JavaScript module specifier: "
                                   (pr-str specifier) " - " why)
                              {:specifier specifier})))]
    (when-not (and (string? specifier) (not (str/blank? specifier)))
      (bad "a string require names a module, and an empty name names nothing."))
    (when (re-find #"[\s\\\"?#]" specifier)
      (bad (str "a specifier is a file name under " js-dir
                "/ and a URL besides, so it cannot hold a space, a backslash, a"
                " quote, a ? or a #.")))
    (when (or (str/starts-with? specifier ".") (str/starts-with? specifier "/"))
      (bad (str "it names a path rather than a package. A string require names a"
                " module resolved from node_modules; a file beside the source is"
                " not something this compiler resolves.")))
    (when (str/ends-with? specifier "/")
      (bad "a specifier names a module, and a trailing slash names a directory."))
    ;; "date-fns/sub$default". A $ in a string require is the sugar for a property
    ;; path INTO the module (doc/cljs-npm.md 4.1), and the analyzer splits it off
    ;; where the ns form is read - so what reaches a file name is the module half
    ;; alone, and a $ arriving here is an unsplit specifier rather than a package
    ;; (npm has no $ in a name). Taken literally it would name a file no bundler
    ;; builds: a 404 at load, in place of this sentence.
    (when (str/includes? specifier "$")
      (bad (str "a $ in a specifier names a path INSIDE the module, which is not"
                " part of any file name - the module this one names is "
                (pr-str (first (str/split specifier #"\$"))) ".")))
    (when (some #{"" "." ".."} (str/split specifier #"/" -1))
      (bad "every segment of it has to be a name."))
    ;; LAST, not first as ns->path calls ns-alias: the checks above say what is
    ;; wrong with a path, and this one says only that the result is not a
    ;; JavaScript name - so asking it last is what puts the sharper message first.
    (names/js-alias specifier)
    (str js-dir "/" specifier ".js")))

(defn symbol-specifier
  "The JavaScript module specifier a bare SYMBOL in a require names, or nil when
  that symbol could not be one.

      react              -> \"react\"
      clipboard-polyfill -> \"clipboard-polyfill\"
      app.core           -> nil
      cljs.core          -> nil

  shadow-cljs lets a package be required by its bare name, and a project written
  against it spells (:require [react :as React]) where upstream spells
  [\"react\" :as React]. Both are read here (doc/cljs-compiler.md 5.53), for the
  reason the three options of a string require are shadow's three: a project moving
  between the two compilers should not have to rewrite its ns forms.

  A DOT IS THE ANSWER NO. It is what a namespace name is made of - every
  ClojureScript namespace anyone writes has one - and it is not something the symbol
  spelling of a package can carry unambiguously, because a package whose name has a
  dot in it can always be written as a string instead. What that buys is the error
  message for the mistake this rule would otherwise swallow: a require of a
  namespace that does not exist, which is a typo or a file not written yet, still
  says `Could not locate nosco/colours.cljs on the source path` rather than quietly
  becoming a package no bundler will ever build. Measured over a 414-namespace
  application, the rule separates the three real packages from the fourteen missing
  namespaces without a single mistake either way.

  It is also not the whole question. A one-segment name may perfectly well be a
  ClojureScript namespace, so a SOURCE WINS - see clojure.cljs.analyzer/js-module-ns?,
  which asks this first because it is the cheap half and then asks the two halves
  that need the world.

  Checked by js->path, so one function decides what a specifier may be. A symbol
  cannot hold most of what that refuses - a space, a quote, a slash, which would
  make it qualified - but stating it once is what keeps a specifier meaning one
  thing however it was written."
  [sym]
  (let [s (str sym)]
    (when (and (simple-symbol? sym) (not (str/includes? s ".")))
      (try (js->path s) s (catch Exception _ nil)))))

(defn specifier
  "How a module compiled from `from-ns` names `to-path`, which is relative to the
  output root: from ns/app/core.js, the prelude is ../../runtime.js and
  my-lib.core is ../my-lib/core.js.

  Always relative, and always with the extension written out: ES modules have no
  extension guessing in either host."
  [from-ns to-path]
  (let [from-dirs (butlast (str/split (ns->path from-ns) #"/"))
        to-parts  (str/split to-path #"/")
        to-dirs   (butlast to-parts)
        shared    (count (take-while true? (map = from-dirs to-dirs)))
        up        (repeat (- (count from-dirs) shared) "..")
        down      (concat (drop shared to-dirs) [(last to-parts)])
        path      (str/join "/" (concat up down))]
    ;; "./" on a specifier that would otherwise start with a name: a bare
    ;; specifier is not a relative path, it is a package lookup.
    (if (str/starts-with? path "..") path (str "./" path))))

;; --- the prelude ------------------------------------------------------------

(def prelude-name
  "runtime.js sits at the output root, not under ns-dir, and every module reaches it
  by the specifier above."
  "runtime.js")

(def prelude-resource
  "Where runtime.js lives on the classpath. It sits in src/clj beside the compiler
  that emits references to it; that tree is an unfiltered resource root, so the file
  ships in the jar verbatim."
  "clojure/cljs/runtime.js")

(defn prelude-source
  "The text of runtime.js. Read on each call: it is a file on disk, and a REPL
  session that changes it should not have to restart to see the change."
  []
  (slurp (io/resource prelude-resource)))

(defn write-prelude!
  "Write what any output directory needs before anything is compiled into it:
  runtime.js, the package.json that makes node read a .js file under this root as
  an ES module rather than as CommonJS, and the two Closure files that are ours -
  base.js, which every converted goog file imports, and goog.js, which a require
  of the bare name fetches. One package.json covers the whole tree, ns-dir and the
  goog tree included.

  THE REST OF THE GOOG TREE IS NOT WRITTEN HERE, and that is the difference between
  a subset and a library. What has to be written is the closure of what was actually
  required, which is known after compiling rather than before - see `ensure-goog!`,
  which the driver calls on its way out.

  Read from the classpath on each call rather than cached, so editing runtime.js
  or a goog file and starting a new runtime is enough to see the change.

  Not a transport: runtime_node.js and runtime_browser.js are one host's way of
  being reached rather than something a compiled program needs, and
  clojure.cljs.repl and clojure.cljs.browser each add theirs beside these
  (doc/cljs-repl.md 6)."
  [dir]
  (let [dir (io/file dir)]
    (.mkdirs dir)
    (spit (File. dir prelude-name) (prelude-source))
    (spit (File. dir "package.json") "{\"type\": \"module\"}\n")
    (goog/write-goog! dir [])
    dir))

(defn ensure-goog!
  "Write into `dir` the Closure files the namespaces `required` name, and what those
  require in turn.

  `required` is any collection of namespace symbols - a whole requires set, Closure
  names and ClojureScript names mixed - because that is what its callers have, and
  telling them apart is this function's job rather than theirs.

  BOTH KINDS OF CLOSURE NAMESPACE, which is why the filter is closure-ns? and not
  goog-ns?: a name in the goog tree, and a Closure-style JavaScript file found on
  the classpath at the name's own path - com.cognitect.transit out of transit-js's
  jar. The second kind is written under ns-dir rather than the goog tree, which
  goog/ns->path decides; everything else about the two is the same, down to the
  converter.

  Called where a module's imports or a script's requires have just been decided:
  both spell a Closure name as a path under this root, and a path that nothing
  wrote is a 404 at load. Cheap to call often - in library mode nothing is
  converted twice (clojure.cljs.goog/written), in subset mode there are twenty
  files, and a name that is neither is answered from a cache after the first ask
  (clojure.cljs.goog/classpath-entry)."
  ([dir required] (ensure-goog! nil dir required))
  ([cenv dir required]
   (let [closure? (fn [ns-sym]
                    ;; THE SAME RULE clojure.cljs.analyzer/closure-ns? states, and
                    ;; it has to be the same: a namespace that was compiled from a
                    ;; .cljs must not then have a .js of its own name converted
                    ;; over the top of the module this run just emitted. The
                    ;; analyzer decides that a declared namespace is not a Closure
                    ;; one, the driver looks for a source before it looks on the
                    ;; classpath, and this is the third place it is decided -
                    ;; because this is the only one holding the file handle.
                    ;;
                    ;; cenv is optional because write-prelude! has none and needs
                    ;; none: with no compile environment there is nothing declared,
                    ;; and the goog half of the question does not depend on one.
                    (and (goog/closure-ns? ns-sym)
                         (not (and cenv (env/declared? cenv ns-sym)))))
         names    (into [] (comp (filter closure?) (map str) (distinct)) required)]
     (when (seq names)
       (goog/write-goog! dir names))
     dir)))

;; --- what the bundler still owes ---------------------------------------------

(defn missing-js
  "Which of `specifiers` name no file under `dir` yet, sorted and without repeats.

  The one question about npm/ this compiler can answer, and it is not the one it
  would like to. Whether a PACKAGE exists is the bundler's business - it does the
  resolving, and node_modules is not ours to read - but whether the FILE WE NAMED
  is on disk is a question about a path we computed, and a path nothing wrote is a
  404 when the program loads.

  Asked after compiling and never before. The bundler's input is the specifier
  list a compile produces, so refusing to compile until npm/ is populated would be
  a cycle with no way in (doc/cljs-npm.md 6). This turns the 404 into a sentence
  instead, which is the whole of what can be done about it from here."
  [dir specifiers]
  (into []
        (comp (distinct) (remove #(.isFile (File. (io/file dir) ^String (js->path %)))))
        (sort specifiers)))

(def ^:private reported
  "Which missing modules this process has already complained about, as
  {dir #{specifier}}.

  clojure.cljs.goog/written's shape and its reason: the check is cheap and is made
  on every compile, and a REPL evaluating form after form in a namespace whose
  package is not there should be told once rather than once a form."
  (atom {}))

(defn report-missing-js!
  "Warn about the modules among `specifiers` that are not under `dir`, once per
  directory and specifier. Returns all of them, freshly reported or not, so a
  caller can hand the list on rather than the warning.

  A WARNING AND NOT AN ERROR, which is the same trade `missing-js` explains: on a
  first build into a fresh output directory every specifier is missing, because
  the list is what the bundler has not been given yet. So this is a build-time
  answer to `what do I have to bundle`, and the compile it interrupts is the one
  that produced the answer.

  NOBODY CALLS THIS DIRECTLY ANY MORE. clojure.cljs.npm/ensure-js! tries to BUILD
  the missing modules first and then asks this what is left, so on a machine with
  a bundler there is usually nothing here to say. It is still the whole answer
  when there is no bundler, no node_modules or no node - which is the mode this
  compiler shipped in until the build was wired in, and is why this did not move
  into that namespace: what a path says about a file is this namespace's question
  (doc/cljs-npm.md 6)."
  [dir specifiers]
  (let [missing (missing-js dir specifiers)
        seen    (get @reported (str dir) #{})
        fresh   (remove seen missing)]
    (when (seq fresh)
      (swap! reported update (str dir) (fnil into #{}) fresh)
      (binding [*out* *err*]
        (println (str "WARNING: " (count fresh) " JavaScript module"
                      (when (< 1 (count fresh)) "s")
                      " required and not under " (File. (io/file dir) js-dir) ":"))
        (doseq [s fresh]
          (println (str "  " s "  ->  " (js->path s))))
        (println (str "  " js-dir "/ is built by esbuild out of node_modules, and"
                      " clojure.cljs.npm runs it when it can find one. Reaching"
                      " this line means it could not, so each of those has to end"
                      " up at the path beside it, as an ES module, or it is a 404"
                      " when the program loads."))))
    missing))
