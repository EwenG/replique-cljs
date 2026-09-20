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

  Nothing durable records a path - no deps file, no manifest, no load-time ordering
  on the JVM (7.3) - so changing the layout makes an output directory stale rather
  than wrong. It is known here and in runtime.js, and nowhere else."}
  clojure.cljs.output
  (:require [clojure.cljs.goog :as goog]
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

  `required` is any collection of namespace symbols - a whole requires set, goog
  names and ClojureScript names mixed - because that is what its callers have, and
  telling them apart is this function's job rather than theirs.

  Called where a module's imports or a script's requires have just been decided:
  both spell a goog name as a path under this root, and a path that nothing wrote
  is a 404 at load. Cheap to call often - in library mode nothing is converted
  twice (clojure.cljs.goog/written), and in subset mode there are twenty files."
  [dir required]
  (let [names (into [] (comp (filter goog/goog-ns?) (map str) (distinct)) required)]
    (when (seq names)
      (goog/write-goog! dir names))
    dir))
