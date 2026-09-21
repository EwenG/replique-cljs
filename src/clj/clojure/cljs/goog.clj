;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The Closure Library subset, and the rewrite that turns a Closure file
  into an ES module. doc/cljs-compiler.md §5.5.

  cljs.core requires seven goog namespaces. The transitive closure of those seven
  is 42 files and 18,458 lines - MORE THAN cljs.core itself - and it is not evenly
  distributed:

      goog.string    34 files  13,099 lines   for isEmpty, endsWith, contains
      goog.Uri       38 files  16,402 lines   for one instance?
      goog.array      4 files   2,344 lines   for four functions
      goog.object     1 file      709 lines   for six functions
      goog.math.Long  5 files   1,625 lines   for instance? and its methods
      goog.math.Integer 2 files 1,024 lines   likewise
      goog.string.StringBuffer 1 file 101 lines - genuinely used

  goog.string and goog.Uri are big for one reason: both carry HTML escaping, so
  both reach goog.dom.safe and the whole safe-HTML type system, TrustedTypes and
  user-agent sniffing. None of that is on any path cljs.core takes.

  So the rule for this tree is NOT 'shim' and NOT 'replace', which is how §7 asked
  the question. It is:

      SHIP THE FILE VERBATIM WHEN ITS DEPENDENCY CHAIN TERMINATES CHEAPLY.
      WRITE OUR OWN WHEN IT DOES NOT.

  goog.asserts costs three files and stops - so it ships, even though goog.math.Long
  calls it exactly once. goog.string costs thirty-four and does not - so it does
  not, even though what cljs.core wants from it is three lines. The disproportion,
  not the size, is what decides.

  Fourteen files are vendored unmodified from google-closure-library
  0.0-20250515-f04e4c0e, which is the version ClojureScript 1.12.145 itself pins.
  Five are ours: base.js, goog.js, and the three files that would otherwise have
  dragged a chain in - goog/string/string.js, goog/array/array.js,
  goog/uri/uri.js. Each of the three says in its own header what it left out and
  how to undo that.

  ## Not everything here is for cljs.core

  The seven above are what cljs.core reaches. Five more files are in the tree
  because ClojureScript's own test suite names them, and they are here rather than
  reduced because the rule at the top says so - their chain terminates at
  goog.asserts, which was already paid for:

      goog.math         477 lines   goog.math.Vec2 and Vec3 both require it
      goog.math.Coordinate   289
      goog.math.Coordinate3  171
      goog.math.Vec2    320   cljs/import_test.cljs:12
      goog.math.Vec3    331   likewise

  1,588 lines of arithmetic on numbers, with no HTML, no DOM and no user-agent
  sniffing anywhere in them - which is the whole difference between this chain and
  goog.string's.

  ## The rewrite

  A vendored file's BODY IS NEVER TOUCHED. What changes is its header, and the
  grammar there is closed - five forms, listed in `parse` - so anything else is
  refused rather than passed through.

      goog.provide('goog.reflect');        kept: goog.provide is a real function
                                           in base.js, not a compiler directive
      goog.require('goog.reflect');        becomes an ES import
      const x = goog.require('goog.foo');  becomes an import plus const x = goog.foo
      goog.module('goog.object');          removed; the module's exports are
      goog.module.declareLegacyNamespace()   assigned to goog.object at the end

  EXACTLY ONE LINE IS ADDED AT THE TOP, and it carries every import. So line N of a
  vendored file is line N+1 of the emitted one, which is what a stack trace through
  goog.math.Long has to be read against. One more line is added at the BOTTOM, after
  everything: goog.expose for a module, goog.register for a provide.

  Load order rides on the ES imports, exactly as it rode on goog.require under the
  debug loader.

  ## Why a goog namespace needs nothing from the analyzer

  base.js registers each provide into $CLJS.namespaces, so `goog.object` IS the
  object $ns(\"goog.object\") returns - and a goog var is then a property of a
  namespace object like every other var (§5.2). (:require [goog.object :as gobject])
  and gobject/get therefore need no new case anywhere: the import runs before the
  prologue, so the registration always wins.

  ## Coexisting with a Closure Library the project already has

  Three surfaces could collide with a real Closure the user's project bundles, and
  only one of them was ever theirs:

    globalThis.goog   THEIRS. Ours is on $CLJS - see base.js. Nothing needed it to
                      be global, and that one word is the whole isolation.
    the output path   OURS, and it is `out-dir` = goog-subset rather than goog,
                      because a real Closure unpacks as goog/ and closure/goog/.
    the namespace     OURS, and deliberately NOT renamed. Renaming would let one
                      project hold two goog.strings - ours for cljs.core and the
                      real one for user code - which is worse than being made to
                      choose, and would cost a patch to ~80 call sites in a
                      core.cljs we want to re-vendor with cp.

  Keeping the name is what makes `check-var!` possible, which is the better prize:
  see `reduced-vars`.

  ## The other tree: a Closure Library the project has

  Everything above is the SUBSET, and the subset is a fallback rather than the only
  answer. A vendored file's body is upstream's, byte for byte; what makes it loadable
  here is `convert` and base.js. So a whole Closure Library on the classpath is the
  same kind of input, and `*closure-library*` is the choice between them.

  What differs between the two is where the index comes from - our own files, parsed,
  or the library's `goog/deps.js`, which is its own statement of what it has and what
  requires what. What does not differ is anything else: the same converter, the same
  output layout, the same base.js. Two files stay ours in both modes, base.js and
  goog.js, and the reductions and the placeholder stop applying in the second,
  because nothing there is reduced.

  THE CHOICE IS NOT A DETECTION. Anything that depends on ClojureScript has a Closure
  Library on its classpath, and a compiler that silently used it would compile a
  project against a different Closure than it compiled against yesterday. The error
  for a name the subset lacks says which answer is true of the classpath in front of
  it - see `get-real-closure`.

  Three things the library does that the subset never did, and each is one rule:
  it requireTypes (a binding, no import, nothing to write); it destructures a
  require (the same import, a pattern where the name was); and 690 of its 781
  modules declare no legacy namespace (which decided whether Closure made a global,
  and decides nothing here, because a goog namespace is a property of the goog
  object either way). A fourth is `canonical`: 193 of its files provide more than
  one name, and only one of them can hold the body.

  ## A third place, and it needs no list at all

  transit-js ships com/cognitect/transit.js in a jar; shadow-cljs ships
  shadow/loader.js. Neither is the Closure Library and neither declares itself
  anywhere, and both are the same kind of input as everything above - a Closure
  header over a body. What was missing for them was never the converter; it was
  somewhere to look, because a jar that is neither of the two trees has no list and
  publishes no deps.js.

  ClojureScript scans the whole classpath for .js files and reads their provide
  lines. This does not, because the path is DERIVABLE FROM THE NAME: dots to
  slashes, which is the rule `ns->path` and clojure.cljs.output/ns->path already
  state and the rule those jars are laid out by. So one io/resource replaces a scan.
  See `classpath-entry`, and doc/cljs-compiler.md 5.52.

  Closure's own tree is the exception that proves it - goog.asserts is
  asserts/asserts.js, and no rule connects those - which is exactly why the subset
  needs `files` and the library needs deps.js.

  ## Not here

  The index for the subset is built by parsing the tree, so a provide is declared in
  one place - the file that provides it. `files` is the one list that has to be
  maintained, and it is paths only: a jar has no directory to enumerate. In library
  mode there is no such list, because deps.js is one; on the classpath there is none
  because the name is the path."}
  clojure.cljs.goog
  (:require [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io File]))

(def root
  "Where the subset lives on the classpath, beside runtime.js and for the same
  reason: src/clj is an unfiltered resource root, so these files ship in the jar
  verbatim.

  Under clojure/cljs, so it cannot collide with anything: this is a path inside our
  own jar. `out-dir` is the one that has to be defensive."
  "clojure/cljs/goog")

;; --- the two places a Closure file can come from -----------------------------
;;
;; The subset above and a whole Closure Library on the classpath are not two
;; mechanisms. A vendored file's body is upstream's, byte for byte, and what makes
;; it loadable here is `convert` plus base.js - so the library is the same kind of
;; input, and all that differs is where the index comes from and how many files
;; there are to choose among.
;;
;; WHICH ONE IS IN USE IS A CHOICE, NOT A DETECTION. A project that happens to have
;; google-closure-library on its classpath - which anything depending on
;; ClojureScript does - must not silently start compiling against a different
;; Closure than the one it compiled against yesterday. The default is the subset,
;; which is what makes this compiler work with no dependency at all; the option is
;; what a project like one using goog.style or goog.net turns on, and the error for
;; a name the subset lacks says so when the library is there to be turned on.

(def library-root
  "Where a Closure Library unpacks on the classpath: goog/base.js, goog/deps.js,
  goog/object/object.js. Both the Maven artifact (org.clojure/google-closure-library)
  and the npm package lay the tree out this way."
  "goog")

(def deps-name
  "The Closure Library's own index, at the root of its tree: one
  goog.addDependency(path, provides, requires, opts) per file, for every file it
  ships. It is what `library-index` reads instead of walking a directory - which a
  jar has none of - and it is the library's own statement of its graph."
  "deps.js")

(defn library-available?
  "Is a Closure Library on the classpath? Asked only to say so in an error - what
  decides which tree is used is `*closure-library*`."
  []
  (some? (io/resource (str library-root "/" deps-name))))

(def ^:dynamic *closure-library*
  "Compile against the Closure Library on the classpath rather than the vendored
  subset.

  False by default, and that default is the promise this namespace's docstring
  makes: a program that requires only what cljs.core requires compiles with nothing
  on the classpath but this jar.

  True is for a project whose own code, or whose libraries, reach past the subset -
  goog.style, goog.net.XhrIo, goog.date, none of which are here and all of which
  are in the library. Then the whole tree comes from there, and the three reductions
  and the one placeholder below stop applying, because the real files are the ones
  being converted.

  Whole-tree rather than file-by-file: a program holding goog.string from one
  Closure release and goog.date from another is a program nobody can reason about,
  and the two files are written to assume they ship together. Two files stay ours
  in both modes - base.js, which is the goog object and our isolation from a page's
  own Closure, and goog.js, which makes the bare name `goog` requirable.

  Set at a REPL or a build with `use-closure-library!`, or bound around a
  compilation; the tests bind it, since a test that changed it for the process
  would decide the mode of every test after it."
  false)

(defn library-option
  "What `*closure-library*` should be for a compilation run with `opts`.

  The option when it says, and what is already in force when it does not - so a
  caller that never mentions it gets the process-wide answer and a caller that does
  gets its own. ONE OUTPUT DIRECTORY WANTS ONE ANSWER: the tree under it is written
  by whichever mode compiled into it, and two modes would leave it holding files
  from two different Closures."
  [opts]
  (if (contains? opts :closure-library)
    (boolean (:closure-library opts))
    *closure-library*))

(defn use-closure-library!
  "Set `*closure-library*` for this process. A build or a REPL calls this once from
  its options; nothing calls it per compilation."
  [on?]
  (alter-var-root #'*closure-library* (constantly (boolean on?)))
  nil)

(def out-dir
  "The directory the subset is written to under an output root, and deliberately
  NOT `goog`.

  The same defensiveness `ns-dir` exists for, against a different collision. A real
  Closure Library unpacks as `goog/`, and as `closure/goog/` in Google's own tree,
  so an output directory that also has a build tool dropping Closure into it would
  land two different libraries on one path. Neither name is available, and the
  awkwardness of this one is the point - nothing mistakes `goog-subset` for the
  Closure Library, which is the whole message of doc/cljs-compiler.md 5.5.

  Nothing durable records it, so changing it makes an output directory stale rather
  than wrong - see clojure.cljs.output."
  "goog-subset")

(def js-out-dir
  "Where a Closure file found on the CLASSPATH is written under an output root, and
  it is `ns` - the very directory an emitted ClojureScript module goes in, at the
  same dots-to-slashes path.

  ONE TREE, because these are namespaces by the same rule everything in it is. The
  converted file registers its provide into $CLJS.namespaces exactly as an emitted
  module registers its own, so $ns(\"com.cognitect.transit\") answers for both; a
  module importing one spells the same relative path it spells for the other; and
  runtime.js's urlFor needs no third branch, because the one it already has for a
  name that is not goog's computes ./ns/com/cognitect/transit.js and is right.

  The goog tree is the one that has to be kept apart, and `out-dir` says why: a real
  Closure Library unpacks as goog/, and a name in it is reserved from ClojureScript
  so nothing emitted can collide. A classpath Closure name is reserved from nothing -
  com.cognitect.transit could have been written in ClojureScript, and if it had been,
  the file would be at this very path. That is not a collision waiting to happen; it
  is the same namespace arriving by the other door, and only one of the two doors is
  ever open (see classpath-entry, and the driver's ensure!, which looks for the
  source first).

  Spelled here rather than read from clojure.cljs.output/ns-dir because that
  namespace requires this one. The two state one rule twice, as runtime.js states it
  a third time, and goog-test holds all of them to it."
  "ns")

(def base
  "The one file that is already an ES module, and so the one file the rewrite
  copies rather than converts. It is also the only file in the tree that imports
  runtime.js."
  "base.js")

(def files
  "Every file in the subset, as a path under `root`, and under `out-dir` in an
  output tree - the two trees are the same shape, so a specifier computed over one
  is correct in the other.

  A list rather than a directory scan: a classpath entry may be a jar, and a jar
  has no directory to walk. Adding a file to the tree means adding a line here;
  everything else about it - what it provides, what it requires - is read out of
  the file itself.

  Ordering is irrelevant. The ES imports carry the load order."
  ["base.js"
   "goog.js"
   "reflect/reflect.js"
   "debug/error.js"
   "dom/nodetype.js"
   "asserts/asserts.js"
   "math/long.js"
   "math/integer.js"
   "math/math.js"
   "math/coordinate.js"
   "math/coordinate3.js"
   "math/vec2.js"
   "math/vec3.js"
   "object/object.js"
   "string/internal.js"
   "string/string.js"
   "string/stringformat.js"
   "string/stringbuffer.js"
   "array/array.js"
   "uri/uri.js"])

(defn goog-ns?
  "Is `ns-sym` a name in the goog tree? SYNTACTIC, and deliberately so: it must be
  decidable by runtime.js's urlFor, which has a name and nothing else.

  It also reserves the whole `goog.` prefix from ClojureScript, as ClojureScript
  reserves it - a namespace called goog.foo cannot be compiled here, and that is
  the right answer rather than a limitation.

  Says nothing about whether we HAVE it; `known?` is that question."
  [ns-sym]
  (let [s (str ns-sym)]
    (or (= "goog" s) (str/starts-with? s "goog."))))

(defn source
  "The text of one Closure file, read from `from` - `root` for one of ours, or
  `library-root` for one of the library's.

  Read on each call, like runtime.js: a file on disk that someone edits should not
  need a restart to take effect. The one-argument arity reads from the subset,
  which is where the two files that are ours in both modes live."
  ([path] (source root path))
  ([from path]
   (let [res (if from (str from "/" path) path)]
     (or (some-> (io/resource res) slurp)
         (throw (ex-info (str "The Closure tree is missing " path
                              ". Expected it on the classpath at " res ".")
                         {:path path :root from}))))))

;; --- reading a Closure header -----------------------------------------------

(def ^:private eol
  "What may follow a header line: nothing, or a trailing line comment.

  `const GoogPromise = goog.requireType('goog.Promise');  // for the type reference.`
  is a real line of goog/promise/promise.js, and a grammar that ended at the
  semicolon refused the file rather than reading it."
  "\\s*(?://.*)?$")

(def ^:private q
  "A Closure name where a header line quotes one.

  EITHER QUOTE. The Closure Library and this subset write single quotes; transit-js
  writes double ones, on every line of every file it ships. Both are JavaScript
  string literals and Closure's own parser reads both, so a grammar that insisted on
  one was refusing a real Closure file over its author's spacing habits - which is
  what `parse` refuses things FOR, and this is not one of them.

  Not a general string literal: no escapes, and the closing quote need not match the
  opening one. A Closure name is a dotted JavaScript identifier, so anything either
  of those would buy cannot appear in one."
  "['\"]([^'\"]+)['\"]")

(def ^:private provide-re  (re-pattern (str "^goog\\.provide\\(" q "\\);" eol)))
(def ^:private module-re   (re-pattern (str "^goog\\.module\\(" q "\\);" eol)))
(def ^:private legacy-re   (re-pattern (str "^goog\\.module\\.declareLegacyNamespace\\(\\);" eol)))
(def ^:private require-re  (re-pattern (str "^goog\\.require\\(" q "\\);" eol)))
(def ^:private bound-re    (re-pattern (str "^(?:const|let|var)\\s+(\\w+)\\s*=\\s*goog\\.require\\(" q "\\);" eol)))

;; Three more shapes, none of which the subset uses and all of which the library
;; does - 337 of its files requireType, 80 destructure a require, and it was the
;; refusal of those that made "vendor it or reduce it" the only way past them.
;;
;; A DESTRUCTURING BINDING is the same thing as a bound require with a pattern
;; where the name was: const {a, b} = goog.require('goog.foo') binds two of
;; goog.foo's exports. It was refused here rather than passed through because
;; emitting it unchanged would call a goog.require that base.js does not have; now
;; it is emitted as the import plus const {a, b} = goog.foo, which is what it means.
;;
;; A requireType IS NOT A LOAD. It says this file names that type in a comment, and
;; Closure's own loader does not fetch it either. So it contributes a binding when
;; it has one - so the annotations still parse as JavaScript - and no import, and
;; nothing to the closure of files that have to be written.
(def ^:private pattern-re  (re-pattern (str "^(?:const|let|var)\\s+(\\{[^}]*\\})\\s*=\\s*goog\\.require\\(" q "\\);" eol)))
(def ^:private type-re     (re-pattern (str "^goog\\.requireType\\(" q "\\);" eol)))
(def ^:private bound-type-re
  (re-pattern (str "^(?:const|let|var)\\s+(\\w+|\\{[^}]*\\})\\s*=\\s*goog\\.requireType\\(" q "\\);" eol)))

(def ^:private header-call-re
  "A line that is TRYING to be one of the five forms: it calls goog.provide,
  goog.module or goog.require outside a comment. If it is not one of the five it is
  refused, because passing it through would put a call to a function base.js does
  not have into the output, to fail at load with something far less informative
  than this.

  Comments are excluded rather than matched loosely, and they have to be: several
  vendored files mention goog.require in a docstring, and goog/string/internal.js
  is full of `@see goog.string.\u2026` lines. A line inside a comment is body."
  #"goog\.(?:provide|module|require|requireType)\(")

(defn- comment-line?
  "Is this line inside a comment? The three shapes Closure's headers are written
  around - a block comment's continuation, its opener, and a line comment."
  [line]
  (let [t (str/trim line)]
    (or (str/starts-with? t "*") (str/starts-with? t "//") (str/starts-with? t "/*"))))

(defn parse
  "The header of one Closure file: what it provides, what it requires, and which
  of the two shapes it is.

  A goog.require inside a COMMENT is body and is left alone - internal.js has
  several in its docstrings. A goog.require anywhere else that is not one of the
  shapes below is refused rather than passed through, which is what catches
  something no rule here spells out - a goog.forwardDeclare, say - instead of
  emitting a call to a function base.js does not have.

  A require is {:name n}, plus :binding when it binds one and :type-only? when it
  is a requireType."
  [src]
  (reduce
   (fn [acc line]
     (condp (fn [re s] (re-matches re s)) line
       provide-re :>> (fn [[_ n]] (-> acc (update :provides conj n) (assoc :kind :provide)))
       module-re  :>> (fn [[_ n]] (-> acc (update :provides conj n) (assoc :kind :module)))
       legacy-re  :>> (fn [_]     (assoc acc :legacy? true))
       require-re :>> (fn [[_ n]] (update acc :requires conj {:name n}))
       bound-re   :>> (fn [[_ b n]] (update acc :requires conj {:name n :binding b}))
       pattern-re :>> (fn [[_ b n]] (update acc :requires conj {:name n :binding b}))
       type-re    :>> (fn [[_ n]] (update acc :requires conj {:name n :type-only? true}))
       bound-type-re :>> (fn [[_ b n]] (update acc :requires
                                               conj {:name n :binding b :type-only? true}))
       (if (and (re-find header-call-re line) (not (comment-line? line)))
         (throw (ex-info (str "Unrecognised Closure header line: " (pr-str line)
                              ". clojure.cljs.goog/parse handles the shapes listed"
                              " beside it and refuses anything else rather than"
                              " emitting it - see the namespace docstring.")
                         {:line line}))
         acc)))
   {:provides [] :requires [] :kind nil :legacy? false}
   (str/split-lines src)))

(defn- subset-index
  "provide name -> {:root :path :requires}, over the whole subset. Built by reading
  the tree rather than declared, so the file that provides a name is the only place
  that says so.

  Refuses two files providing one name: which one an import meant would then
  depend on the order `files` happens to be in."
  []
  (reduce (fn [m path]
            (let [{:keys [provides requires]} (parse (source path))]
              (reduce (fn [m n]
                        (when-let [prev (get m n)]
                          (throw (ex-info (str "Two files in the Closure subset provide "
                                               n ": " (:path prev) " and " path ".")
                                          {:provide n :files [(:path prev) path]})))
                        (assoc m n {:root root :path path
                                    :requires requires :provides provides}))
                      m
                      provides)))
          {}
          (remove #{base} files)))

(def ^:private dep-re
  "One goog.addDependency line of deps.js: the path, the provides, the requires.
  The fourth argument - {'lang': 'es6', 'module': 'goog'} - says nothing this needs;
  what a file is is read off the file, by `parse`, as it is for the subset."
  #"^goog\.addDependency\('([^']*)',\s*\[([^\]]*)\],\s*\[([^\]]*)\]")

(defn- quoted-names
  "The names in a deps.js list: 'goog.a', 'goog.b' -> (\"goog.a\" \"goog.b\")."
  [s]
  (map second (re-seq #"'([^']*)'" s)))

(def ^:private library-cache
  "The parsed deps.js, kept. A jar does not change under a running process, and
  this is 1,600 entries that `known?` would otherwise reparse on every goog require
  the analyzer resolves. The subset is not cached for the reason `source` is not:
  those files are ours and someone may be editing them."
  (atom nil))

(defn- library-index
  "provide name -> {:root :path :requires}, read from the library's own deps.js.

  The requires come from deps.js rather than from the files, which is the one place
  this departs from 'the file that provides a name is the only place that says so' -
  and it is the library's own statement of its graph, published for exactly this
  purpose. `convert` still reads every file it converts and still refuses a require
  the index cannot resolve, so the two disagreeing is caught rather than assumed
  away.

  goog.js is ours in both modes and is spliced in here, because the library has no
  file that provides the bare name `goog` - base.js IS that name there, and base.js
  is ours."
  []
  (or @library-cache
      (let [src   (source library-root deps-name)
            index (reduce (fn [m line]
                            (if-let [[_ path provides requires] (re-find dep-re line)]
                              (let [provides (vec (quoted-names provides))
                                    entry    {:root     library-root
                                              :path     path
                                              :provides provides
                                              :requires (mapv (fn [r] {:name r})
                                                              (quoted-names requires))}]
                                (reduce #(assoc %1 %2 entry) m provides))
                              m))
                          {}
                          (str/split-lines src))
            ours  (:provides (parse (source "goog.js")))]
        (reset! library-cache
                (reduce #(assoc %1 %2 {:root root :path "goog.js"
                                       :requires [] :provides (vec ours)})
                        index ours)))))

(defn index
  "provide name -> {:root :path :requires} for whichever tree is in use.

  One shape, two sources: the subset parsed out of our own files, or the library's
  deps.js. Everything downstream - what is known, what a file requires, what has to
  be written - reads this and needs no case of its own."
  []
  (if *closure-library* (library-index) (subset-index)))

(defn known?
  "Is `ns-sym` a goog name the tree in use actually provides?

  `goog` is in here like any other name, because goog.js provides it - see that
  file for why it exists when base.js is the goog object already."
  [ns-sym]
  (contains? (index) (str ns-sym)))

;; --- the third place a Closure file can come from: anywhere on the classpath --
;;
;; transit-js ships com/cognitect/transit.js in a jar, with goog.provide at the top
;; and nine more files under it; shadow-cljs ships shadow/loader.js, a goog.module
;; that declares a legacy namespace. Neither is the Closure Library and neither is in
;; any list here, and both are the same kind of input as everything above - a Closure
;; header over a body, which `convert` turns into an ES module and base.js makes
;; loadable.
;;
;; WHAT WAS MISSING WAS NEVER THE MACHINERY. It was the index: `subset-index` walks a
;; list we maintain, `library-index` reads a deps.js the library publishes, and a jar
;; that is neither has no list and no deps.js to read. ClojureScript's answer is to
;; SCAN - every classpath entry, every .js in it, read each one's provide line, and
;; build a map. Ours is not, and the reason is the reason doc/cljs-output-layout.md
;; 7.3 gives for everything else here:
;;
;;     THE PATH IS DERIVABLE FROM THE NAME, so there is nothing to index.
;;
;; com.cognitect.transit is at com/cognitect/transit.js, shadow.loader at
;; shadow/loader.js, and com.cognitect.transit.impl.decoder at
;; com/cognitect/transit/impl/decoder.js - dots to slashes, which is the same rule
;; `ns->path`, clojure.cljs.output/ns->path and runtime.js's urlFor already state,
;; and the rule these libraries lay their jars out by because it is the one Closure's
;; own debug loader resolves a name with. So a lookup replaces a scan: one
;; io/resource for a name we are asked about, instead of several hundred jars read
;; ahead of being asked.
;;
;; The subset is the exception that proves it. Closure's own tree is NOT derivable -
;; goog.asserts is asserts/asserts.js, goog.debug.Error is debug/error.js - which is
;; exactly why those two need a list and a deps.js, and why the subset is written OUT
;; at derived names rather than at Closure's own.

(defn js-path
  "Where a Closure name is looked for on the classpath: com.cognitect.transit ->
  com/cognitect/transit.js.

  Dots to slashes and nothing else. NO MUNGING, unlike a ClojureScript source path:
  a Closure name is a dotted JavaScript identifier - it is evaluated as a property
  path by the library's own body - so there is no hyphen for a munge to map, and a
  name carrying one is a name no Closure file can provide."
  [provide]
  (str (str/replace (str provide) "." "/") ".js"))

(def ^:private classpath-cache
  "provide name -> its entry, or ::none. Both directions are kept, and the negative
  half is the one that matters: the analyzer asks whether a name is a Closure file
  for every prefix it cannot otherwise place, and Math/floor must not cost a
  classpath walk twice.

  Cached for `library-cache`'s reason and with its limit - a jar does not change
  under a running process. A .js a developer is EDITING is the case this gets wrong,
  and it gets it wrong once per name per JVM."
  (atom {}))

(defn- claims?
  "Does `src` open by providing `provide`? The cheap half of the question, asked
  before `parse`.

  IT IS ASKED FIRST ON PURPOSE. `parse` is strict - a goog.require it does not
  recognise is refused rather than passed through - and that strictness is right for
  a file we are about to convert and wrong for a file that merely happens to sit at
  a path we probed. Anything on the classpath can be at com/example/thing.js, and a
  compiler that threw while deciding whether a namespace was JavaScript at all would
  be refusing files it was never going to touch. So: does this file say it is the
  thing we asked for? Only then is it ours to be strict about."
  [src provide]
  (boolean (some #(or (= [provide] (rest (re-matches provide-re %)))
                      (= [provide] (rest (re-matches module-re %))))
                 (str/split-lines src))))

(defn classpath-entry
  "The index entry for a Closure-style JavaScript file on the classpath providing
  `provide`, or nil when there is none.

  The same shape every other index hands back, so `convert`, `closure` and
  `write-goog!` need no case of their own: {:root :path :provides :requires}, with
  :root nil because the path is already the resource's whole name.

  THE FILE MUST CLAIM THE NAME. A file at the derived path that provides something
  else, or that is not a Closure file at all - an emitted ES module, a bundle, a
  plain script - is not an answer, and nil here is what lets a ClojureScript
  namespace called com.cognitect.transit go on being one. That check is also what
  keeps this safe to ask about EVERY name: the question is not `is there a .js
  there`, it is `is there a Closure file there that says it is this`.

  A goog name is never one of these. Its tree is chosen - subset or library - and
  a third answer found by probing the classpath would be exactly the silent
  substitution `*closure-library*` exists to prevent."
  [provide]
  (let [provide (str provide)
        cached  (get @classpath-cache provide ::miss)]
    (if (not= ::miss cached)
      (when-not (= ::none cached) cached)
      (let [entry (when-not (goog-ns? provide)
                    (let [path (js-path provide)]
                      (when-let [src (some-> (io/resource path) slurp)]
                        (when (claims? src provide)
                          (let [{:keys [provides requires]} (parse src)]
                            {:root nil :path path
                             :provides provides :requires requires})))))]
        (swap! classpath-cache assoc provide (or entry ::none))
        entry))))

(defn entry
  "The Closure file that provides `name`, from `idx` or from the classpath.

  ONE LOOKUP FOR BOTH TREES. `idx` is whichever goog index is in use and is a map
  because it can be enumerated; the classpath cannot, so it is asked by name. The
  goog one is asked first: a name in that tree is answered by the tree that was
  chosen, never by something a jar happened to put at the same path."
  [idx name]
  (or (get idx name) (classpath-entry name)))

(defn js-ns?
  "Is `ns-sym` a Closure-style JavaScript file on the classpath rather than a
  ClojureScript namespace?

  What the analyzer asks to decide that (:require [com.cognitect.transit :as t]) is
  a require of JavaScript - no vars to refer, nothing to compile, an import of a
  file this converts. Its callers ask it LAST, after a namespace that was actually
  declared has already answered, so a .cljs always wins over a .js of the same name
  and the ambiguity never has to be resolved here."
  [ns-sym]
  (some? (classpath-entry ns-sym)))

(defn closure-ns?
  "Is `ns-sym` a Closure namespace - one whose implementation is a JavaScript file
  this compiler CONVERTS rather than a ClojureScript file it compiles?

  Two kinds, and after this line almost nothing downstream cares which: a goog name,
  which is syntactic and reserved, or a file on the classpath at the name's own path.
  Both end up as an ES module registered into $CLJS.namespaces, so both are reached
  by $ns(\"the.name\") and a var in either is a property of that object."
  [ns-sym]
  (or (goog-ns? ns-sym) (js-ns? ns-sym)))

(defn provided?
  "Is `name` a Closure namespace this compilation can actually reach? `known?`
  widened to the classpath, and the question every place that would have asked
  `known?` about a name that might not be goog's should ask instead."
  [name]
  (or (known? name) (some? (classpath-entry name))))

;; --- what the reductions actually provide -----------------------------------

(def reduced-vars
  "The three namespaces this tree REDUCES, and every var each one has.

  These names already mean something. The real goog.string has 71 functions and the
  real goog.array 65; ours have fifteen and eleven, chosen because they are what
  cljs.core, clojure.string, cljs.pprint and cljs.reader call. A user who requires
  goog.string and reaches for `format` is asking for a function that exists in the
  Closure Library and does not exist here.

  Without this table that is a runtime TypeError, in their code, looking like their
  bug - which is exactly the M5 failure mode (doc/cljs-compiler.md 8: bugs surface as
  wrong answers rather than errors). With it, it is an analysis error naming the
  reduction. See `check-var!`.

  Only the reductions are listed. The nine vendored files are COMPLETE, so there is
  nothing to check them against and a var they do not have is the Closure Library's
  business, not ours. That asymmetry is the point: we check what we truncated."
  {"goog.string" #{"startsWith" "endsWith" "contains" "trim" "trimLeft" "trimRight"
                   "isEmptyOrWhitespace" "isEmpty" "regExpEscape" "makeSafe"
                   "capitalize" "isNumeric" "isUnicodeChar" "urlEncode"
                   "urlDecode"}
   "goog.array"  #{"defaultCompare" "sort" "toArray" "clone" "stableSort" "shuffle"
                   "slice" "splice" "insertArrayAt" "isEmpty" "removeAt"}})

(def deferred
  "Namespaces that are a placeholder and nothing else, so EVERY var in them is
  missing rather than some. goog.Uri is 38 files for one instance? - see
  goog/uri/uri.js and doc/cljs-compiler.md 7."
  {"goog.Uri" (str "goog.Uri is a placeholder: its 38-file dependency chain was"
                   " deferred because cljs.core uses it for one instance? test."
                   " uri? still answers - false, correctly, while nothing can"
                   " construct one - but nothing else about goog.Uri works.")})

(defn get-real-closure
  "What to do about a goog name this tree does not have, as a sentence to end an
  error with. Two answers, and which one is true is a fact about the classpath:
  the library is there and was not asked for, or it is not there at all.

  Said here once, because three errors in two namespaces end this way and a reader
  hitting any of them wants the same next step."
  []
  (if (library-available?)
    (str "a Closure Library is on your classpath - compile with :closure-library"
         " true (or call clojure.cljs.goog/use-closure-library!) to use it instead"
         " of the vendored subset.")
    (str "put a Closure Library on the classpath"
         " (org.clojure/google-closure-library) and compile with :closure-library"
         " true, or vendor what you need into clojure/cljs/goog and add it to"
         " clojure.cljs.goog/files.")))

(defn check-var!
  "Refuse `var-name` in the goog namespace `ns-name` if this tree is known not to
  have it. Returns nil when there is nothing to say, which is the common case: a
  namespace we vendored whole is not our business to police.

  Called by the analyzer when it resolves a goog var - which is the only place that
  knows a name was WRITTEN, as opposed to merely being absent from a JavaScript
  object nobody can enumerate at compile time.

  Nothing to say in library mode, and that is not a gap: the reductions and the
  placeholder are things WE truncated, and in that mode nothing is truncated. The
  file being converted is the real one, so a var it does not have is the Closure
  Library's business, which is the same asymmetry the vendored files already have."
  [ns-name var-name]
  (when-not *closure-library*
    (when-let [msg (get deferred ns-name)]
      (throw (ex-info (str ns-name "/" var-name " - " msg) {:ns ns-name :var var-name})))
    (when-let [have (get reduced-vars ns-name)]
      (when-not (contains? have var-name)
        (throw (ex-info (str ns-name "/" var-name " is not in the Closure subset. "
                             ns-name " here is a " (count have) "-function reduction ("
                             (str/join ", " (sort have)) ") - the real one was left out"
                             " because its dependency chain does not terminate cheaply,"
                             " which doc/cljs-compiler.md 5.5 explains. To get the real"
                             " one: " (get-real-closure))
                        {:ns ns-name :var var-name :have have}))))))

(defn declared-vars
  "The vars a reduction's FILE actually assigns, read back out of it: every
  `goog.string.foo =` at the start of a line. What `reduced-vars` is checked against,
  so the table cannot drift from the code it describes."
  [ns-name path]
  (into #{}
        (keep #(second (re-matches
                        (re-pattern (str "^" (str/replace ns-name "." "\\.")
                                         "\\.(\\w+) = .*"))
                        %)))
        (str/split-lines (source path))))

;; --- the rewrite ------------------------------------------------------------

(defn ns->path
  "The output file for a goog namespace, relative to the OUTPUT root:
  goog.math.Long -> goog-subset/goog/math/Long.js.

  Dots to slashes - the same rule clojure.cljs.output/ns->path uses for a
  ClojureScript namespace, under a different root - and that is the whole reason
  the output tree does not mirror Closure's own. Closure's layout is not derivable
  from the name (goog.asserts is asserts/asserts.js, goog.debug.Error is
  debug/error.js, and no rule connects them), and a path that is not derivable has
  to be RECORDED - a manifest, which doc/cljs-output-layout.md §7.3 rules out,
  because $CLJS.require must compute a URL from a name with nothing to ask the JVM.

  Injective because dots-to-slashes is. It puts a file goog/string.js beside a
  directory goog/string/, which every filesystem allows.

  Sound only because each file in this subset provides exactly ONE name - checked
  by `index`, which refuses two files providing one name, and by goog-test.

  A CLASSPATH CLOSURE FILE GOES UNDER `ns` INSTEAD - see js-out-dir - and the rule
  inside that tree is this same one for the third time."
  [provide]
  (str (if (goog-ns? provide) out-dir js-out-dir)
       "/" (str/replace provide "." "/") ".js"))

(def base-path
  "base.js sits at the root of the output subtree, as runtime.js does at the root of
  the output. It provides nothing, so `ns->path` has no name to work from - and it
  needs none, being the one file everything else imports rather than requires."
  (str out-dir "/" base))



(defn- relative
  "How the file at `from` names the file at `to`, both relative to the OUTPUT root.
  The same rule as clojure.cljs.output/specifier and for the same reason - a
  relative specifier is the only form node's resolver and a browser's URL resolver
  read alike."
  [from to]
  (let [from-dirs (butlast (str/split from #"/"))
        to-parts  (str/split to #"/")
        to-dirs   (butlast to-parts)
        shared    (count (take-while true? (map = from-dirs to-dirs)))
        up        (repeat (- (count from-dirs) shared) "..")
        path      (str/join "/" (concat up (drop shared to-dirs) [(last to-parts)]))]
    (if (str/starts-with? path "..") path (str "./" path))))

(def ^:private header-res
  "Every line shape `parse` consumes, so `convert` blanks exactly what it read.
  goog.provide is NOT here: it is a real function in base.js and the body may be a
  class whose name it declares, so the line stays."
  [module-re legacy-re require-re bound-re pattern-re type-re bound-type-re])

(defn canonical
  "The provide a file is WRITTEN under, when it provides more than one name.

  193 of the library's 1,609 entries provide several - a namespace and the nested
  names under it, goog.editor.range and goog.editor.range.Point out of one file.
  `ns->path` is a pure function of a NAME, because runtime.js computes a URL from
  one with nothing to ask the JVM (doc/cljs-output-layout.md 7.3), so those two
  names are two paths and only one of them can hold the body. The first provide is
  it; the others get `stub`.

  The first rather than the shortest, because the order is the file's own and a
  rule that sorts is a rule that can disagree with what the file meant."
  [entry]
  (first (:provides entry)))

(defn stub
  "The file written at a provide that is not its file's canonical one: an import of
  the file that is, and nothing else.

  One line rather than a second copy of the body, which would run it twice - and
  the body registers every name it provides, so importing it is all this has to do.
  `ns->path` stays a pure function of a name, which is the constraint this exists
  to satisfy."
  [provide this]
  (str "import \"" (relative (ns->path provide) (ns->path (canonical this))) "\";\n"))

(defn convert
  "One Closure file as an ES module.

  `provide` names it - its canonical one, see `canonical` - and `idx` says where its
  file is. base.js is not converted: it is already a module, and it is what the
  others import.

  The output is the input with its header lines blanked, ONE line added at the top
  carrying every import, and ONE at the end - exposing a module's exports under its
  name, or registering what a provide file provided. Blanked rather than deleted so
  that the body keeps its shape; the single line at the top means line N in the
  source file is line N+1 here.

  A goog.module IS EXPOSED WHETHER OR NOT IT DECLARES A LEGACY NAMESPACE. Under
  Closure that declaration decides whether a global is created, and a module without
  one is reached only through the const its requirer binds. Here every namespace is
  a property of the goog object either way - that is what goog.expose does, and what
  makes (:require [goog.x :as y]) need no case in the analyzer - so the distinction
  has nothing left to decide. It has to be this way for the library, where 781 files
  are modules and 91 declare a legacy name."
  [provide idx]
  (let [{:keys [root path] :as this} (entry idx provide)
        src      (source root path)
        {:keys [kind provides requires]} (parse src)
        _        (when-not kind
                   (throw (ex-info (str path " has neither goog.provide nor"
                                        " goog.module. Every file must declare what"
                                        " it provides - that is how the index is"
                                        " built.")
                                   {:path path})))
        _        (doseq [{n :name t :type-only?} requires]
                   (when-not (or t (entry idx n))
                     (throw (ex-info (str path " requires " n ", which no file in the"
                                          " Closure tree in use provides. "
                                          (get-real-closure))
                                     {:path path :require n}))))
        here     (ns->path provide)
        ;; A requireType is not a load: it says this file names that type in a
        ;; comment, and Closure's own loader does not fetch it either.
        loads    (remove :type-only? requires)
        imports  (into [(str "import { goog } from \"" (relative here base-path) "\";")]
                       (map (fn [{:keys [name]}]
                              (str "import \"" (relative here (ns->path name)) "\";")))
                       loads)
        ;; THE ROOT SEGMENT OF A NAME THAT IS NOT GOOG'S, bound so the body can
        ;; name it. transit.js opens `var transit = com.cognitect.transit;` and
        ;; means the object its own goog.provide made - under Closure's loader
        ;; that object is globalThis.com, because provide walks the global, and
        ;; `com` is then a free variable every file in the jar can see.
        ;;
        ;; Here it is not global. base.js hangs a provide off goog.roots_ instead,
        ;; which is the same isolation the goog object itself gets and for the same
        ;; reason - a page may hold a real Closure, and two Closures must not share
        ;; a namespace. So the free variable has to be BOUND, once, at the top of
        ;; the module: const com = goog.root("com").
        ;;
        ;; Every name the file provides or requires contributes its first segment,
        ;; because under Closure every one of them was reachable that way and a
        ;; vendored body may name any of them - a bare goog.require with no binding
        ;; means exactly `I will write this name out`. goog's own is not among them:
        ;; that one arrives as an import, which is where this tree's isolation lives.
        ;;
        ;; goog.root creates what is missing rather than reading what is there, so
        ;; the order of the line does not matter: a file whose only `com` name is the
        ;; one it provides binds it before its own goog.provide runs, and finds the
        ;; same object when it does.
        roots    (into (sorted-set)
                       (comp (remove goog-ns?)
                             (map #(subs % 0 (or (str/index-of % ".") (count %)))))
                       (concat provides (map :name requires)))
        bindings (into (into (if (= kind :module) ["let exports = {};"] [])
                             (map #(str "const " % " = goog.root(\"" % "\");"))
                             roots)
                       (keep (fn [{:keys [name binding]}]
                               (when binding
                                 ;; the provide name IS the expression: goog.asserts
                                 ;; names the object base.js's provide hung off goog.
                                 ;; A destructuring binding reads the same object.
                                 (str "const " binding " = " name ";"))))
                       requires)
        header   (str/join " " (concat imports bindings))
        blank    (fn [line] (if (some #(re-matches % line) header-res) "" line))
        body     (map blank (str/split-lines src))
        ;; the last lines, and every file has at least one. A module's exports have
        ;; to be EXPOSED under its name; a provide file has already assigned whatever
        ;; it provides, but must still be REGISTERED - and registered here rather
        ;; than inside goog.provide, because a provide that ends up holding a class
        ;; has its name replaced by the body it precedes. See base.js.
        ;;
        ;; Every name, not just the canonical one: the file that holds the body is
        ;; the only place the others are ever registered from.
        trailer  (if (= kind :module)
                   [(str "goog.expose('" (first provides) "', exports);")]
                   (mapv #(str "goog.register('" % "');") provides))]
    (when (and (= kind :module) (not= 1 (count provides)))
      (throw (ex-info (str path " is a goog.module providing " (count provides)
                           " names. A module provides exactly one.")
                      {:path path :provides provides})))
    (when-not (= provide (canonical this))
      (throw (ex-info (str provide " is not the canonical provide of " path
                           " - " (canonical this) " is. A file is converted once,"
                           " under the name it is written at; the rest get a stub.")
                      {:path path :provide provide})))
    (str/join "\n" (concat [header] body trailer [""]))))

;; --- writing the tree -------------------------------------------------------

(defn closure
  "`names` and everything they require, transitively, as provide names.

  Follows what a file LOADS, so a requireType is not followed - see `convert`.
  Refuses a name the tree does not have, here rather than at the import it would
  have emitted, because this is where the name is still attached to the thing that
  asked for it.

  A NAME DRAGS IN ITS CANONICAL SIBLING, and that is not tidiness. A program that
  requires goog.debug.entryPointRegistry gets a `stub` at that path, because the
  name its file is written under is goog.debug.EntryPointMonitor - and a stub is an
  import of a file that has to be there. Nothing else would ask for it: the program
  never names it, and no other file requires it."
  [idx names]
  ;; `todo` carries [name who-asked-for-it], and the second half is only ever read
  ;; by the error below - which is the difference between "No such Closure
  ;; namespace: goog.string.Const" and knowing that shadow.loader is what wanted
  ;; it. A name nobody asked for is one the caller named itself, and the message
  ;; says so by leaving the clause out.
  (loop [seen #{} todo (mapv (fn [n] [n nil]) names)]
    (if-let [[n from] (peek todo)]
      (if (seen n)
        (recur seen (pop todo))
        (let [this (or (entry idx n)
                       (throw (ex-info (str "No such Closure namespace: " n
                                            (when from (str ", required by " from))
                                            ". " (get-real-closure))
                                       (cond-> {:provide n} from (assoc :from from)))))]
          (recur (conj seen n)
                 (into (conj (pop todo) [(canonical this) n])
                       (comp (remove :type-only?) (map (fn [r] [(:name r) n])))
                       (:requires this)))))
      seen)))

(def ^:private written
  "What this process has already converted into which directory, as {dir #{provide}}.

  WHAT MAY BE SKIPPED IS WHAT NOBODY IS EDITING, and that asymmetry is `source`'s.
  The subset's twenty files are ours, so one someone edits has to take effect
  without a restart and they are converted on every call. A jar is not edited under
  a running process, so the library's 1,600 and anything found on the classpath are
  converted once per output directory and then remembered - which is what a REPL
  needs, since compile-form calls write-goog! for every form and transit-js alone is
  ten files of it."
  (atom {}))

(defn write-goog!
  "Write into `dir` - an output root - base.js, goog.js, and the transitive closure
  of the goog namespaces `names`, at the paths `ns->path` gives.

  NOT the whole tree. The subset could be written whole and was, but the library
  cannot: it is 1,600 files, and a program that requires goog.object does not want
  1,599 of them converted. So what is written is what is reachable from what was
  actually required - which is also why this takes `names` at all, and why the
  driver calls it after compiling rather than the prelude calling it before.

  base.js and goog.js are ours in both modes and are always written: the first is
  what every converted file imports, and the second is what a require of the bare
  name `goog` fetches.

  Returns the provide names it wrote."
  [dir names]
  (let [idx   (index)
        dir   (io/file dir)
        seen  (get @written (str dir) #{})
        ;; `goog` is always in: goog.js is what a require of the bare name fetches,
        ;; and cljs.core names goog/typeOf without requiring anything.
        want  (closure idx (cons "goog" names))
        ;; a file out of a jar - the library's, or one found on the classpath, which
        ;; is what a nil :root means. See `written` for why only those are skipped.
        jar?  (fn [n] (or *closure-library* (nil? (:root (entry idx n)))))
        todo  (remove #(and (seen %) (jar? %)) want)
        put!  (fn [path text]
                (let [f (File. dir ^String path)]
                  (.mkdirs (.getParentFile f))
                  (spit f text)))]
    (put! base-path (source base))
    (doseq [provide todo]
      (let [this (entry idx provide)]
        (put! (ns->path provide)
              (if (= provide (canonical this))
                (convert provide idx)
                (stub provide this)))))
    (swap! written update (str dir) (fnil into #{}) (filter jar? want))
    (set todo)))
