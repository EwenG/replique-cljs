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

  ## Not here

  The index is built by parsing the tree, so a provide is declared in one place -
  the file that provides it. `files` is the one list that has to be maintained, and
  it is paths only: a jar has no directory to enumerate."}
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
  "The text of one file of the subset. Read on each call, like runtime.js: a file
  on disk that someone edits should not need a restart to take effect."
  [path]
  (or (some-> (io/resource (str root "/" path)) slurp)
      (throw (ex-info (str "The Closure subset is missing " path
                           ", which clojure.cljs.goog/files names."
                           " Expected it on the classpath at " root "/" path ".")
                      {:path path}))))

;; --- reading a Closure header -----------------------------------------------

(def ^:private provide-re  #"^goog\.provide\('([^']+)'\);\s*$")
(def ^:private module-re   #"^goog\.module\('([^']+)'\);\s*$")
(def ^:private legacy-re   #"^goog\.module\.declareLegacyNamespace\(\);\s*$")
(def ^:private require-re  #"^goog\.require\('([^']+)'\);\s*$")
(def ^:private bound-re    #"^(?:const|let|var)\s+(\w+)\s*=\s*goog\.require\('([^']+)'\);\s*$")

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
  five forms is refused rather than passed through, which is what catches a shape
  like `const {a, b} = goog.require(...)` that a looser rule would silently emit."
  [src]
  (reduce
   (fn [acc line]
     (condp (fn [re s] (re-matches re s)) line
       provide-re :>> (fn [[_ n]] (-> acc (update :provides conj n) (assoc :kind :provide)))
       module-re  :>> (fn [[_ n]] (-> acc (update :provides conj n) (assoc :kind :module)))
       legacy-re  :>> (fn [_]     (assoc acc :legacy? true))
       require-re :>> (fn [[_ n]] (update acc :requires conj {:name n}))
       bound-re   :>> (fn [[_ b n]] (update acc :requires conj {:name n :binding b}))
       (if (and (re-find header-call-re line) (not (comment-line? line)))
         (throw (ex-info (str "Unrecognised Closure header line: " (pr-str line)
                              ". clojure.cljs.goog/parse handles five forms and"
                              " refuses anything else rather than emitting it -"
                              " see the namespace docstring.")
                         {:line line}))
         acc)))
   {:provides [] :requires [] :kind nil :legacy? false}
   (str/split-lines src)))

(defn index
  "provide name -> path, over the whole subset. Built by reading the tree rather
  than declared, so the file that provides a name is the only place that says so.

  Refuses two files providing one name: which one an import meant would then
  depend on the order `files` happens to be in."
  []
  (reduce (fn [m path]
            (reduce (fn [m n]
                      (when-let [prev (get m n)]
                        (throw (ex-info (str "Two files in the Closure subset provide "
                                             n ": " prev " and " path ".")
                                        {:provide n :files [prev path]})))
                      (assoc m n path))
                    m
                    (:provides (parse (source path)))))
          {}
          (remove #{base} files)))


(defn known?
  "Is `ns-sym` a goog name this subset actually provides?

  `goog` is in here like any other name, because goog.js provides it - see that
  file for why it exists when base.js is the goog object already."
  [ns-sym]
  (contains? (index) (str ns-sym)))

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

(defn check-var!
  "Refuse `var-name` in the goog namespace `ns-name` if this tree is known not to
  have it. Returns nil when there is nothing to say, which is the common case: a
  namespace we vendored whole is not our business to police.

  Called by the analyzer when it resolves a goog var - which is the only place that
  knows a name was WRITTEN, as opposed to merely being absent from a JavaScript
  object nobody can enumerate at compile time."
  [ns-name var-name]
  (when-let [msg (get deferred ns-name)]
    (throw (ex-info (str ns-name "/" var-name " - " msg) {:ns ns-name :var var-name})))
  (when-let [have (get reduced-vars ns-name)]
    (when-not (contains? have var-name)
      (throw (ex-info (str ns-name "/" var-name " is not in the Closure subset. "
                           ns-name " here is a " (count have) "-function reduction ("
                           (str/join ", " (sort have)) ") - the real one was left out"
                           " because its dependency chain does not terminate cheaply,"
                           " which doc/cljs-compiler.md 5.5 explains. To get it:"
                           " vendor what you need into clojure/cljs/goog and add it"
                           " to clojure.cljs.goog/files.")
                      {:ns ns-name :var var-name :have have})))))

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
  by `index`, which refuses two files providing one name, and by goog-test."
  [provide]
  (str out-dir "/" (str/replace provide "." "/") ".js"))

(def base-path
  "base.js sits at the root of the output subtree, as runtime.js does at the root of
  the output. It provides nothing, so `ns->path` has no name to work from - and it
  needs none, being the one file everything else imports rather than requires."
  (str out-dir "/" base))

(defn- out-path
  "Where a source path lands in the output tree. Not the same shape: the source
  keeps Closure's layout so the vendored files diff against upstream, and the output
  uses the derivable one."
  [path idx]
  (if (= path base)
    base-path
    (ns->path (first (keep (fn [[n p]] (when (= p path) n)) idx)))))

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

(defn convert
  "One Closure file as an ES module.

  `path` is its place in the tree and `idx` the provide index. base.js is returned
  unchanged - it is already a module, and it is what the others import.

  The output is the input with its header lines blanked, ONE line added at the top
  carrying every import, and ONE at the end - assigning a module's exports to its
  legacy name, or registering a provide. Blanked rather than deleted so that the
  body keeps its shape; the single line at the top means line N in the vendored file
  is line N+1 here."
  [path idx]
  (let [src (source path)]
    (if (= path base)
      src
      (let [{:keys [kind provides requires legacy?]} (parse src)
            _ (when-not kind
                (throw (ex-info (str path " has neither goog.provide nor goog.module."
                                     " Every file in the subset must declare what it"
                                     " provides - that is how the index is built.")
                                {:path path})))
            _ (when (and (= kind :module) (not legacy?))
                (throw (ex-info (str path " is a goog.module without"
                                     " declareLegacyNamespace(). Nothing here can"
                                     " import a module's exports directly - a goog"
                                     " namespace is reached through the goog object -"
                                     " so the legacy name is the only way in.")
                                {:path path})))
            _ (doseq [{n :name} requires]
                (when-not (get idx n)
                  (throw (ex-info (str path " requires " n
                                       ", which no file in the Closure subset"
                                       " provides. Either vendor the file that"
                                       " does and add it to"
                                       " clojure.cljs.goog/files, or reduce the"
                                       " requirer the way goog/string/string.js"
                                       " is reduced.")
                                  {:path path :require n}))))
            here     (out-path path idx)
            imports  (into [(str "import { goog } from \"" (relative here base-path) "\";")]
                           (map (fn [{:keys [name]}]
                                  (str "import \"" (relative here (ns->path name)) "\";")))
                           requires)
            bindings (into (if (= kind :module) ["let exports = {};"] [])
                           (keep (fn [{:keys [name binding]}]
                                   (when binding
                                     ;; the provide name IS the expression:
                                     ;; goog.asserts names the object base.js's
                                     ;; provide hung off goog
                                     (str "const " binding " = " name ";"))))
                           requires)
            header   (str/join " " (concat imports bindings))
            blank    (fn [line]
                       (if (or (re-matches module-re line)
                               (re-matches legacy-re line)
                               (re-matches require-re line)
                               (re-matches bound-re line))
                         ""
                         line))
            body     (map blank (str/split-lines src))
            ;; the last line, and every file has one. A module's exports have to
            ;; be ASSIGNED to its legacy name; a provide file has already assigned
            ;; whatever it provides, but must still be REGISTERED - and registered
            ;; here rather than inside goog.provide, because a provide that ends up
            ;; holding a class has its name replaced by the body it precedes. See
            ;; base.js.
            trailer  [(if (= kind :module)
                        (str "goog.expose('" (first provides) "', exports);")
                        (str "goog.register('" (first provides) "');"))]]
        (str/join "\n" (concat [header] body trailer [""]))))))

(defn write-goog!
  "Write the whole subset into `dir`, which is an output root: the tree lands under
  <out>/goog-subset, at the paths `ns->path` gives - NOT at its shape on the
  classpath, which is Closure's and is not derivable from a name.

  Converted on each call rather than cached, for the same reason runtime.js is read
  on each call."
  [dir]
  (let [idx (index)]
    (doseq [path files]
      (let [f (File. (io/file dir) ^String (out-path path idx))]
        (.mkdirs (.getParentFile f))
        (spit f (convert path idx))))
    (io/file dir)))
