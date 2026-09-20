;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.cljs.goog-test
  "The Closure Library subset: doc/cljs-compiler.md §5.5.

  Three things want checking, and they are independent:

    - the nine VENDORED files are unmodified, checked against the same jar
      ClojureScript 1.12.145 pins;
    - the REWRITE that makes them ES modules preserves the body and refuses a
      header it does not recognise;
    - the result RUNS, and every function cljs.core reaches for gives the answer
      it gave under Closure."
  (:require [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.goog :as goog]
            [clojure.cljs.output]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]])
  (:import [java.io File]))

(use-fixtures :each h/cursor)

;; --- the vendored files are unmodified --------------------------------------

(def vendored
  "The files copied from google-closure-library verbatim. The other five -
  base.js, goog.js and the three reductions - are ours, and are excluded here
  because there is nothing upstream to compare them to."
  ["reflect/reflect.js"
   "debug/error.js"
   "dom/nodetype.js"
   "asserts/asserts.js"
   "math/long.js"
   "math/integer.js"
   ;; the goog.math geometry, added at M6 for cljs/import_test.cljs. Five files,
   ;; 1,588 lines, and their whole chain is goog.asserts - which was already here
   "math/math.js"
   "math/coordinate.js"
   "math/coordinate3.js"
   "math/vec2.js"
   "math/vec3.js"
   "object/object.js"
   "string/internal.js"
   ;; goog.string.format, added at M6 for cljs/repl.cljs. One file, 217 lines,
   ;; and its whole chain is goog.string - which was already here
   "string/stringformat.js"
   "string/stringbuffer.js"])

(def ^:private closure-library?
  "Is google-closure-library on the test classpath, to diff the vendored files
  against? A missing one skips those tests rather than failing them, like node and
  the ClojureScript jar."
  (some? (io/resource "goog/math/long.js")))

(h/deftest-when closure-library? test-the-vendored-files-are-unmodified
  ;; The property that makes 'vendored' an honest word, and the one that decays
  ;; silently: a hand-edit to fix something in goog/math/long.js would work, and
  ;; would be invisible until someone tried to re-vendor from a newer Closure and
  ;; lost it. The rewrite is allowed to change these files; the repo is not.
  (doseq [path vendored]
    (testing path
      (is (= (slurp (io/resource (str "goog/" path)))
             (goog/source path))))))

(h/deftest-when closure-library? test-the-array-subset-is-copied-not-rewritten
  ;; goog/array/array.js is ours, but its four function BODIES are Closure's -
  ;; that is the claim its header makes, and it is the claim that makes taking
  ;; four functions out of a 1,782-line file honest rather than a reimplementation
  ;; nobody reviewed. Each body must appear verbatim in the upstream file.
  (let [upstream (slurp (io/resource "goog/array/array.js"))
        ours     (goog/source "array/array.js")
        ;; the distinctive interior of each, with no name on it: our file spells
        ;; the functions goog.array.f = function... where Closure spells them
        ;; function f(...), so the signature line is exactly what cannot match
        bodies   ["return a > b ? 1 : a < b ? -1 : 0;"
                  "arr.sort(opt_compareFn || "
                  "compArr[i] = {index: i, value: arr[i]};"
                  "return valueCompareFn(obj1.value, obj2.value) || obj1.index - obj2.index;"
                  "const j = Math.floor(randFn() * (i + 1));"
                  "// If length is not a number the following is false. This case is kept for"]]
    (doseq [b bodies]
      (testing b
        (is (str/includes? ours b))
        (is (str/includes? upstream b))))))

;; --- the index --------------------------------------------------------------

(deftest test-the-index-is-read-out-of-the-tree
  ;; A provide is declared in exactly one place - the file that provides it - so
  ;; adding a file to the subset means adding its path and nothing else.
  (let [idx (goog/index)]
    (are [n path] (= path (:path (get idx n)))
      "goog.math.Long"           "math/long.js"
      "goog.math.Integer"        "math/integer.js"
      "goog.object"              "object/object.js"
      "goog.string"              "string/string.js"
      "goog.string.format"       "string/stringformat.js"
      "goog.string.internal"     "string/internal.js"
      "goog.string.StringBuffer" "string/stringbuffer.js"
      "goog.array"               "array/array.js"
      "goog.Uri"                 "uri/uri.js"
      "goog.asserts"             "asserts/asserts.js"
      "goog.debug.Error"         "debug/error.js"
      "goog.dom.NodeType"        "dom/nodetype.js"
      "goog.reflect"             "reflect/reflect.js"
      ;; goog itself has a file of its own, so that a require of it can FETCH
      ;; something - base.js is imported, never required. See goog/goog.js.
      "goog"                     "goog.js")
    ;; base.js is not in it: it is the file the others import, and it provides
    ;; nothing they can require
    (is (not (contains? (set (map :path (vals idx))) "base.js")))
    ;; and it is kept out by index and convert excluding it, NOT by its header
    ;; being unparseable - a file in this tree that parse would refuse is a trap
    ;; for whoever next changes which files are parsed
    (is (= {:provides ["goog"] :requires [] :kind :provide :legacy? false}
           (goog/parse (goog/source goog/base))))))

(deftest test-every-require-in-the-subset-is-provided-by-it
  ;; The closure is closed. This is the test that fails when someone vendors a
  ;; file without vendoring what it needs - and it fails at build time rather
  ;; than as a node import error at the far end.
  (let [idx (goog/index)]
    (doseq [path (remove #{goog/base} goog/files)]
      (doseq [{:keys [name]} (:requires (goog/parse (goog/source path)))]
        (testing (str path " requires " name)
          (is (contains? idx name)))))))

;; --- the rewrite ------------------------------------------------------------

(defn- provide-of
  "The name `path` is converted under - what `convert` takes, where `files` holds
  paths. One file can provide several names and is written under the first (see
  clojure.cljs.goog/canonical); this finds that one."
  [idx path]
  (first (for [[n entry] idx
               :when (and (= path (:path entry)) (= n (goog/canonical entry)))]
           n)))

(deftest test-exactly-one-line-is-added-at-the-top
  ;; The property a stack trace through goog.math.Long is read against: line N of
  ;; the vendored file is line N+1 here. It is why the header is one long line
  ;; carrying every import rather than one line per import.
  (let [idx (goog/index)]
    (doseq [path (remove #{goog/base} goog/files)]
      (testing path
        (let [src  (str/split-lines (goog/source path))
              out  (str/split-lines (goog/convert (provide-of idx path) idx))]
          ;; one at the top and one at the bottom, and convert ends with a newline
          ;; so split-lines is even with the source
          (is (= (+ (count src) 2) (count out)))
          (is (str/starts-with? (first out) "import { goog } from ")))))))

(deftest test-a-vendored-body-is-never-touched
  ;; Line for line, the output is the input with the header lines blanked. Blanked
  ;; rather than deleted is what keeps the offset at exactly one.
  (let [idx (goog/index)]
    (doseq [path vendored]
      (testing path
        (let [src (str/split-lines (goog/source path))
              out (rest (str/split-lines (goog/convert (provide-of idx path) idx)))]
          (doseq [[a b] (map vector src out)]
            ;; either untouched, or blanked because it was one of the header
            ;; lines the rewrite consumes: a require (bare or bound), the
            ;; goog.module line, or declareLegacyNamespace
            (is (or (= a b)
                    (and (= b "")
                         (or (str/includes? a "goog.require")
                             (str/includes? a "goog.module"))))
                (str "line changed: " (pr-str a) " -> " (pr-str b)))))))))

(deftest test-a-bound-require-becomes-a-reference-through-goog
  ;; const asserts = goog.require('goog.asserts') has to keep working as a
  ;; binding, because the body calls asserts.assert - so the import carries the
  ;; ORDER and the const carries the NAME, and they are separate lines.
  (let [out (goog/convert "goog.math.Long" (goog/index))
        header (first (str/split-lines out))]
    ;; ../asserts.js, not ../asserts/asserts.js: the specifier is computed over the
    ;; OUTPUT tree, which is laid out by provide name (goog.asserts ->
    ;; goog/asserts.js), not over Closure's own layout on the classpath
    (is (str/includes? header "import \"../asserts.js\";"))
    (is (str/includes? header "const asserts = goog.asserts;"))
    (is (str/includes? header "const reflect = goog.reflect;"))
    ;; and the body still says asserts.assert, untouched
    (is (str/includes? out "asserts.assert(value === intValue"))))

(deftest test-a-module-gets-its-legacy-name-assigned-last
  ;; goog.math.Long IS the Long constructor, not a namespace holding one, and the
  ;; assignment has to come after the whole body: exports is reassigned at
  ;; long.js:758 but constants are still being hung on Long below it.
  (let [out (goog/convert "goog.math.Long" (goog/index))]
    (is (= "goog.expose('goog.math.Long', exports);"
           (last (remove str/blank? (str/split-lines out)))))
    (is (str/includes? (first (str/split-lines out)) "let exports = {};")))
  ;; a goog.provide file has already assigned what it provides, so its last line
  ;; only REGISTERS - but it must still be the last line, and for the same reason:
  ;; goog.provide('goog.math.Integer') makes an empty object that the body then
  ;; replaces with the constructor, so registering any earlier files the empty one
  ;; away and (Integer.) fails with "not a constructor"
  (let [out (goog/convert "goog.math.Integer" (goog/index))]
    (is (not (str/includes? out "goog.expose")))
    (is (= "goog.register('goog.math.Integer');"
           (last (remove str/blank? (str/split-lines out)))))))

(h/deftest-when h/node? test-a-provide-that-holds-a-class-registers-the-class
  ;; The bug that test caught, from the other end: what $ns hands back has to be
  ;; the constructor, not the empty object goog.provide made on its way past.
  (is (= "function function function"
         (h/run-js
          (str "await import(\"./goog-subset/goog/string/StringBuffer.js\");\n"
               "await import(\"./goog-subset/goog/math/Integer.js\");\n"
               "await import(\"./goog-subset/goog/Uri.js\");\n"
               "console.log([typeof $CLJS.ns(\"goog.string.StringBuffer\"),\n"
               "             typeof $CLJS.ns(\"goog.math.Integer\"),\n"
               "             typeof $CLJS.ns(\"goog.Uri\")].join(\" \"));")))))

(deftest test-the-header-grammar-is-closed
  ;; The refusal that matters: a goog.require shape the rewrite does not know
  ;; would otherwise pass through into the output as a call to a function base.js
  ;; does not have, and fail at load with something far less useful.
  (are [src] (thrown-with-msg? Exception #"Unrecognised Closure header line"
                               (goog/parse src))
    "goog.require('goog.foo', 'extra');"
    "goog.provide('goog.foo')")          ; no semicolon

  ;; A TRAILING COMMENT IS NOT A DIFFERENT SHAPE. goog/promise/promise.js writes
  ;; `const GoogPromise = goog.requireType('goog.Promise');  // for the type
  ;; reference.`, and a grammar that ended at the semicolon refused the file rather
  ;; than reading it - which is what refusing anything unrecognised costs when the
  ;; recogniser is too narrow.
  (are [src expected] (= expected (:requires (goog/parse src)))
    "goog.require('goog.b');  // why"
    [{:name "goog.b"}]

    "const B = goog.requireType('goog.b'); // for the type reference."
    [{:name "goog.b" :binding "B" :type-only? true}])
  (is (= ["goog.a"] (:provides (goog/parse "goog.provide('goog.a');  // a comment"))))

  ;; and closed is not the same as narrow. These three are what the library writes
  ;; and the subset never did - a destructured require, and a requireType with a
  ;; binding or without one - so each is read rather than refused, and each carries
  ;; what convert needs to tell it from a load.
  (are [src expected] (= expected (:requires (goog/parse src)))
    "const {a, b} = goog.require('goog.foo');"
    [{:name "goog.foo" :binding "{a, b}"}]

    "goog.requireType('goog.foo');"
    [{:name "goog.foo" :type-only? true}]

    "const Foo = goog.requireType('goog.foo');"
    [{:name "goog.foo" :binding "Foo" :type-only? true}])
  ;; and a goog.require inside a COMMENT is body, not header. This is not
  ;; hypothetical tidiness: the vendored files mention goog.require in their
  ;; docstrings, and a rule that matched them would refuse the tree it exists to
  ;; convert
  (are [line] (= [] (:requires (goog/parse line)))
    " * @see goog.require('goog.foo');"
    "  // goog.require('goog.foo');"
    "/* goog.module('goog.foo'); */"))


;; --- what the reductions provide --------------------------------------------

(deftest test-the-declared-surface-is-what-the-file-defines
  ;; The table and the code it describes cannot drift: `reduced-vars` is read back
  ;; out of the file. Adding a function to goog/string/string.js without listing it
  ;; would make check-var! refuse a name that works, which is worse than the silent
  ;; failure it exists to prevent.
  (are [ns-name path] (= (get goog/reduced-vars ns-name)
                         (goog/declared-vars ns-name path))
    "goog.string" "string/string.js"
    "goog.array"  "array/array.js"))

(deftest test-a-name-the-reduction-does-not-have-is-refused
  ;; The whole point: goog.string/repeat exists in the Closure Library and does not
  ;; exist here. Without this it compiles to goog$string$ns.repeat(...) and fails at
  ;; RUNTIME, in the user's code, looking like the user's bug.
  ;;
  ;; `format` was the example until §5.29 and no longer reaches this check at all:
  ;; the real one is a FILE of its own, so vendoring it made goog.string.format a
  ;; provide and a provide resolves before check-var! is asked. The reduction is
  ;; unchanged; format simply stopped being part of the question.
  (are [ns-name var-name] (thrown-with-msg?
                           Exception #"is not in the Closure subset"
                           (goog/check-var! ns-name var-name))
    "goog.string" "repeat"
    "goog.string" "htmlEscape"
    "goog.array"  "binarySearch"
    "goog.array"  "removeDuplicates")
  ;; and the message says what IS there, because the next question after "why not"
  ;; is always "then what"
  (is (thrown-with-msg? Exception #"contains, endsWith, isEmpty, isEmptyOrWhitespace"
                        (goog/check-var! "goog.string" "repeat"))))

(deftest test-a-name-the-reduction-does-have-is-allowed
  (are [ns-name var-name] (nil? (goog/check-var! ns-name var-name))
    "goog.string" "contains"
    "goog.string" "isEmpty"
    "goog.array"  "stableSort"
    "goog.array"  "defaultCompare"))

(deftest test-a-vendored-namespace-is-not-policed
  ;; The asymmetry that makes this honest: we check what we TRUNCATED. goog.object
  ;; is vendored whole, so a name it does not have is the Closure Library's business
  ;; and not ours - and there is nothing to check against, since a JavaScript
  ;; object's properties cannot be enumerated at compile time.
  (are [ns-name var-name] (nil? (goog/check-var! ns-name var-name))
    "goog.object"     "getValueByKeys"
    "goog.object"     "nonesuch"
    "goog.math.Long"  "fromString"
    "goog.asserts"    "assert"))

(deftest test-every-var-of-a-deferred-namespace-is-refused
  ;; goog.Uri is a placeholder, so it is not that SOME names are missing - all of
  ;; them are, and the message says so rather than listing an empty surface.
  (are [var-name] (thrown-with-msg? Exception #"goog.Uri is a placeholder"
                                    (goog/check-var! "goog.Uri" var-name))
    "parse" "QueryData" "getScheme"))

;; --- it runs ----------------------------------------------------------------

(defn- goog-js
  "Run `program` beside a written output root, with the goog subset imported.

  `imports` are goog NAMES, and the paths come from clojure.cljs.goog/ns->path -
  the output tree is laid out by provide name, not by Closure's own file layout, so
  goog.math.Long is goog/math/Long.js here and math/long.js on the classpath."
  [imports program]
  (h/run-js (str (str/join "\n" (map #(str "import \"./" (goog/ns->path %) "\";")
                                     imports))
                 "\nimport { goog } from \"./" goog/base-path "\";\n"
                 program)))

(h/deftest-when h/node? test-every-function-cljs-core-uses-works
  (testing "goog.math.Long - 64-bit arithmetic, which is why it is vendored whole"
    (is (= "1099511627777"
           (goog-js ["goog.math.Long"]
                    "const L = goog.math.Long;
                     console.log(L.fromNumber(Math.pow(2,40)).add(L.getOne()).toString());")))
    (is (= "123456789012345"
           (goog-js ["goog.math.Long"]
                    "const L = goog.math.Long;
                     console.log(L.fromString(\"123456789012345\")
                                  .multiply(L.fromInt(7)).div(L.fromInt(7)).toString());"))))

  (testing "goog.math.Integer - arbitrary precision"
    (is (= "99999999999999999999"
           (goog-js ["goog.math.Integer"]
                    "console.log(goog.math.Integer.fromString(\"9\".repeat(20)).toString());"))))

  (testing "goog.string - the three functions, which are goog.string.internal's"
    (is (= "true false true true"
           (goog-js ["goog.string"]
                    "const s = goog.string;
                     console.log([s.isEmpty(\"\"), s.isEmpty(\"x\"),
                                  s.endsWith(\"abc\",\"bc\"), s.contains(\"abc\",\"b\")]
                                 .join(\" \"));"))))

  (testing "goog.object - the six functions"
    (is (= "1 true a {\"a\":1}"
           (goog-js ["goog.object"]
                    "const o = {}; goog.object.set(o, \"a\", 1);
                     console.log([goog.object.get(o,\"a\"), goog.object.containsKey(o,\"a\"),
                                  goog.object.getKeys(o).join(\",\"),
                                  JSON.stringify(goog.object.clone(o))].join(\" \"));"))))

  (testing "goog.array - the four functions"
    (is (= "1,2,3 1,2 -1 1"
           (goog-js ["goog.array"]
                    "const a = [3,1,2]; goog.array.stableSort(a);
                     console.log([a.join(\",\"), goog.array.clone([1,2]).join(\",\"),
                                  goog.array.defaultCompare(1,2),
                                  goog.array.defaultCompare(2,1)].join(\" \"));"))))

  (testing "goog.string.StringBuffer - genuinely constructed, not just tested for"
    (is (= "abc 3"
           (goog-js ["goog.string.StringBuffer"]
                    "const sb = new goog.string.StringBuffer(\"a\");
                     sb.append(\"b\").append(\"c\");
                     console.log(sb.toString() + \" \" + sb.getLength());")))))

(h/deftest-when h/node? test-stable-sort-is-stable
  ;; The one function of the four whose contract is not obvious from its body, and
  ;; the reason cljs.core calls stableSort rather than sort: sort-by must not
  ;; reorder equal keys.
  (is (= "a1,b1,c1,a2"
         (goog-js ["goog.array"]
                  "const xs = [{k:1,v:\"a1\"},{k:1,v:\"b1\"},{k:1,v:\"c1\"},{k:2,v:\"a2\"}];
                   goog.array.stableSort(xs, (x,y) => x.k - y.k);
                   console.log(xs.map(x => x.v).join(\",\"));"))))

(h/deftest-when h/node? test-a-goog-namespace-is-a-namespace-object
  ;; §5.2 applied to goog, and the whole reason the analyzer needs no new case:
  ;; $ns("goog.object") is goog.object itself, so gobject/get is a property of a
  ;; namespace object exactly like any ClojureScript var. base.js registers it,
  ;; and the static import runs before any prologue calls $ns.
  (is (= "true true true"
         (goog-js ["goog.object" "goog.math.Long"]
                  "console.log([$CLJS.ns(\"goog.object\").get === goog.object.get,
                                $CLJS.ns(\"goog.math\").Long === goog.math.Long,
                                $CLJS.ns(\"goog.math.Long\") === goog.math.Long]
                               .join(\" \"));"))))

(h/deftest-when h/node? test-the-subset-never-touches-the-global-goog
  ;; The isolation claim, and the only test of it: a project can bundle a real
  ;; Closure Library, and that one owns globalThis.goog. Ours is on $CLJS.
  ;;
  ;; Checked in both directions, because one alone would pass for the wrong
  ;; reason: loading the whole subset must leave globalThis.goog absent, AND a
  ;; globalThis.goog that is already there must come through untouched - it is the
  ;; second that fails if base.js ever goes back to `globalThis.goog ??= {}`, since
  ;; then it would ADOPT theirs and write our provides into it.
  (is (= "undefined true | pre-existing 1"
         (h/run-js
          (str "globalThis.goog = { theirs: \"pre-existing\", typeOf: 1 };\n"
               "const before = globalThis.goog;\n"
               "await import(\"./goog-subset/goog/string.js\");\n"
               "await import(\"./goog-subset/goog/math/Long.js\");\n"
               ;; their object is untouched: no string, no math, same identity,
               ;; and even `typeOf` - a name base.js sets on ours - is still theirs
               "console.log([typeof globalThis.goog.string,\n"
               "             globalThis.goog === before, \"|\",\n"
               "             globalThis.goog.theirs, globalThis.goog.typeOf]\n"
               "            .join(\" \"));")))))

(deftest test-the-subset-is-not-written-to-a-path-a-real-closure-would-want
  ;; goog/ is where a real Closure Library unpacks, and closure/goog/ is where
  ;; Google's own tree puts it. Neither name is available to us, which is why
  ;; out-dir is deliberately awkward.
  (is (= "goog-subset" goog/out-dir))
  (is (not (contains? #{"goog" "closure"} goog/out-dir)))
  (let [dir (h/temp-dir)]
    (try
      (clojure.cljs.output/write-prelude! dir)
      (clojure.cljs.output/ensure-goog! dir '[goog.math.Long])
      (is (.isFile (java.io.File. dir "goog-subset/goog/math/Long.js")))
      (is (not (.exists (java.io.File. dir "goog"))))
      (finally (h/delete-tree! dir)))))

(h/deftest-when h/node? test-goog-typeof-is-closures-not-ours
  ;; Two functions named typeOf, and they differ where it matters: Closure
  ;; separates null from undefined and runtime.js does not, because
  ;; (extend-type nil ...) is ONE case in ClojureScript. cljs.core dispatches on
  ;; goog/typeOf, so this file has to keep Closure's.
  (is (= "null undefined | null null"
         (goog-js []
                  "console.log([goog.typeOf(null), goog.typeOf(undefined), \"|\",
                                $CLJS.typeOf(null), $CLJS.typeOf(undefined)].join(\" \"));"))))

(h/deftest-when h/node? test-uri-is-deferred-and-says-so
  ;; The decision recorded in doc/cljs-compiler.md §7. uri? has to keep answering,
  ;; and false is the right answer while nothing can construct one - but reaching
  ;; for a real Uri has to fail loudly rather than quietly do nothing.
  (is (= "false" (goog-js ["goog.Uri"] "console.log(({}) instanceof goog.Uri);")))
  (is (str/includes? (goog-js ["goog.Uri"] "new goog.Uri(\"http://x/\");")
                     "goog.Uri is not implemented")))

(h/deftest-when h/node? test-asserts-is-a-no-op-because-debug-is-false
  ;; goog.asserts is vendored - three files, and the chain stops - but
  ;; ENABLE_ASSERTS is goog.define('...', goog.DEBUG) and base.js sets DEBUG
  ;; false, so an assert returns its argument and costs a call. That is what
  ;; goog.math.Long's one assert compiles to.
  (is (= "false 7"
         (goog-js ["goog.asserts"]
                  "console.log(goog.asserts.ENABLE_ASSERTS + \" \"
                               + goog.asserts.assert(7));"))))

(defn- module-output
  "Compile `src` as app.core THROUGH THE DRIVER, run the module, and print the value
  of its `out` var.

  Through the driver rather than through h/output, and the difference is the point:
  h/js emits a namespace's prologue and body but not its IMPORTS, which is the
  driver's job. That was invisible while every test compiled a namespace requiring
  nothing - a goog require is the first thing whose import has to actually be
  there, and without it $ns(\"goog.string\") is an empty object and every call is
  `not a function`."
  [src]
  (let [dir (h/temp-dir)]
    (try
      (let [srcdir (File. dir "src")
            out    (File. dir "out")
            f      (File. srcdir "app/core.cljs")]
        (.mkdirs (.getParentFile f))
        (spit f src)
        (driver/compile-namespace! (env/compile-env) 'app.core
                                   {:source-paths [srcdir] :out-dir out})
        (spit (File. out "run.mjs")
              (str "import \"./ns/app/core.js\";\n"
                   "import { $CLJS } from \"./runtime.js\";\n"
                   "console.log($CLJS.ns(\"app.core\").out);\n"))
        (let [{:keys [out err exit]} (sh/sh "node" (str (File. out "run.mjs")))]
          (if (zero? exit) (str/trim out) (str "THREW: " (str/trim err)))))
      (finally (h/delete-tree! dir)))))

;; --- requiring goog from ClojureScript --------------------------------------
;;
;; Everything above is about the subset as JavaScript. This is the other half: a
;; goog namespace reached from a ns form, which needs the analyzer to know that a
;; goog name is not a namespace to compile and that a goog var is not a Var.

(h/deftest-when h/node? test-a-goog-namespace-is-required-and-called
  (is (= "true 7 -1"
         (module-output
          "(ns app.core (:require [goog.string :as gs] [goog.object :as gobject]
                                  [goog.array :as garray]))
           (def out (js* \"[~{}, ~{}, ~{}].join(\\\" \\\")\"
                         (gs/isEmpty \"\") (gobject/get (js* \"{a: 7}\") \"a\")
                         (garray/defaultCompare 1 2)))"))))

(deftest test-a-goog-call-is-a-method-call-not-a-cljs-one
  ;; goog is a plain JavaScript function: no arity dispatch to go through, and no
  ;; reason for the null receiver every ClojureScript call carries.
  (let [js (h/js (h/fresh-env)
                 "(ns app.core (:require [goog.object :as gobject]))
                  (gobject/get 1 2)")]
    (is (str/includes? js "goog$object$ns.get((1), (2))"))
    (is (not (str/includes? js ".call(null")))))

(deftest test-a-goog-var-is-not-munged
  ;; §5.3: goog owns these names, so they are spelled the host's way. A var of
  ;; ours would go through the injective munge and come out as something else.
  (is (str/includes? (h/js (h/fresh-env)
                           "(ns app.core (:require [goog.array :as garray]))
                            (garray/defaultCompare 1 2)")
                     "defaultCompare")))

(h/deftest-when h/node? test-import-gives-a-class-its-bare-name
  ;; (:import [goog.string StringBuffer]) is the one ns reference cljs.core needs
  ;; that :require cannot express, and it opens core.cljs.
  (is (= "abc"
         (module-output
          "(ns app.core (:import [goog.string StringBuffer]))
           (def out (js* \"~{}.append(\\\"bc\\\").toString()\" (StringBuffer. \"a\")))"))))

(h/deftest-when h/node? test-goog-is-implicitly-available
  ;; cljs.core names goog/typeOf nineteen times and never requires goog.
  (is (= "array" (module-output "(ns app.core) (def out (goog/typeOf (js* \"[]\")))")))
  ;; and the require is RECORDED, not assumed - without the import, $ns("goog")
  ;; would be an empty object at run time and typeOf would not be there
  (let [js (h/js (h/fresh-env) "(ns app.core) (goog/typeOf 1)")]
    (is (str/includes? js "const goog$ns = $ns(\"goog\");"))))

(h/deftest-when h/node? test-a-provide-is-a-value-as-well-as-a-module
  ;; goog.math.Long names the class itself. A simple symbol with dots in it, so it
  ;; never reaches qualified-symbol resolution at all.
  (is (= "true false"
         (module-output
          "(ns app.core (:require goog.math.Long))
           (def out (js* \"[~{} instanceof ~{}, ~{} instanceof ~{}].join(\\\" \\\")\"
                         (js* \"~{}.fromInt(3)\" goog.math.Long) goog.math.Long
                         (js* \"{}\") goog.math.Long))"))))

(h/deftest-when h/node? test-the-script-path-fetches-goog-too
  ;; The REPL's path, and the only thing that exercises urlFor's goog branch -
  ;; the second implementation of the layout, in JavaScript, which has a name and
  ;; nothing else to compute a URL from.
  (is (= "true | 5"
         (h/script-output
          "(ns app.core (:require [goog.string :as gs] [goog.object :as gobject]))
           (js* \"[~{}, ~{}].join(\\\" | \\\")\"
                (gs/contains \"abc\" \"b\") (gobject/get (js* \"{k: 5}\") \"k\"))"))))

(deftest test-the-module-imports-goog-from-the-right-place
  (let [js (h/js (h/fresh-env) "(ns app.core (:require [goog.object :as gobject]))
                                (gobject/get 1 2)")]
    ;; the prologue binds it like any other namespace, because it IS one
    (is (str/includes? js "const goog$object$ns = $ns(\"goog.object\");"))))

;; --- what the analyzer refuses ----------------------------------------------

(defn- refuses [src]
  (try (h/js (h/fresh-env) src) nil
       (catch Exception e (or (ex-message e) ""))))

(deftest test-a-goog-namespace-we-do-not-have-is-refused-early
  ;; The alternative is an import of a file that is not there and a 404 at load.
  ;; The message names the subset, because "no such namespace" would send someone
  ;; looking for a typo in a name that is correct.
  (let [msg (refuses "(ns app.core (:require [goog.dom :as gdom]))")]
    (is (re-find #"No such Closure namespace: goog.dom" msg))
    (is (re-find #"ships a SUBSET" msg))
    (is (re-find #"goog.object" msg))))

(deftest test-refer-on-a-goog-namespace-is-refused
  ;; There is no Var to map. :import is how Closure gives a bare name, and the
  ;; message says so rather than leaving someone to guess.
  (let [msg (refuses "(ns app.core (:require [goog.string :refer [contains]]))")]
    (is (re-find #"Cannot :refer" msg))
    (is (re-find #":import" msg))))

(deftest test-macro-options-on-a-goog-namespace-are-refused
  (is (re-find #"Closure namespace"
               (refuses "(ns app.core (:require [goog.object :include-macros true]))"))))

(deftest test-the-reduction-check-fires-through-the-analyzer
  ;; The whole point of reduced-vars, reached the way a user reaches it. Without
  ;; this the call compiles to goog$string$ns.repeat(...) and fails at run time.
  ;;
  ;; `format` was the example here until §5.29, and stopped being one for a reason
  ;; worth keeping: the real goog.string.format lives in a FILE of its own, so
  ;; vendoring that file makes it a provide - a name in its own right rather than a
  ;; var in a shorter namespace - and it resolves before check-var! is ever asked.
  ;; The reduction is unchanged; what changed is that format is no longer part of it.
  (let [msg (refuses "(ns app.core (:require [goog.string :as gs])) (gs/repeat \"x\" 2)")]
    (is (re-find #"goog.string/repeat is not in the Closure subset" msg))
    (is (re-find #"contains, endsWith, isEmpty, isEmptyOrWhitespace" msg)))
  ;; and a vendored namespace is NOT policed - goog.object is complete, so a name
  ;; it does not have is Closure's business and fails the way any interop does
  (is (nil? (refuses "(ns app.core (:require [goog.object :as gobject]))
                      (gobject/getValueByKeys 1 2)"))))

(deftest test-a-deferred-namespace-refuses-every-var
  (is (re-find #"goog.Uri is a placeholder"
               (refuses "(ns app.core (:require [goog.Uri :as u])) (u/parse \"x\")"))))

(deftest test-a-fully-qualified-goog-name-brings-its-own-import
  ;; doc/cljs-compiler.md §5.18. A name written out in full carries its own
  ;; referent, so it needs no ns form - but it is still RECORDED as a require,
  ;; because that is what the module's imports are computed from. Which makes the
  ;; test that matters whether it RUNS: analysing is the easy half, and without the
  ;; import $ns("goog.object") is an empty object and every call is not a function.
  (is (= "1" (module-output
              "(ns app.core) (def out (goog.object/get #js {:a 1} \"a\"))")))

  ;; named in FULL, because goog.math.Long is one provide and not a var called Long
  ;; in a namespace called goog.math - which is what the dotted-symbol rule would
  ;; otherwise make of it (analyzer/analyze-dotted-symbol). cljs.spec.alpha writes
  ;; exactly this, at alpha.cljs:1463, with no require to go with it.
  (is (= "false" (module-output
                  "(ns app.core) (def out (instance? goog.math.Long 1))")))

  ;; and the same provide reached the other way round. goog.string/StringBuffer is
  ;; NOT a var in the 11-function reduction goog.string: slash and dot are two
  ;; spellings of one name. This is what cljs.core/with-out-str expands to, in
  ;; whichever namespace called it.
  (is (= "ab" (module-output
               "(ns app.core)
                (def out (let [sb (goog.string/StringBuffer.)]
                           (.append sb \"a\") (.append sb \"b\") (.toString sb)))")))

  ;; strictness where it says something: a name this fork does not ship
  (is (re-find #"subset of the Closure Library"
               (refuses "(ns app.core) (goog.dom/getElement 1)"))))

(deftest test-the-goog-math-geometry-is-in-the-subset
  ;; The five files added at M6, and the reason they could be added VERBATIM: the
  ;; whole chain is goog.math -> goog.asserts, and goog.asserts was already here for
  ;; goog.math.Long. No HTML, no DOM, no user-agent sniffing anywhere in them -
  ;; which is the entire difference between this chain and goog.string's.
  ;;
  ;; The index is built by PARSING the tree, so this also proves the five files are
  ;; on the classpath and that their headers parse.
  (are [name] (goog/known? name)
    'goog.math 'goog.math.Coordinate 'goog.math.Coordinate3
    'goog.math.Vec2 'goog.math.Vec3)

  (testing "and nothing new came in behind them"
    ;; every require of the five, minus what the subset already had
    (let [reqs (into #{} (comp (mapcat #(:requires (goog/parse (goog/source %))))
                               (map (comp symbol :name)))
                     ["math/math.js" "math/coordinate.js" "math/coordinate3.js"
                      "math/vec2.js" "math/vec3.js"])]
      (is (= '#{goog.asserts goog.math goog.math.Coordinate goog.math.Coordinate3}
             reqs))))

  (testing "an :import of one resolves and records its require"
    ;; the runtime proof is cljs/import_test.cljs, which constructs a Vec2 and a
    ;; Vec3 under node; this is the analyzer half of it
    (let [cenv (h/fresh-env 'cljs.user)]
      (h/analyze cenv '(ns app.g (:import [goog.math Vec2 Vec3])))
      (is (contains? (env/requires cenv 'app.g) 'goog.math.Vec2))
      (is (contains? (env/requires cenv 'app.g) 'goog.math.Vec3))
      (is (= :goog-ns (:op (h/analyze cenv 'Vec2)))))))

;; --- goog.string.format ------------------------------------------------------

(deftest test-format-is-a-provide-and-so-escapes-the-reduction
  ;; §5.29. goog.string is a fourteen-function reduction and `format` is not one of
  ;; them - reduced-vars would refuse it, and did, because the real one lives in a
  ;; FILE OF ITS OWN. Vendoring that file makes goog.string.format a provide, and a
  ;; provide is a name in its own right rather than a var in a shorter namespace,
  ;; so it resolves before check-var! is ever asked. That is the same rule
  ;; goog.math.Long goes through (§5.18), arrived at from the other direction.
  (is (contains? (set (keys (goog/index))) "goog.string.format"))
  (is (not (contains? (get goog/reduced-vars "goog.string") "format")))
  ;; nothing about the reduction moved - see
  ;; test-the-reduction-check-fires-through-the-analyzer, which now asks about
  ;; `repeat` for exactly this reason
  (is (nil? (refuses "(ns app.core (:require [goog.string :as gs] [goog.string.format]))
                      (gs/format \"%s\" 1)"))))

(deftest test-format-emits-the-provide-not-a-property
  (let [js (h/js (h/fresh-env)
                 "(ns app.core (:require [goog.string :as gstring] [goog.string.format]))
                  (gstring/format \"%s\" 1)")]
    (is (str/includes? js "const goog$string$format$ns = $ns(\"goog.string.format\");") js)
    (is (str/includes? js "goog$string$format$ns(\"%s\", (1))") js)))

(h/deftest-when h/node? test-format-runs
  ;; through the driver, so the import is there - see module-output
  (is (= "a-7-1.50"
         (module-output
          "(ns app.core (:require [goog.string :as gstring] [goog.string.format]))
           (def out (gstring/format \"%s-%d-%.2f\" \"a\" 7 1.5))"))))

;; --- the Closure Library, when a project has one -----------------------------
;;
;; The same jar the vendored files are diffed against, used the other way round:
;; there as the thing `vendored` must still equal, here as the tree a project
;; compiles against instead of the subset. So these run wherever those do.

(defmacro ^:private with-library
  "Run `body` against the Closure Library on the classpath.

  `binding` rather than `use-closure-library!`, which alters the root: a test that
  set the mode for the process would decide it for every test after it."
  [& body]
  `(binding [goog/*closure-library* true] ~@body))

(h/deftest-when closure-library? test-the-library-index-is-its-own-deps-js
  ;; 1,609 goog.addDependency lines, which is the library saying where every name
  ;; it has lives - so nothing here walks a directory, which a jar has none of.
  (with-library
    (let [idx (goog/index)]
      (are [n path] (= path (:path (get idx n)))
        ;; names the subset does not have, which is the whole point
        "goog.style"     "style/style.js"
        "goog.net.XhrIo" "net/xhrio.js"
        "goog.date"      "date/date.js"
        "goog.functions" "functions/functions.js"
        ;; and one it does, from the other tree
        "goog.object"    "object/object.js")
      (is (< 1000 (count idx)))
      ;; goog.js stays ours in both modes: the library has no file that provides
      ;; the bare name, because there base.js IS that name - and base.js is ours
      (is (= {:root goog/root :path "goog.js"}
             (select-keys (get idx "goog") [:root :path]))))))

(h/deftest-when closure-library? test-the-tree-in-use-is-chosen-not-detected
  ;; A project that has google-closure-library on its classpath - which anything
  ;; depending on ClojureScript does - must not silently start compiling against a
  ;; different Closure than it compiled against yesterday. This whole test file
  ;; runs with one on the classpath, and the default is still the subset.
  (is (false? goog/*closure-library*))
  (is (not (goog/known? 'goog.style)))
  (with-library (is (goog/known? 'goog.style)))
  ;; and the error for a name the subset lacks says which of the two answers is
  ;; true of this classpath
  (is (str/includes? (goog/get-real-closure) ":closure-library"))
  (is (str/includes? (goog/get-real-closure) "on your classpath")))

(deftest test-the-mode-can-be-set-for-a-process
  ;; What a build or a REPL calls once from its options, where the tests bind. Put
  ;; back in a finally, because this one alters the root: a test that left it set
  ;; would decide the mode of every test after it.
  (try
    (goog/use-closure-library! true)
    (is (true? goog/*closure-library*))
    (finally (goog/use-closure-library! false)))
  (is (false? goog/*closure-library*)))

(h/deftest-when closure-library? test-only-what-we-truncated-is-policed
  ;; The reductions and the placeholder are things WE removed, so they are ours to
  ;; report. In library mode nothing is removed and there is nothing to report -
  ;; the file being converted is the real one, and a var it does not have is the
  ;; Closure Library's business.
  (is (thrown-with-msg? Exception #"reduction" (goog/check-var! "goog.string" "format")))
  (is (thrown-with-msg? Exception #"placeholder" (goog/check-var! "goog.Uri" "parse")))
  (with-library
    (is (nil? (goog/check-var! "goog.string" "format")))
    (is (nil? (goog/check-var! "goog.Uri" "parse")))))

(deftest test-only-what-is-required-is-written
  ;; What made the subset writable whole is that it is twenty files. The library is
  ;; 1,600, so what is written is the closure of what was required and nothing else
  ;; - which is also why write-goog! takes names at all.
  (let [dir (h/temp-dir)]
    (try
      (goog/write-goog! dir ["goog.object"])
      (is (.isFile (io/file dir "goog-subset/goog/object.js")))
      ;; always, in both modes: the file every converted file imports, and the file
      ;; a require of the bare name fetches
      (is (.isFile (io/file dir "goog-subset/base.js")))
      (is (.isFile (io/file dir "goog-subset/goog.js")))
      ;; and nothing else. goog.math.Long is in the subset and nobody asked for it
      (is (not (.exists (io/file dir "goog-subset/goog/math/Long.js"))))
      (finally (h/delete-tree! dir)))))

(deftest test-a-require-is-followed-and-a-requiretype-is-not
  ;; A requireType says this file names that type in a comment. Closure's own
  ;; loader does not fetch it, and neither does this: it contributes a binding when
  ;; it has one, so the annotations still parse, and nothing to the closure.
  (let [parsed (goog/parse "goog.provide('goog.a');\ngoog.require('goog.b');\ngoog.requireType('goog.c');\n")]
    (is (= [{:name "goog.b"} {:name "goog.c" :type-only? true}] (:requires parsed))))
  (when closure-library?
    (with-library
      (let [idx  (goog/index)
            out  (goog/convert "goog.style" idx)
            head (first (str/split-lines out))]
        ;; goog/style/style.js requires goog.dom and requireTypes goog.events.Event
        (is (str/includes? head "import \"./dom.js\";"))
        (is (not (str/includes? head "events/Event.js")))
        ;; and it is not in what has to be on disk either
        (is (contains? (goog/closure idx ["goog.style"]) "goog.dom"))
        (is (not (contains? (goog/closure idx ["goog.style"]) "goog.events.Event")))))))

(h/deftest-when closure-library? test-a-module-is-exposed-with-or-without-a-legacy-name
  ;; 781 of the library's files are goog.module and 91 declare a legacy namespace.
  ;; Under Closure that declaration decides whether a global is created; here every
  ;; namespace is a property of the goog object either way, so it decides nothing -
  ;; and a converter that refused the other 690 could not convert the library.
  (with-library
    (let [idx (goog/index)
          out (goog/convert "goog.async.promises" idx)]
      (is (not (str/includes? out "declareLegacyNamespace")))
      (is (str/includes? out "let exports = {};"))
      (is (= "goog.expose('goog.async.promises', exports);"
             (last (remove str/blank? (str/split-lines out))))))))

(h/deftest-when closure-library? test-a-file-that-provides-several-names-is-written-once
  ;; 193 of the library's entries provide more than one name - a namespace and the
  ;; nested names under it. ns->path is a pure function of a NAME, because
  ;; runtime.js computes a URL from one with nothing to ask the JVM, so those are
  ;; two paths and only one of them can hold the body.
  (with-library
    (let [idx   (goog/index)
          entry (get idx "goog.editor.range.Point")]
      (is (= "goog.editor.range" (goog/canonical entry)))
      ;; the other path is an import of the one that has the body, and nothing else
      (is (= "import \"../range.js\";\n" (goog/stub "goog.editor.range.Point" entry)))
      ;; and the body registers both, because it is the only place the second one
      ;; is ever registered from
      (let [out (goog/convert "goog.editor.range" idx)]
        (is (str/includes? out "goog.register('goog.editor.range');"))
        (is (str/includes? out "goog.register('goog.editor.range.Point');")))
      ;; A STUB DRAGS IN THE FILE IT IMPORTS. Asking for the second name alone has
      ;; to put the first on disk, because nothing else will: the program never
      ;; names it and no other file requires it. goog.debug.entryPointRegistry is
      ;; the case that found this - goog.net.XhrIo reaches it, and the file is
      ;; written under goog.debug.EntryPointMonitor.
      (is (contains? (goog/closure idx ["goog.debug.entryPointRegistry"])
                     "goog.debug.EntryPointMonitor")))))

(defn- node
  "Run `f` under node. Its trimmed stdout, or \"THREW: <message>\"."
  [^java.io.File f]
  (let [{:keys [out err exit]} (sh/sh "node" (.getPath f))]
    (if (zero? exit) (str/trim out) (str "THREW: " (str/trim err)))))

(h/deftest-when (and h/node? closure-library?) test-the-library-compiles-and-runs
  ;; The end of it, through every piece at once: a namespace requiring two Closure
  ;; namespaces the subset does not have, compiled with :closure-library true, its
  ;; files converted out of the jar on demand, imported by node and called.
  ;;
  ;; goog.crypt.base64 is a goog.provide file with a chain behind it - goog.crypt,
  ;; goog.userAgent and what those reach - so what this really runs is the closure,
  ;; not one file.
  (let [src (h/write-sources!
             (h/temp-dir)
             '{probe.core "(ns probe.core
                             (:require [goog.functions :as gfunc]
                                       [goog.crypt.base64 :as b64]))
                           (defn run [] (str (b64/encodeString \"hi\") \"-\" ((gfunc/constant 5))))"})
        out (h/temp-dir)]
    (try
      (let [cenv   (env/compile-env {:ns 'cljs.user})
            result (driver/compile-namespace! cenv 'probe.core
                                              {:out-dir out
                                               :closure-library true
                                               :source-paths [src]})
            entry  (io/file out "check.mjs")]
        (is (= '[cljs.core probe.core] (:compiled result)))
        ;; converted out of the jar, at the path a name gives rather than Closure's
        (is (.isFile (io/file out "goog-subset/goog/crypt/base64.js")))
        (is (.isFile (io/file out "goog-subset/goog/functions.js")))
        (spit entry (str "import { ns as $ns } from \"./runtime.js\";\n"
                         "import \"./ns/probe/core.js\";\n"
                         "console.log($ns(\"probe.core\").run());\n"))
        (is (= "aGk=-5" (node entry))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

(h/deftest-when h/node? test-base-js-has-what-the-library-reaches-for
  ;; Sixteen functions and one object, added to base.js because the library's bodies
  ;; call them and the subset's never did. The list was measured over its 1,604
  ;; non-test files - goog.setTestOnly in 744 of them, getCssName in 570, bind in
  ;; 457 - rather than guessed.
  ;;
  ;; TESTED AS A SURFACE, not through a program that happens to use it. A program
  ;; reaches four or five of these, and the one it does not reach is exactly the one
  ;; that could be missing: taking goog.bind out of base.js broke nothing anywhere
  ;; else in this file, which is what said this test had to exist.
  (is (= "ok" (goog-js [] "
     const eq = (a, b, what) => { if (a !== b) throw new Error(what + ': ' + a + ' != ' + b); };
     eq(goog.bind(function(x){ return this.n + x; }, {n: 1})(2), 3, 'bind');
     eq(typeof goog.now(), 'number', 'now');
     eq(goog.getCssName('a-b'), 'a-b', 'getCssName');
     eq(goog.getCssName('a', 'b'), 'a-b', 'getCssName/2');
     eq(goog.getMsg('{$who} said', {who: 'x'}), 'x said', 'getMsg');
     eq(goog.setTestOnly('x'), undefined, 'setTestOnly');
     eq(goog.isDateLike(new Date()), true, 'isDateLike');
     eq(goog.isDateLike(1), false, 'isDateLike/2');
     let scoped = 0; goog.scope(function(){ scoped = 1; }); eq(scoped, 1, 'scope');
     goog.exportSymbol('a.b.c', 7, globalThis); eq(globalThis.a.b.c, 7, 'exportSymbol');
     eq(goog.getObjectByName('a.b.c', globalThis), 7, 'getObjectByName');
     eq(goog.getObjectByName('a.nope.c', globalThis), null, 'getObjectByName/2');
     const o = {}; goog.exportProperty(o, 'p', 8); eq(o.p, 8, 'exportProperty');
     eq(goog.cloneObject({a: {b: 1}}).a.b, 1, 'cloneObject');
     const u = {}; eq(goog.hasUid(u), false, 'hasUid');
     goog.getUid(u); eq(goog.hasUid(u), true, 'hasUid/2');
     goog.removeUid(u); eq(goog.hasUid(u), false, 'removeUid');
     function C(){}; goog.addSingletonGetter(C);
     eq(C.getInstance(), C.getInstance(), 'addSingletonGetter');
     // null under node, which has no Trusted Types - the branch every caller handles
     eq(goog.createTrustedTypesPolicy('x'), null, 'createTrustedTypesPolicy');
     goog.setCssNameMapping({a: 'z'}); eq(goog.getCssName('a'), 'z', 'setCssNameMapping');
     goog.setCssNameMapping(null);
     console.log('ok');")))
  ;; goog.module.get is the one that is an object rather than a function: a module
  ;; inside a goog.scope reaches what it required with it, and what it hands back is
  ;; what goog.expose assigned.
  (is (= "true" (goog-js ["goog.string"]
                         "console.log(goog.module.get('goog.string') === goog.string);"))))
