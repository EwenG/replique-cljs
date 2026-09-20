;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.cljs.output-test
  "The output layout: doc/cljs-output-layout.md, and the one test that keeps its
  two implementations in step."
  (:require [clojure.cljs.output :as output]
            [clojure.cljs.test-harness :as h]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is]])
  (:import [java.io File]))

(deftest test-a-namespace-becomes-a-nested-file
  (are [ns-sym path] (= path (output/ns->path ns-sym))
    'app          "ns/app.js"
    'app.core     "ns/app/core.js"
    'a.b.c.d      "ns/a/b/c/d.js"
    ;; unmunged, unlike cljs.util/ns->relpath: nothing loads an emitted .js
    ;; through a classloader, so the reason a JVM package name cannot hold a
    ;; hyphen does not reach here
    'my-lib.core  "ns/my-lib/core.js"))

(deftest test-the-path-is-injective
  ;; the property that matters: two namespaces never share a file. It holds
  ;; because . -> / is injective and nothing else happens - munging is where
  ;; ClojureScript loses it, sending my-lib.core and my_lib.core to one file
  (let [names '[app app.core a.b.c.d my-lib.core my-lib.core-2 x.y-z x.y z]]
    (is (= (count names) (count (set (map output/ns->path names))))))
  ;; and a namespace that would need a file named .js is refused before a path is
  ;; computed, by the precondition ns-alias already carries
  (are [ns-sym] (thrown? Exception (output/ns->path ns-sym))
    'a.b.
    '.a
    'a..b))

(deftest test-a-specifier-becomes-a-file-under-npm
  (are [specifier path] (= path (output/js->path specifier))
    "react"                 "npm/react.js"
    ;; a sub-path IS a path here, unlike in the alias: it becomes directories, so
    ;; the tree under npm/ looks like node_modules does
    "react-dom/client"      "npm/react-dom/client.js"
    "@visx/scale"           "npm/@visx/scale.js"
    "date-fns/locale/en-GB" "npm/date-fns/locale/en-GB.js"
    ;; .js appended even when the specifier already ends in one, because "sse" and
    ;; "sse.js" are two packages and skipping it would give them one file
    "sse.js"                "npm/sse.js.js"))

(deftest test-the-specifier-path-is-injective
  (let [specs ["react" "react-dom" "react-dom/client" "sse" "sse.js"
               "@visx/scale" "@visx/shape" "date-fns/sub" "date-fns/locale/da"]]
    (is (= (count specs) (count (set (map output/js->path specs)))))))

(deftest test-what-is-not-a-package
  ;; each refused for a reason of its own, and none of them is "unsupported": a
  ;; relative specifier is a different feature, and the rest could not be a file
  ;; under the output root at all
  (are [specifier] (thrown? Exception (output/js->path specifier))
    ""
    "./beside-the-source.js"
    "../up.js"
    "/absolute"
    "react/"
    "react//dom"
    "react/../dom"
    "a b"
    "a\"b"
    "a?b"
    "a#b"
    ;; the ClojureScript spelling of an export, which this compiler has an option
    ;; for - so taking it literally would name a file no bundler builds
    "date-fns/sub$default"))

(deftest test-the-dollar-suffix-is-not-part-of-the-file-name
  ;; a $ is the sugar for a property path INTO the module (doc/cljs-npm.md 4), and
  ;; the analyzer splits it off where the ns form is read - so what names a file is
  ;; the module half, and one arriving here unsplit is a bug rather than a package.
  ;; The message names the module it would have meant.
  (let [msg (or (h/message #(output/js->path "react-useportal$default")) "")]
    (is (re-find #"names a path INSIDE the module" msg))
    (is (re-find #"\"react-useportal\"" msg)))
  ;; and the two halves of one do name the same file as the module alone, which is
  ;; why they are one import between them
  (is (= "npm/date-fns/sub.js" (output/js->path "date-fns/sub"))))

(deftest test-a-module-names-another-file-relatively
  (are [from to spec] (= spec (output/specifier from to))
    'app.core "runtime.js"        "../../runtime.js"
    'app      "runtime.js"        "../runtime.js"
    'a.b.c.d  "runtime.js"        "../../../../runtime.js"
    ;; a sibling namespace, with the shared directories cancelled
    'app.core "ns/app/util.js"    "./util.js"
    'app.core "ns/my-lib/core.js" "../my-lib/core.js"
    'app      "ns/other.js"       "./other.js")
  ;; never bare: a specifier without ./ or ../ is a package lookup, not a path
  (is (every? #(or (str/starts-with? % "./") (str/starts-with? % "../"))
              (for [from '[app app.core a.b.c]
                    to   ["runtime.js" "ns/app/core.js" "ns/x.js"]]
                (output/specifier from to)))))

(h/deftest-when h/node? test-the-two-implementations-of-the-path-agree
  ;; runtime.js states the layout a second time, because $CLJS.require computes a
  ;; URL from a name with nothing to ask the JVM. Two statements of one rule drift
  ;; unless something runs them against each other, so this does - it is the only
  ;; reason the JVM half is public.
  (let [names '[app app.core a.b.c.d my-lib.core x9.core-2]
        js    (str "console.log(JSON.stringify(["
                   (str/join ", " (map #(str "\"" % "\"") names))
                   "].map((n) => $CLJS.urlFor(n))));")]
    ;; a JSON array of strings reads as a Clojure vector of strings
    (is (= (mapv #(str "./" (output/ns->path %)) names)
           (read-string (h/run-js js))))))

(h/deftest-when h/node? test-the-two-implementations-of-the-npm-path-agree
  ;; the same standoff one tree over: $CLJS.requireJs computes a URL from a
  ;; specifier, so runtime.js states js->path a second time and this is what keeps
  ;; the two from drifting apart
  (let [specs ["react" "react-dom/client" "@visx/scale" "sse.js"
               "date-fns/locale/en-GB"]
        js    (str "console.log(JSON.stringify(["
                   (str/join ", " (map #(str "\"" % "\"") specs))
                   "].map((n) => $CLJS.urlForJs(n))));")]
    (is (= (mapv #(str "./" (output/js->path %)) specs)
           (read-string (h/run-js js))))))

(deftest test-the-prelude-is-written-with-its-package-json
  (let [dir (doto (File. (System/getProperty "java.io.tmpdir")
                         (str "cljs-out-" (System/nanoTime)))
              (.deleteOnExit))]
    (try
      (output/write-prelude! dir)
      (is (str/includes? (slurp (File. dir "runtime.js")) "$CLJS"))
      ;; one package.json at the root makes every .js under it - ns/ included - an
      ;; ES module for node rather than CommonJS
      (is (= "{\"type\": \"module\"}\n" (slurp (File. dir "package.json"))))
      (finally (run! #(.delete ^File %) (reverse (file-seq dir)))))))
