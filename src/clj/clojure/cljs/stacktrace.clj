;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "A JavaScript stack trace, read back as ClojureScript.

  The consumer of the source maps clojure.cljs.source-map writes. A runtime hands
  the JVM `e.stack` verbatim (runtime.js), which reads

      Error: boom 42
          at demo$core$boom (file:///tmp/out/ns/demo/core.js:9:10)
          at demo$core$outer (file:///tmp/out/ns/demo/core.js:12:28)
          at eval (repl/cljs.user/1.js:7:39)
          at process.processTicksAndRejections (node:internal/process/task_queues:104:5)
          at async evaluate (file:///tmp/out/runtime.js:296:39)

  and what a REPL user wants to see is

          at demo.core/boom (demo/core.cljs:5:11)
          at demo.core/outer (demo/core.cljs:8:3)
          at eval (repl/cljs.user/1.js:7:39)

  THREE THINGS HAPPEN AND THEY ARE INDEPENDENT.

    THE LOCATION is looked up in the .js.map beside the file the frame names, which
    is where the driver wrote it (§5.43). One mapping per generated line means the
    answer is the line's, which is what a stack frame needs and all it needs.

    THE NAME is demunged - demo$core$boom is demo.core/boom - by the rule
    cljs.spec.alpha's fn-sym uses on the same names: split on $, demunge each
    piece, join all but the last with dots (see clojure.cljs.names/var-fn-name,
    §5.34). Lossy, as that name is: a-b and a_b are one name. Best effort, so a
    name that does not read as one is left exactly as it came.

    THE NOISE below the last ClojureScript frame is dropped - node's internals and
    the prelude's own entry points, which are the same three lines under every
    error and are never the mistake. TRAILING only: a machinery frame between two
    of yours is something you called through, and stays.

  WHAT IS NOT MAPPED, and is one milestone away rather than one bug: a form TYPED
  at the REPL. Its script carries a fresh repl/<ns>/<n>.js (§5.42) and no map,
  because a map needs the source text and the REPL does not keep what it read. The
  frame still names the input, which is what §5.42 bought; it does not yet name the
  form. See doc/cljs-repl.md R2.

  NOTHING HERE FETCHES. The maps are read off the output directory, so this works
  the same for a browser - whose frames spell the same files as http: URLs - as for
  node, and it needs no runtime surface at all.

  doc/cljs-compiler.md §5.45, doc/cljs-repl.md R2."}
  clojure.cljs.stacktrace
  (:require [clojure.cljs.source-map :as sm]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io File]
           [java.net URI]))

;; --- the frames -------------------------------------------------------------

(def ^:private named-frame
  "    at <name> (<url>:<line>:<column>)

  The name is NON-GREEDY so that it ends at the first \" (\": V8 has one older shape
  that nests a location inside the name - `at eval (eval at evaluate (…), …)` -
  which §5.42 stopped us producing, and stopping at the first bracket leaves it
  unresolvable rather than resolved wrongly."
  #"^(\s*)at (.+?) \((.+):(\d+):(\d+)\)$")

(def ^:private bare-frame
  "    at <url>:<line>:<column> - a frame in code with no enclosing function."
  #"^(\s*)at (.+):(\d+):(\d+)$")

(def ^:private frame-words
  "Words V8 puts in front of the thing a frame names: `async` where the frame is
  suspended at an await, `new` where it is a constructor call."
  ["async " "new "])

(defn- prefixed
  "[prefix rest]. The words above belong to the FRAME and not to the name, so they
  come off before anything tries to read one - and `async` can sit in front of a
  URL, where left alone it would make a path with a space in it, which is exactly
  what `located` must not resolve."
  [^String s]
  (loop [s s, acc ""]
    (if-let [w (some #(when (str/starts-with? s %) %) frame-words)]
      (recur (subs s (count w)) (str acc w))
      [acc s])))

(defn frames
  "A stack string as one map per line:

    :raw     the line, which is the answer for anything not a frame - the first
             line of a V8 stack is the error's own message, not a frame
    :indent  the whitespace it came with, so the shape survives a rewrite
    :name    the function, as JavaScript spells it; absent on a bare frame
    :prefix  what V8 wrote in front of it - \"async \", \"new \", or nothing
    :url     :line :column   where the frame is, in the GENERATED file"
  [^String stack]
  (mapv (fn [line]
          (if-let [[_ indent nm url l c] (re-matches named-frame line)]
            (let [[prefix nm] (prefixed nm)]
              {:raw line :indent indent :name nm :prefix prefix :url url
               :line (parse-long l) :column (parse-long c)})
            (if-let [[_ indent url l c] (re-matches bare-frame line)]
              (let [[prefix url] (prefixed url)]
                {:raw line :indent indent :prefix prefix :url url
                 :line (parse-long l) :column (parse-long c)})
              {:raw line})))
        (str/split-lines stack)))

;; --- where a frame points ---------------------------------------------------

(defn- under
  "`f` as a path relative to `dir`, spelled with forward slashes, or nil when it is
  not under it. The relative path is what a user recognises and what the map is
  found beside."
  [^File dir ^File f]
  (let [d (str (.getCanonicalPath dir) File/separator)
        p (.getCanonicalPath f)]
    (when (.startsWith p d)
      (str/replace (subs p (count d)) File/separatorChar \/))))

(defn- located
  "[file relative-path] for the file under `dir` that `url` names, or nil.

  Three spellings reach here and they are the same file: a file: URL, which is what
  node gives for a module it imported; an http: URL, which is what a browser gives
  for that file served over the wire; and a bare relative path, which is what a
  //# sourceURL puts on an eval'd script (§5.42). Anything that does not land under
  `dir` is not ours - node: internals, and whatever else a host puts on a stack."
  [^File dir ^String url]
  (when-let [f (try
                 (cond
                   (str/starts-with? url "file:") (io/file (URI. url))
                   (re-find #"^https?:" url)      (io/file dir (subs (.getPath (URI. url)) 1))
                   (re-find #"^[A-Za-z][-+.A-Za-z0-9]*:" url) nil   ; node:, data:, …
                   ;; a relative path is a //# sourceURL and those we write; a
                   ;; space in one means it is something else wearing the shape
                   (re-find #"\s" url)            nil
                   :else                          (io/file dir url))
                 (catch Exception _ nil))]
    (when-let [rel (under dir f)]
      [f rel])))

(def ^:private decoded
  "Decoded maps, keyed by a .map file and the time it was last written.

  A map is a pure function of its file, so this caches a value and not a state, and
  a recompile that rewrites the file changes the key. Worth having rather than
  obvious: cljs.core's map is half a megabyte of JSON, and without this a session
  would decode it once per frame of every stack."
  (atom {}))

(defn- map-for
  "The decoded map beside `js`, or nil - there is none for a script that was
  evaluated rather than fetched, and none for a file compiled before §5.43."
  [^File js]
  (let [f (io/file (str (.getPath js) ".map"))]
    (when (.isFile f)
      (let [k [(.getCanonicalPath f) (.lastModified f)]
            v (get @decoded k ::miss)]
        (if (identical? ::miss v)
          (let [m (try (sm/decode (slurp f)) (catch Exception _ nil))]
            (swap! decoded assoc k m)
            m)
          v)))))

(defn symbolicate
  "`frames`, with each frame that names a file under `dir` given

    :file    that file's path relative to `dir`
    :source  where it came from - {:file :line :column} - when a map says

  and every other frame left as it was."
  [dir ^String stack]
  (let [^File dir (io/file dir)]
    (mapv (fn [frame]
            (if-let [[f rel] (and (:url frame) (located dir (:url frame)))]
              (assoc frame
                     :file rel
                     :source (when-let [m (map-for f)]
                               (sm/position m (:line frame) (:column frame))))
              frame))
          (frames stack))))

;; --- how it reads ------------------------------------------------------------

(defn- demunged
  "`js` as the qualified symbol it was munged from, or nil.

  cljs.spec.alpha's rule (clojure.cljs.names/var-fn-name, §5.34): the pieces
  between $ are namespace segments and the last is the name. clojure.lang.Compiler
  owns the inverse of the character map - names/char-map is Clojure's own - so
  there is no second table here to disagree with the first.

  nil for anything that does not read as a var name, which is most of what a stack
  carries: eval, process.processTicksAndRejections, an anonymous frame."
  [^String js]
  (let [parts (str/split js #"\$")]
    (when (and (> (count parts) 1)
               (every? seq parts)
               (not (str/includes? js " "))
               (not (str/includes? js ".")))
      (str (str/join "." (map #(clojure.lang.Compiler/demunge %) (butlast parts)))
           "/" (clojure.lang.Compiler/demunge ^String (last parts))))))

(def ^:private prelude
  "The runtime's own files. A frame in one of them is the machinery that evaluated
  your form, not your form."
  #{"runtime.js" "runtime_node.js" "runtime_browser.js"})

(defn- machinery?
  [frame]
  (boolean (and (:url frame)
                (or (nil? (:file frame))
                    (contains? prelude (:file frame))))))

(defn- render
  [frame]
  (let [{:keys [indent name prefix source file line column raw]} frame
        at  (str indent "at " prefix)
        loc (cond
              source (str (:file source) ":" (:line source) ":" (:column source))
              file   (str file ":" line ":" column))]
    (cond
      (nil? loc) raw
      name       (str at (or (demunged name) name) " (" loc ")")
      :else      (str at loc))))

(defn trace
  "The stack as a REPL should print it, or `stack` unchanged when there is no
  output directory to read maps out of.

  TWO THINGS ARE DROPPED and both are already on the screen or never were:

    THE FIRST LINE, which is the error's message - the REPL prints that as the
    result, so a stack that repeats it says one thing twice.

    THE TRAILING MACHINERY, which is node's internals and the prelude's entry
    points. Trailing only, and the word is load-bearing: a machinery frame between
    two of yours is something your code called through, and dropping it would hide
    the call."
  [dir ^String stack]
  (if (or (nil? dir) (str/blank? stack))
    stack
    (let [fs (symbolicate dir stack)
          fs (if (and (seq fs) (nil? (:url (first fs)))) (subvec fs 1) fs)
          n  (count (take-while machinery? (rseq fs)))]
      (str/join "\n" (map render (subvec fs 0 (- (count fs) n)))))))
