;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "JavaScript that remembers where it came from, and the Source Map v3
  file that says so.

  Two halves, and the first is the one that made this hard.

  THE PROBLEM. Destination-driven emission (doc/cljs-compiler.md §5.1) returns
  `{:stmts [...] :expr \"...\"}` - plain strings, built with `str`, with no node
  attached. Output line numbers were said to be free, because a script is a vector
  of one-string-per-line and an output line is an index into it; what was not free
  was everything INSIDE a line, and in particular the body of a function, which
  emit-fn joins into a single multi-line `:expr` string. Function bodies are where
  the program is, so a map that could not see inside one would map nothing worth
  mapping. Retrofitting provenance through every emit* was the budgeted price
  (doc/cljs-repl.md R2).

  THE PRICE WAS NOT PAID, because of one observation: CONCATENATION IS
  CONCATENATION OF LINES. If a chunk of text knows the source position of each of
  its own lines, then the lines of `(str a b)` are the lines of a followed by the
  lines of b - with a's last and b's first being the SAME line, since nothing
  separates them, and a's position winning because it starts earlier. That is the
  whole composition rule, and it is exact rather than approximate.

  So a chunk is:

      text    the JavaScript
      lines   one source position per line of `text`, nil where unknown
              (count lines) = 1 + the number of newlines in text

  and `cat` is `str` with that rule. The emitter refers-clojure-excludes `str` and
  refers this one instead, so EVERY existing str call in it composes positions
  without being rewritten - which is why the retrofit is one line of ns form and
  not eighty of edits. A Src is a CharSequence, so anything downstream that only
  wants the text gets it from `str` or `.toString` as before.

  `cat` returns a plain String when no argument carries a position. That is not
  only an optimisation: it means a compile that never ran clojure.cljs.source-info
  produces exactly the strings it produced before, so nothing that does not ask for
  a source map pays for one, in allocation or in behaviour.

  THE SECOND HALF is the file format, which is small once the first half exists:
  one mapping per generated line, at generated column 0. A consumer looking up
  column 30 of generated line 5 finds the greatest mapping at or before it, so a
  per-line mapping answers every column of that line - enough for a stack frame and
  enough for devtools to highlight a line. Per-EXPRESSION mappings would need
  generated columns, which means tracking the width of everything emitted, and buy
  a precision no consumer of ours asks for yet.

  WHAT IS NOT HERE: `names`, which maps a generated identifier back to its source
  name. Ours are already legible - x__3 is x, and demunging is a pure function of
  the name (§5.38) - so the array stays empty.

  AND A THIRD HALF, ADDED LATER: `decode` and `position`, which read a map back.
  They are here rather than in a namespace of their own so that the format has ONE
  description and both directions read it - encode converts a position to the
  file's zero-based counting and position converts it back, at the same door. The
  consumer is clojure.cljs.stacktrace (§5.45).

  doc/cljs-compiler.md §5.43, §5.45."}
  clojure.cljs.source-map
  (:refer-clojure :exclude [cat])
  (:require [clojure.string :as str])
  (:import [clojure.lang IPersistentVector]
           [java.util Base64]))

;; --- text that remembers -----------------------------------------------------

(deftype Src [^String text ^IPersistentVector lines]
  CharSequence
  (toString [_] text)
  (length [_] (.length text))
  (charAt [_ i] (.charAt text i))
  (subSequence [_ a b] (.subSequence text a b)))

(defn- newline-count
  "How many newlines are in `s` - which is one fewer than the number of lines it
  has, and the invariant every line vector here is sized by."
  ^long [^String s]
  (loop [i 0, n 0]
    (let [j (.indexOf s (int \newline) i)]
      (if (neg? j) n (recur (inc j) (inc n))))))

(defn- blank-lines
  "The line vector of text nothing has placed: one nil per line."
  [^String s]
  (vec (repeat (inc (newline-count s)) nil)))

(defn text
  "The JavaScript in `x`, whether or not it carries positions."
  ^String [x]
  (if (instance? Src x) (.text ^Src x) (clojure.core/str x)))

(defn line-positions
  "One source position per line of `x`, nil where nothing placed that line.

  Always (inc newlines) long, so a caller can zip it against the lines of the
  text without checking."
  [x]
  (if (instance? Src x) (.lines ^Src x) (blank-lines (clojure.core/str x))))

(defn- splice
  "The line vectors of two chunks laid end to end. Their adjacent lines - a's last
  and b's first - are one line, because nothing separates them, and it is a's
  position that stands: a started the line."
  [a b]
  (into (conj (pop a) (or (peek a) (nth b 0))) (subvec b 1)))

(defn- cat*
  "`str` over a seq, composing positions. See the namespace docstring."
  [parts]
  (if-not (some #(instance? Src %) parts)
    (apply clojure.core/str parts)
    (let [sb (StringBuilder.)
          ls (reduce (fn [acc p]
                       (let [^String t (text p)]
                         (.append sb t)
                         (let [pl (if (instance? Src p) (.lines ^Src p) (blank-lines t))]
                           (if (nil? acc) pl (splice acc pl)))))
                     nil parts)]
      (Src. (.toString sb) ls))))

(defn cat
  "The emitter's `str`: text, and the source positions of its lines.

  Identical to clojure.core/str for arguments that carry no position, down to
  returning a String rather than a chunk."
  ([] "")
  ([x] (if (instance? Src x) x (clojure.core/str x)))
  ([x y] (cat* [x y]))
  ([x y & more] (cat* (list* x y more))))

(defn join
  "`sep` between each of `parts`, composing positions.

  The one that matters is (join \"\\n\" lines): the newline before a line is what
  makes that line a line, so the line's own position becomes the position of the
  line it starts. Nothing special is needed for it - splice says so already."
  [sep parts]
  (cat* (interpose sep parts)))

(defn fill
  "`x` with `pos` written onto every line of it that nothing has placed.

  THE RULE IS THE SAME ONE clojure.cljs.source-info uses on the tree: a line
  belongs to the nearest enclosing node that claims it. Filling happens innermost
  first - ->result runs as each node's emit returns - so the innermost claim
  stands, and an outer fill finds nothing left to do.

  Returns `x` itself when there is nothing to write, which is the common case
  after the first fill and the only case when no source map is being made."
  [pos x]
  (cond
    (nil? pos) x

    (instance? Src x)
    (let [ls (.lines ^Src x)]
      (if (some nil? ls)
        (Src. (.text ^Src x) (mapv #(or % pos) ls))
        x))

    :else
    (let [^String s (clojure.core/str x)]
      (Src. s (vec (repeat (inc (newline-count s)) pos))))))

;; --- JSON --------------------------------------------------------------------

(defn json-string
  "`s` as a JSON string literal.

  Control characters are escaped because JSON.parse refuses a raw one - and both
  things written through this hold arbitrary text: a source map embeds whole
  ClojureScript files in sourcesContent, and clojure.cljs.repl sends emitted
  JavaScript, which js* lets hold any character at all."
  [^String s]
  (let [sb (StringBuilder. "\"")]
    (dotimes [i (.length s)]
      (let [c (.charAt s i)]
        (case c
          \"         (.append sb "\\\"")
          \\         (.append sb "\\\\")
          \newline   (.append sb "\\n")
          \return    (.append sb "\\r")
          \tab       (.append sb "\\t")
          \backspace (.append sb "\\b")
          \formfeed  (.append sb "\\f")
          (if (< (int c) 0x20)
            (.append sb (format "\\u%04x" (int c)))
            (.append sb c)))))
    (clojure.core/str (.append sb \"))))

;; --- the v3 file -------------------------------------------------------------

(def ^:private base64-digits
  "The alphabet VLQ digits are spelled in. Not the same thing as base64 ENCODING a
  byte string, which is what an inline map's data: URL is - that one is
  java.util.Base64, below."
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

(defn- vlq!
  "Append `n` as a base64 VLQ: the sign goes in the LOW bit, and each digit
  carries five bits with the sixth set while more follow."
  [^StringBuilder sb ^long n]
  (loop [v (if (neg? n) (bit-or (bit-shift-left (- n) 1) 1) (bit-shift-left n 1))]
    (let [digit (bit-and v 0x1f)
          rest  (unsigned-bit-shift-right v 5)]
      (if (pos? rest)
        (do (.append sb (.charAt base64-digits (bit-or digit 0x20)))
            (recur rest))
        (.append sb (.charAt base64-digits digit))))))

(defn- mappings
  "The `mappings` field: one generated line per semicolon, and in each line at most
  one segment, at generated column 0.

  Every field but the generated column is a DELTA against the last segment
  written, across the whole file rather than the line - which is why a generated
  line with no position writes nothing and shifts nothing."
  [positions index-of]
  (let [sb (StringBuilder.)]
    (loop [ps (seq positions), first? true, ps' 0, pl 0, pc 0]
      (if-not ps
        (.toString sb)
        (let [p (first ps)]
          (when-not first? (.append sb \;))
          (if-not (and p (:file p) (:line p))
            (recur (next ps) false ps' pl pc)
            (let [si (index-of (:file p))
                  l  (dec (long (:line p)))
                  c  (dec (long (or (:column p) 1)))]
              (.append sb \A)                 ; generated column 0, always
              (vlq! sb (- si ps'))
              (vlq! sb (- l pl))
              (vlq! sb (- c pc))
              (recur (next ps) false si l c))))))))

(defn encode
  "A Source Map v3 document, as JSON.

    :file       the generated file this maps, as it is named on disk
    :positions  one source position (or nil) per line of the generated file
    :content    {source-path -> the text of that source}, embedded verbatim

  The sources are the distinct :file values of `positions`, in the order they are
  first mentioned. A position naming a source `:content` has nothing for gets a
  null in sourcesContent, which is the format's way of saying \"fetch it\" - and
  the one case we do not want, since a REPL input is not on disk anywhere.

  SOURCES ARE EMBEDDED RATHER THAN REFERENCED, and that is a decision worth
  stating: it makes a .js.map self-contained, so devtools shows ClojureScript
  without the source tree being reachable from wherever the output is served, and
  it is the only thing that CAN work for a REPL input, which has no URL at all.
  The cost is the source text once per map."
  [{:keys [file positions content]}]
  (let [sources (into [] (comp (filter :line) (keep :file) (distinct)) positions)
        idx     (zipmap sources (range))]
    (clojure.core/str
     "{\"version\":3"
     ",\"file\":" (json-string (clojure.core/str file))
     ",\"sources\":[" (str/join "," (map json-string sources)) "]"
     ",\"sourcesContent\":[" (str/join
                              ","
                              (map #(if-let [c (get content %)] (json-string c) "null")
                                   sources))
     "]"
     ",\"names\":[]"
     ",\"mappings\":" (json-string (mappings positions idx))
     "}")))

(defn data-url
  "`json` as a data: URL, for a //# sourceMappingURL that has nowhere to point.

  A REPL input is evaluated, not fetched, so there is no file beside it for a map
  to live in; the map has to travel in the comment itself."
  [^String json]
  (clojure.core/str
   "data:application/json;charset=utf-8;base64,"
   (.encodeToString (Base64/getEncoder) (.getBytes json "UTF-8"))))

;; --- reading one back --------------------------------------------------------
;;
;; The inverse of everything above, which is here rather than in a namespace of its
;; own so that the format has ONE description and both directions read it. The
;; consumer is clojure.cljs.stacktrace: a frame says demo/core.js:9:10 and a REPL
;; user wants demo/core.cljs:5:4.
;;
;; A source map is JSON, so the JVM has to read JSON - which is the one place it
;; does. clojure.cljs.repl says the JVM writes JSON and node writes EDN so that
;; neither parses the format it is worst at, and that stays true of the WIRE; a map
;; is not on the wire. It is a file, in a format devtools also reads, so its shape
;; is not ours to choose.

(defn- skip-ws ^long [^String s ^long i]
  (loop [i i]
    (if (and (< i (.length s)) (Character/isWhitespace (.charAt s i)))
      (recur (inc i))
      i)))

(defn- read-json-string
  "The string literal starting at `i` (which holds the opening quote), as
  [value next-index].

  JSON's escapes are not EDN's - \\b and \\f are JSON's and the reader would not
  know them - which is why this cannot be clojure.edn/read-string on a literal that
  happens to look similar."
  [^String s ^long i]
  (let [sb (StringBuilder.)]
    (loop [i (inc i)]
      (let [c (.charAt s i)]
        (cond
          (= c \")  [(.toString sb) (inc i)]
          (= c \\)  (let [e (.charAt s (inc i))]
                      (if (= e \u)
                        (do (.append sb (char (Integer/parseInt (subs s (+ i 2) (+ i 6)) 16)))
                            (recur (+ i 6)))
                        (do (.append sb (case e
                                          \b \backspace
                                          \f \formfeed
                                          \n \newline
                                          \r \return
                                          \t \tab
                                          e))
                            (recur (+ i 2)))))
          :else     (do (.append sb c) (recur (inc i))))))))

(declare ^:private read-json)

(defn- read-json-seq
  "The members of an array or object, from just after its opening bracket, until
  `close`. `member` reads one and returns [value next-index]."
  [^String s ^long i close member]
  (loop [i (skip-ws s i), acc []]
    (if (= close (.charAt s i))
      [acc (inc i)]
      (let [[v i] (member s i)
            i     (skip-ws s i)]
        (if (= \, (.charAt s i))
          (recur (skip-ws s (inc i)) (conj acc v))
          [(conj acc v) (inc i)])))))

(defn- read-json-entry [^String s ^long i]
  (let [[k i] (read-json-string s i)
        i     (skip-ws s i)
        [v i] (read-json s (skip-ws s (inc i)))]      ; (inc i) steps over the colon
    [[k v] i]))

(defn- read-json
  "One JSON value at `i`, as [value next-index]. An object becomes a map with
  STRING keys, an array a vector, a number a long or a double."
  [^String s ^long i]
  (let [c (.charAt s i)]
    (cond
      (= c \{) (let [[kvs i] (read-json-seq s (inc i) \} read-json-entry)]
                 [(into {} kvs) i])
      (= c \[) (let [[vs i] (read-json-seq s (inc i) \] read-json)] [vs i])
      (= c \") (read-json-string s i)
      (.startsWith s "true" i)  [true (+ i 4)]
      (.startsWith s "false" i) [false (+ i 5)]
      (.startsWith s "null" i)  [nil (+ i 4)]
      :else
      (let [end (long (loop [j i]
                        (if (and (< j (.length s))
                                 (not (Character/isWhitespace (.charAt s j)))
                                 (not (#{\, \] \}} (.charAt s j))))
                          (recur (inc j))
                          j)))
            t   (subs s i end)]
        [(if (re-find #"[.eE]" t) (Double/parseDouble t) (Long/parseLong t)) end]))))

(def ^:private base64-values
  "The inverse of base64-digits. Beside it on purpose: two tables that had to agree
  and did not would be a bug nothing would catch until a map was read by something
  other than us."
  (into {} (map-indexed (fn [i c] [c i])) base64-digits))

(defn- vlq-values
  "The integers one base64 VLQ segment spells. The inverse of vlq!, and the sign is
  where vlq! put it: the low bit of the assembled value."
  [^String seg]
  (loop [i 0, shift 0, acc 0, out []]
    (if (>= i (.length seg))
      out
      (let [d (long (base64-values (.charAt seg i)))
            a (+ acc (bit-shift-left (bit-and d 0x1f) shift))]
        (if (pos? (bit-and d 0x20))
          (recur (inc i) (+ shift 5) a out)
          (recur (inc i) 0 0
                 (conj out (let [v (unsigned-bit-shift-right a 1)]
                             (if (odd? a) (- v) v)))))))))

(defn- decode-mappings
  "The `mappings` field as one vector per generated line, each holding that line's
  segments in generated-column order:

      {:column 0 :source 0 :line 4 :source-column 13}

  all four counted from zero, as the file counts them. A segment of fewer than four
  fields names no source - it says only that a generated column exists - so it
  advances the column and contributes nothing.

  THE GENERATED COLUMN RESETS AT EVERY LINE and the other three do not: they are
  deltas across the whole file, which is what lets a generated line with no segment
  shift nothing. Ours writes at most one segment per line, at column 0 (mappings
  above), but nothing here assumes that - a map from another tool reads the same."
  [^String s]
  (first
   (reduce
    (fn [[lines psrc pline pcol] ^String line]
      (let [[segs psrc pline pcol]
            (reduce
             (fn [[segs psrc pline pcol gcol] ^String seg]
               (let [v (vlq-values seg)]
                 (if (< (count v) 4)
                   [segs psrc pline pcol (+ gcol (long (or (first v) 0)))]
                   (let [gc (+ gcol (long (nth v 0)))
                         sr (+ psrc (long (nth v 1)))
                         sl (+ pline (long (nth v 2)))
                         sc (+ pcol (long (nth v 3)))]
                     [(conj segs {:column gc :source sr :line sl :source-column sc})
                      sr sl sc gc]))))
             [[] psrc pline pcol 0]
             (str/split line #"," -1))]
        [(conj lines segs) psrc pline pcol]))
    [[] 0 0 0]
    (str/split s #";" -1))))

(defn decode
  "A Source Map v3 document as data:

    :file      the generated file it maps
    :sources   the source paths, in the order the mappings index them
    :content   one entry per source - its text, or nil where the map only names it
    :lines     one vector of segments per generated line (decode-mappings)

  The inverse of encode, for the fields encode writes. `names` is not read because
  ours is always empty and nothing here would use it."
  [^String json]
  (let [m (first (read-json json (skip-ws json 0)))]
    {:file    (get m "file")
     :sources (vec (get m "sources"))
     :content (vec (get m "sourcesContent"))
     :lines   (decode-mappings (or (get m "mappings") ""))}))

(defn position
  "Where generated `line`:`column` came from, as {:file :line :column}, or nil if
  that line maps nowhere.

  ONE-BASED ON BOTH SIDES, which is not how the file counts. Source Map v3 counts
  lines and columns from zero; a stack frame, an editor and a person all count from
  one. encode does the conversion going out, so this does it coming back, and the
  format's zeroes stay inside this namespace.

  THE GREATEST SEGMENT AT OR BEFORE THE COLUMN, which is the format's own lookup
  rule and is the reason one mapping per generated line answers every column of
  that line. A column before the first segment of its line maps nowhere - the
  format has no way to say what was there - and a call with no column at all takes
  the line's first segment, which is what a frame that lost its column wants."
  ([m line] (position m line nil))
  ([m line column]
   (when-let [segs (seq (get (:lines m) (dec (long line))))]
     (let [seg (if (nil? column)
                 (first segs)
                 (last (take-while #(<= (long (:column %)) (dec (long column))) segs)))]
       (when seg
         {:file   (get (:sources m) (:source seg))
          :line   (inc (long (:line seg)))
          :column (inc (long (:source-column seg)))})))))

(defn source-text
  "The text of `path` as the map embedded it, or nil. What makes a map
  self-contained also makes it the only copy of a REPL input that exists."
  [m path]
  (when-let [i (first (keep-indexed #(when (= path %2) %1) (:sources m)))]
    (get (:content m) i)))
