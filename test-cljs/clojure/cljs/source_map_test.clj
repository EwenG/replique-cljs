;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Text that remembers where it came from, and the v3 file that says so.

  TWO HALVES, TESTED DIFFERENTLY.

  The composition rule is an algebraic claim - the lines of (str a b) are the lines
  of a followed by the lines of b, sharing one line where they meet - so it is
  tested as an algebraic claim, on chunks built by hand, without a compiler
  anywhere near it.

  The file format is a claim about a wire format, so the test DECODES rather than
  compares text, through the second implementation of base64 VLQ that lives in the
  harness (h/map-positions). An encoder tested against a string constant tests
  that nobody edited the constant.

  What is NOT here is a compile: clojure.cljs.driver-test maps real output. This is
  the layer under it."}
  clojure.cljs.source-map-test
  (:require [clojure.cljs.source-map :as sm]
            [clojure.cljs.test-harness :as h]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]))

;; --- the composition rule ----------------------------------------------------

(defn- mappings-of
  "The raw `mappings` field, for the two assertions that are about its spelling."
  [json]
  (second (re-find #"\"mappings\":\"([^\"]*)\"" json)))

(def ^:private p1 {:file "a.cljs" :line 1 :column 1})
(def ^:private p2 {:file "a.cljs" :line 2 :column 3})
(def ^:private p3 {:file "a.cljs" :line 9 :column 5})

(deftest test-text-that-carries-nothing-is-a-string
  ;; not an optimisation but the compatibility rule: a compile that never ran
  ;; clojure.cljs.source-info produces exactly the strings it produced before, so
  ;; nothing that does not want a map pays for one.
  (is (string? (sm/cat "a" "b" "c")))
  (is (string? (sm/join ", " ["a" "b"])))
  (is (= "abc" (sm/cat "a" "b" "c")))
  (is (= [nil nil] (sm/line-positions "a\nb"))))

(deftest test-a-chunk-is-a-charsequence
  ;; everything downstream that only wants the text gets it the way it always did
  (let [c (sm/fill p1 "foo\nbar")]
    (is (= "foo\nbar" (str c)))
    (is (= "foo\nbar" (sm/text c)))
    (is (= 7 (count c)))
    (is (str/includes? c "oo\nba"))))

(deftest test-concatenation-is-concatenation-of-lines
  ;; the whole rule. a's lines, then b's, with a's LAST and b's FIRST being one
  ;; line - nothing separates them - and a's position winning it, because a's line
  ;; started first.
  (let [a (sm/fill p1 "one\ntwo")
        b (sm/fill p2 "three\nfour")]
    (is (= "one\ntwothree\nfour" (sm/text (sm/cat a b))))
    (is (= [p1 p1 p2] (sm/line-positions (sm/cat a b))))
    ;; three lines, not four: the join is one line
    (is (= 3 (count (sm/line-positions (sm/cat a b)))))))

(deftest test-an-unplaced-part-does-not-claim-the-line-it-lands-on
  ;; (str "let x = " <a function expression>) - the prefix carries no position, so
  ;; the line belongs to what does.
  (let [f (sm/fill p3 "(function () {\n  return 1;\n})")
        s (sm/cat "let x = " f ";")]
    (is (= "let x = (function () {\n  return 1;\n});" (sm/text s)))
    (is (= [p3 p3 p3] (sm/line-positions s)))))

(deftest test-joining-lines-gives-each-line-its-own-position
  ;; the case the emitter is built on: a vector of statements joined by newlines.
  ;; The newline BEFORE a line is what makes it a line, so the line's own position
  ;; becomes that line's - and nothing in cat has to know it is happening.
  (let [ls [(sm/fill p1 "a();") (sm/fill p2 "b();") "c();"]]
    (is (= "a();\nb();\nc();" (sm/text (sm/join "\n" ls))))
    (is (= [p1 p2 nil] (sm/line-positions (sm/join "\n" ls))))))

(deftest test-fill-writes-only-where-nothing-has-been-written
  ;; the same rule clojure.cljs.source-info uses on the tree: the innermost node
  ;; that claims a line keeps it, and an enclosing one finds nothing to do.
  (let [inner (sm/fill p3 "x")
        outer (sm/fill p1 (sm/cat "f(" inner ");"))]
    (is (= [p3] (sm/line-positions outer)))
    (is (identical? outer (sm/fill p2 outer))))
  ;; and a nil position is not a position: filling with one changes nothing
  (is (= "plain" (sm/fill nil "plain")))
  (is (identical? "plain" (sm/fill nil "plain"))))

;; --- the file format ---------------------------------------------------------

(deftest test-a-map-round-trips-through-a-second-decoder
  (let [ps   [nil p1 p2 nil p3]
        json (sm/encode {:file "out.js" :positions ps :content {"a.cljs" "(+ 1 2)\n"}})]
    (is (= [nil ["a.cljs" 1 1] ["a.cljs" 2 3] nil ["a.cljs" 9 5]]
           (h/map-positions json)))
    (is (str/includes? json "\"version\":3"))
    (is (str/includes? json "\"file\":\"out.js\""))
    (is (str/includes? json "\"names\":[]"))))

(deftest test-an-unmapped-line-shifts-nothing
  ;; every field but the generated column is a delta against the LAST SEGMENT
  ;; WRITTEN, not against the previous line - so holes in the middle are free
  (let [dense  (sm/encode {:file "o.js" :positions [p1 p2 p3]})
        sparse (sm/encode {:file "o.js" :positions [p1 nil nil p2 nil p3]})]
    (is (= [["a.cljs" 1 1] ["a.cljs" 2 3] ["a.cljs" 9 5]]
           (h/map-positions dense)))
    (is (= [["a.cljs" 1 1] nil nil ["a.cljs" 2 3] nil ["a.cljs" 9 5]]
           (h/map-positions sparse)))))

(deftest test-several-sources-are-indexed-in-the-order-they-are-mentioned
  (let [b    {:file "b.cljs" :line 4 :column 2}
        json (sm/encode {:file "o.js" :positions [p1 b p2 b]})]
    (is (= ["a.cljs" "b.cljs"] (h/map-sources json)))
    (is (= [["a.cljs" 1 1] ["b.cljs" 4 2] ["a.cljs" 2 3] ["b.cljs" 4 2]]
           (h/map-positions json)))))

(deftest test-the-source-travels-with-the-map
  ;; embedded rather than referenced: it is the only thing that works when the
  ;; source tree is not reachable from wherever the output is served, and the only
  ;; thing that CAN work for a source that is not on disk at all
  (let [json (sm/encode {:file "o.js" :positions [p1] :content {"a.cljs" "(+ 1 2)\n"}})]
    (is (str/includes? json "\"sourcesContent\":[\"(+ 1 2)\\n\"]")))
  ;; and null - the format's "go and fetch it" - when there is nothing to embed
  (let [json (sm/encode {:file "o.js" :positions [p1]})]
    (is (str/includes? json "\"sourcesContent\":[null]"))))

(deftest test-a-position-with-no-file-is-not-a-position
  ;; a node the source-info pass never reached carries no :file, and a segment
  ;; naming source -1 is not something a consumer can read
  (let [json (sm/encode {:file "o.js" :positions [{:line 3} p1]})]
    (is (= ["a.cljs"] (h/map-sources json)))
    (is (= [nil ["a.cljs" 1 1]] (h/map-positions json)))))

(deftest test-vlq-spells-the-values-the-specification-does
  ;; the three worth pinning by hand: zero, the first value that needs a
  ;; continuation digit, and a negative one
  (let [seg (fn [n] (mappings-of (sm/encode {:file "o.js"
                                             :positions [{:file "a" :line 1 :column 1}
                                                         {:file "a" :line (inc n) :column 1}]})))]
    ;; the second line's line delta is n
    (is (= "AAAA;AACA"  (seg 1)))
    ;; 16 doubles to 32, which does not fit in five bits: a low digit of 0 with the
    ;; continuation bit set is 'g', and what is left, 1, is 'B'
    (is (= "AAAA;AAgBA" (seg 16)))
    (is (= [1 16] [(nth (h/vlq-values "AACA") 2) (nth (h/vlq-values "AAgBA") 2)])))
  ;; and going backwards up the file is negative
  (let [json (sm/encode {:file "o.js" :positions [{:file "a" :line 9 :column 1}
                                                  {:file "a" :line 2 :column 1}]})]
    (is (= [["a" 9 1] ["a" 2 1]] (h/map-positions json)))
    (is (= -7 (nth (h/vlq-values (second (str/split (mappings-of json) #";"))) 2)))))

(deftest test-a-data-url-carries-a-whole-map
  (let [json (sm/encode {:file "o.js" :positions [p1] :content {"a.cljs" "(+ 1 2)\n"}})
        url  (sm/data-url json)]
    (is (str/starts-with? url "data:application/json;charset=utf-8;base64,"))
    (is (= json (String. (.decode (java.util.Base64/getDecoder)
                                  (subs url (inc (str/index-of url ","))))
                         "UTF-8")))))

(deftest test-json-escapes-what-json-parse-refuses
  (is (= "\"a\\\"b\"" (sm/json-string "a\"b")))
  (is (= "\"a\\\\b\"" (sm/json-string "a\\b")))
  (is (= "\"a\\nb\"" (sm/json-string "a\nb")))
  ;; a raw control character is a parse error, and js* lets emitted JavaScript hold
  ;; any character at all
  (is (= "\"\\u0001\"" (sm/json-string "\u0001"))))

;; --- reading one back --------------------------------------------------------
;;
;; decode is the inverse of encode and lives beside it, so a round trip proves less
;; than it looks: two implementations wrong the same way would agree. The tests that
;; carry weight here are the ones whose input was NOT produced by encode - a
;; mappings field written out by hand from the specification - and the one that
;; compares decode against the harness's independent reader.

(deftest test-a-mappings-field-written-by-hand-reads-back
  ;; three lines, each one segment, spelled straight from the specification:
  ;; A is 0, C is 1 and E is 2 once the sign bit comes out of the low end
  (let [m (sm/decode (str "{\"version\":3,\"file\":\"o.js\""
                          ",\"sources\":[\"a.cljs\"],\"sourcesContent\":[null]"
                          ",\"names\":[],\"mappings\":\"AAAA;AACA;AAEA\"}"))]
    (is (= "o.js" (:file m)))
    (is (= ["a.cljs"] (:sources m)))
    (is (= [{:file "a.cljs" :line 1 :column 1}
            {:file "a.cljs" :line 2 :column 1}
            {:file "a.cljs" :line 4 :column 1}]
           (mapv #(sm/position m %) [1 2 3])))
    (testing "and a generated line the file does not reach maps nowhere"
      (is (nil? (sm/position m 4))))))

(deftest test-the-greatest-segment-at-or-before-the-column-wins
  ;; ONE LINE, TWO SEGMENTS - which ours never writes and the format allows, so the
  ;; lookup rule is tested against the specification's world rather than this
  ;; compiler's. A segment's four fields are generated column, source index, source
  ;; line, source column - so IACA is "four columns along, one source line down".
  (let [m (sm/decode (str "{\"version\":3,\"file\":\"o.js\",\"sources\":[\"a.cljs\"]"
                          ",\"sourcesContent\":[null],\"names\":[]"
                          ",\"mappings\":\"AAAA,IACA\"}"))]
    (is (= [1 1 1 1 2 2]
           (mapv #(:line (sm/position m 1 %)) [1 2 3 4 5 6]))))
  ;; and a column BEFORE the first segment of its line maps nowhere: the format has
  ;; no way to say what was there
  (let [m (sm/decode (str "{\"version\":3,\"file\":\"o.js\",\"sources\":[\"a.cljs\"]"
                          ",\"sourcesContent\":[null],\"names\":[]"
                          ",\"mappings\":\"IAAA\"}"))]
    (is (nil? (sm/position m 1 3)))
    (is (= 1 (:line (sm/position m 1 5))))
    (testing "and asking without a column takes the line's first segment"
      (is (= 1 (:line (sm/position m 1)))))))

(deftest test-decode-and-the-harness-agree
  ;; TWO IMPLEMENTATIONS, and the point of the harness keeping its own: this is the
  ;; only assertion in the file that compares one decoder against another rather
  ;; than against a constant.
  (let [ps   [nil p1 p2 nil p3 {:file "b.cljs" :line 4 :column 2}]
        json (sm/encode {:file "o.js" :positions ps :content {"a.cljs" "(+ 1 2)\n"}})
        m    (sm/decode json)]
    (is (= (h/map-sources json) (:sources m)))
    (is (= (h/map-positions json)
           (mapv (fn [i] (when-let [p (sm/position m i)]
                           [(:file p) (:line p) (:column p)]))
                 (range 1 (inc (count ps))))))))

(deftest test-a-source-travelling-inside-the-map-comes-back-out
  (let [src  "(ns a)\n\"] and } and \\\" inside a string\"\n"
        json (sm/encode {:file "o.js" :positions [p1] :content {"a.cljs" src}})
        m    (sm/decode json)]
    ;; the brackets matter: a decoder that found the end of sourcesContent by
    ;; scanning for the next ] would stop inside the ClojureScript
    (is (= src (sm/source-text m "a.cljs")))
    (is (nil? (sm/source-text m "nothing.cljs")))
    (testing "and a source the map only names has no text"
      (is (nil? (sm/source-text (sm/decode (sm/encode {:file "o.js" :positions [p1]}))
                                "a.cljs"))))))

(deftest test-json-reads-back-what-json-string-writes
  ;; the escapes are JSON's and not EDN's - backspace and formfeed are not escapes
  ;; the reader knows - so the two halves have to be each other's inverse and not
  ;; nearly so
  (doseq [s ["plain" "a\"b" "a\\b" "a\nb" "a\tb" "ab" "ab"
             "] } , : [ {" "é☃"]]
    (let [json (sm/encode {:file "o.js"
                           :positions [{:file "a.cljs" :line 1 :column 1}]
                           :content {"a.cljs" s}})]
      (is (= s (sm/source-text (sm/decode json) "a.cljs")) (pr-str s)))))
