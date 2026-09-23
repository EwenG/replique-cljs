;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Naming: the two spellings, and the property the compiler rests on.

  clojure.cljs.names has no allocator and no bookkeeping - names cannot collide
  because munge is injective and the three kinds we own have disjoint shapes. Both
  of those are claims about all names, not about the handful anyone thought to try,
  so both are tested by exhaustion over the characters that make them hard.

  Needs neither node nor the ClojureScript jar."}
  clojure.cljs.names-test
  (:require [clojure.cljs.names :as names]
            [clojure.cljs.test-harness :as h]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]]))

(use-fixtures :each h/cursor)

;; --- the two spellings ------------------------------------------------------

(deftest test-host-names-keep-the-clojurescript-spelling
  ;; a property or method belongs to the host, so the host's spelling wins
  (are [sym expected] (= expected (names/host-name sym))
    'innerHTML  "innerHTML"
    'foo-bar    "foo_bar"
    'foo?       "foo_QMARK_"
    ;; a reserved word is a fine property name: o.delete is legal, o.delete$ is a
    ;; different property that does not exist
    'delete     "delete"
    'new        "new"
    ;; $ and _ pass through untouched - cljs$lang$maxFixedArity has to survive
    'cljs$lang$maxFixedArity "cljs$lang$maxFixedArity"
    'foo_bar    "foo_bar")
  ;; and it is deliberately lossy: both spellings name the same host property
  (is (= (names/host-name 'foo-bar) (names/host-name 'foo_bar))))

(deftest test-our-names-are-escaped
  (are [sym expected] (= expected (names/munge sym))
    'foo        "foo"
    'foo-bar    "foo_bar"
    ;; the escape is itself escaped, which is what makes this injective
    'foo_bar    "foo$US$bar"
    'foo?       "foo$QMARK$"
    ;; both characters map: - to _ and > to $GT$
    '->x        "_$GT$x"
    ;; $ is ours, so it cannot survive in a name we own
    'a$b        "a$DL$b"))

(deftest test-munge-is-injective
  ;; The property the whole design rests on, by exhaustion over the characters
  ;; that make munging hard: the escape, the separator, a mapped character, and a
  ;; plain one. Any collision here is a var silently clobbering another var.
  (let [alphabet [\a \_ \- \> \$ \:]
        names    (loop [ns (map str alphabet), all []]
                   (if (> (count (first ns)) 4)
                     all
                     (recur (for [n ns, c alphabet] (str n c)) (into all ns))))
        munged   (map names/munge names)]
    (is (< 1500 (count names)) "the alphabet should generate a real spread")
    (is (= (count munged) (count (distinct munged)))
        (str "collisions: "
             (pr-str (->> (map vector names munged)
                          (group-by second)
                          (filter #(< 1 (count (val %))))
                          (take 5)))))
    ;; host-name, by contrast, is lossy on purpose - stated so it cannot be
    ;; mistaken for an oversight
    (is (not= (count names) (count (distinct (map names/host-name names)))))))

;; --- the shapes -------------------------------------------------------------

(deftest test-the-four-kinds-have-disjoint-shapes
  (names/with-name-scope
    (let [locals (map names/local-name '[x x foo-bar t t$1 ns])
          temps  (repeatedly 6 names/temp-name)
          aliases (map names/ns-alias '[app.core my-app.core t.1 t core a.b-c])
          ;; the fourth: the name on (def f (fn* ...))'s emitted function. `ns` is
          ;; the case that matters - a bare $ns would be the runtime helper, and
          ;; app$core$ns (ClojureScript's fully-qualified shape) would be the
          ;; alias of the namespace it lives in
          selfs  (map names/fn-self-name '[f ns core t x foo-bar])
          ;; the fifth: var-fn-name, the QUALIFIED shape a def normally gets.
          ;; It is not $fn-suffixed - it cannot be, because cljs.spec.alpha reads
          ;; it back by splitting on $ - so it earns its disjointness the way the
          ;; others do, by what munge can and cannot spell (§5.34)
          quals  (keep #(names/var-fn-name 'app.core %) '[f core t x foo-bar ns fn])]
      ;; a local always ends in __<digits>
      (is (every? #(re-matches #".*__\d+" %) locals) (pr-str locals))
      ;; a temporary never contains __, so it can be no local however spelled
      (is (every? #(and (str/starts-with? % "t$") (not (str/includes? % "__"))) temps)
          (pr-str temps))
      ;; an alias always ends in $ns, so it can be none of those
      (is (every? #(str/ends-with? % "$ns") aliases) (pr-str aliases))
      ;; and a self-name always ends in $fn
      (is (every? #(str/ends-with? % "$fn") selfs) (pr-str selfs))
      ;; a qualified name is its namespace path and then a name: never $ns (that
      ;; is the alias, and var-fn-name answers nil rather than spell it), never
      ;; __<digits> (munge escapes $, so no local base is a path), and its last
      ;; piece is a name rather than digits (so it is no temporary)
      (is (= 5 (count quals)) (pr-str quals))
      (is (every? #(and (str/starts-with? % "app$core$")
                        (not (str/ends-with? % "$ns"))
                        (not (re-matches #".*__\d+" %))
                        (not (re-matches #"t\$\d+" %)))
                  quals)
          (pr-str quals))
      ;; nor can any of them be a runtime helper
      (let [runtime #{"$ns" "$CLJS" "truth_"}
            all     (concat locals temps aliases selfs quals)]
        (is (empty? (filter runtime all)) (pr-str (filter runtime all)))
        (is (= (count all) (count (distinct all))) (pr-str all))))))

(deftest test-shapes-stay-disjoint-in-bulk
  ;; by sweep rather than by example: every kind, over names chosen to make the
  ;; shapes hard to tell apart
  (names/with-name-scope
    (let [bases   '[f ns core t x t$1 fn foo-bar foo_bar a$b]
          locals  (mapcat (fn [_] (map names/local-name bases)) (range 20))
          temps   (repeatedly 200 names/temp-name)
          selfs   (map names/fn-self-name bases)
          aliases (map names/ns-alias '[t.1 t f ns core app.core a.b.c my-app.core
                                        fn t.1.ns])
          quals   (for [n '[app.core t my-app.core a.b.c core]
                        b bases
                        :let [js (names/var-fn-name n b)]
                        :when js]
                    js)
          modules (map names/js-alias ["t" "ns" "fn" "core" "app.core" "t.1"
                                       "a-b" "a_b" "@x/y" "x/y"])
          all     (concat locals temps selfs aliases (distinct quals) modules
                          ["$ns" "$CLJS" "truth_"])]
      (is (< 400 (count all)))
      (is (= (count all) (count (distinct all)))
          (str "collisions: "
               (pr-str (->> (frequencies all) (filter #(< 1 (val %))) (take 5))))))))

(deftest test-aliases-are-pure
  ;; no scope, no allocation, no memo - just the name
  (are [ns-sym expected] (= expected (names/ns-alias ns-sym))
    'app.core     "app$core$ns"
    'my-app.core  "my_app$core$ns"
    'a.b.c.d      "a$b$c$d$ns"
    'core         "core$ns"
    ;; a namespace named for a reserved word is never bare, so never a problem
    'new          "new$ns"
    ;; a numeric segment: t.1 would be t$1, exactly a temporary, without the suffix
    't.1          "t$1$ns")
  (is (= (names/ns-alias 'app.core) (names/ns-alias "app.core"))))

(deftest test-aliases-are-injective-under-the-precondition
  ;; joining munged segments with $ is only unambiguous because no segment can
  ;; contain one. Exhaustively: every namespace of up to three legal segments.
  (let [segs ["a" "a-b" "ab" "b"]
        nss  (concat segs
                     (for [x segs y segs] (str x "." y))
                     (for [x segs y segs z segs] (str x "." y "." z)))
        as   (map names/ns-alias nss)]
    (is (< 60 (count nss)))
    (is (= (count as) (count (distinct as)))
        (str "collisions: "
             (pr-str (->> (map vector nss as)
                          (group-by second)
                          (filter #(< 1 (count (val %))))
                          (take 5)))))))

(deftest test-a-namespace-with-nothing-in-a-segment
  ;; str/split drops trailing empty segments, so a.b. and a.b both gave a$b$ns -
  ;; the collision the precondition promises cannot happen. Not excluded by the
  ;; filesystem either: ns->relpath sends them to a/b.cljs and a/b/.cljs.
  (are [ns-sym] (thrown? Exception (names/ns-alias ns-sym))
    (symbol "a.b.")
    (symbol "a.b..")
    (symbol "a..b")
    (symbol "")        ; would have been "$ns", the runtime helper itself
    (symbol "."))
  ;; and an alias that would not be a JavaScript name at all
  (is (thrown? Exception (names/ns-alias (symbol "1a.core"))))
  ;; while a numeric segment after the first is fine: t$1$ns is a legal name
  (is (= "t$1$ns" (names/ns-alias 't.1))))

(deftest test-a-module-alias-is-what-the-import-binds
  ;; the fifth shape: a string require names a module, and the module is bound to
  ;; this name once - whatever the ns form went on to ask of it
  (are [specifier expected] (= expected (names/js-alias specifier))
    "react"                 "react$js"
    ;; a hyphen is the common case and stays legible, exactly as in a namespace
    "react-dom"             "react_dom$js"
    ;; a sub-path is not a path here: / is a character like any other, and it is
    ;; escaped like any other
    "react-dom/client"      "react_dom$SLASH$client$js"
    "@visx/scale"           "$CIRCA$visx$SLASH$scale$js"
    ;; a DOT, which is the one character munge lets through, because a namespace
    ;; name is spelled with them and a variable cannot hold one. sse.js is a real
    ;; package and date-fns/locale/en-GB is a real file
    "sse.js"                "sse$DOT$js$js"
    "date-fns/locale/en-GB" "date_fns$SLASH$locale$SLASH$en_GB$js"
    ;; npm allows a leading digit and JavaScript does not: one $ in front, which
    ;; nothing else can produce because every code is a $ and then a CAPITAL
    "3d-view"               "$3d_view$js"))

(deftest test-module-aliases-are-injective
  ;; by sweep, over the characters a specifier actually holds - the property the
  ;; $-delimited codes exist for, restated one escape wider than munge's
  (let [pieces ["a" "a-b" "a_b" "a.b" "@a" "a$b" "3a" "a/b"]
        specs  (concat pieces
                       (for [x pieces y pieces] (str x y))
                       (for [x pieces y pieces] (str x "/" y)))
        as     (map names/js-alias specs)]
    (is (< 120 (count specs)))
    (is (= (count as) (count (distinct as)))
        (str "collisions: "
             (pr-str (->> (map vector specs as)
                          (group-by second)
                          (filter #(< 1 (count (val %))))
                          (take 5)))))
    ;; and never one of the other shapes: always ends in $js, never in $ns or $fn,
    ;; never __<digits>
    (is (every? #(and (str/ends-with? % "$js")
                      (not (str/ends-with? % "$ns"))
                      (not (str/ends-with? % "$fn"))
                      (not (re-matches #".*__\d+" %)))
                as))))

(deftest test-a-specifier-that-cannot-be-a-name
  ;; nothing names nothing - and "$js" on its own would have been a legal
  ;; identifier, which is what makes this a check rather than a formality
  (are [specifier] (thrown? Exception (names/js-alias specifier))
    ""
    "   "
    nil
    'react           ; a symbol is a namespace; a module is written as a string
    "a b"
    "a(b)")
  ;; a module alias and a namespace alias can never collide, whatever they are
  ;; named for: one ends in $js and the other in $ns
  (is (not= (names/js-alias "app") (names/ns-alias 'app))))

(deftest test-a-name-we-own-must-be-spellable
  ;; every character a symbol may hold is munged except the dot, which separates
  ;; names rather than belonging to one
  (are [sym] (thrown? Exception (names/check-own-name! sym "a var name"))
    'a.b
    'a.b.c
    (symbol "1a")
    (symbol "has space"))
  (are [sym expected] (= expected (names/check-own-name! sym "a var name"))
    'foo      "foo"
    'foo-bar  "foo_bar"
    'foo?     "foo$QMARK$"
    'if       "if"))

(deftest test-no-name-scope-says-so
  ;; the NPE this replaces named an atom, not the discipline it belongs to
  (is (re-find #"No name scope"
               (try (names/temp-name) "" (catch Exception e (.getMessage e)))))
  (is (re-find #"No name scope"
               (try (names/local-name 'x) "" (catch Exception e (.getMessage e))))))

(deftest test-a-namespace-segment-that-would-not-survive-the-join
  ;; the precondition, and the message that explains it
  (are [ns-sym] (thrown? Exception (names/ns-alias ns-sym))
    'my_lib.core        ; _ munges to $US$
    'a.b_c
    'foo.core$macros    ; self-hosted ClojureScript's macro namespaces
    'a.b?)
  (is (re-find #"not my_lib.core"
               (try (names/ns-alias 'my_lib.core) (catch Exception e (.getMessage e)))))
  ;; and what it costs: nothing that could have a source file, because
  ;; cljs.util/ns->relpath sends my-lib.core and my_lib.core to the same path
  (is (= "my_app$core$ns" (names/ns-alias 'my-app.core))))

(deftest test-locals-are-unique-within-a-scope
  (names/with-name-scope
    (let [a (names/local-name 'x)
          b (names/local-name 'x)
          c (names/local-name 'x-y)]
      (is (= ["x__1" "x__2" "x_y__3"] [a b c])))))

(deftest test-a-scope-starts-over
  ;; so the same file always compiles to the same names
  (is (= (names/with-name-scope [(names/local-name 'x) (names/temp-name)])
         (names/with-name-scope [(names/local-name 'x) (names/temp-name)]))))

;; --- the protocol shape -----------------------------------------------------

(deftest test-protocol-names-are-pure
  (are [proto expected] (= expected (names/protocol-name proto))
    'app.core/IShape      "app$core$$IShape"
    'my-app.core/IShape   "my_app$core$$IShape"
    'core/I               "core$$I")
  (are [proto m n expected] (= expected (names/protocol-method-name proto m n))
    'app.core/IShape '-area  1 "app$core$$IShape$_area$arity$1"
    'app.core/IShape '-scale 3 "app$core$$IShape$_scale$arity$3"
    ;; a method may hold anything munge can spell - it is the last piece
    'app.core/IShape '-a>b   1 "app$core$$IShape$_a$GT$b$arity$1"
    'app.core/IShape 'p!     2 "app$core$$IShape$p$BANG$$arity$2"))

(deftest test-a-protocol-name-that-would-not-survive-the-join
  ;; the same precondition a namespace segment carries, and for the same reason:
  ;; the $ that ends the protocol part has to be findable
  (are [proto] (str/includes? (h/message #(names/protocol-name proto)) "would not survive")
    'app.core/I_Shape
    'app.core/I$Shape
    'app.core/I>Shape)
  (is (str/includes? (h/message #(names/protocol-name 'IShape)) "needs a namespace")))

(deftest test-protocol-names-are-injective
  ;; A property name is computed independently by the site that installs an
  ;; implementation and by every site that calls one, so a collision is one
  ;; protocol's method answering for another's - silently. By exhaustion over the
  ;; pieces that make the joins hard rather than by example.
  (let [nss     '[a a.b a.b.C a.b.C.x a.ns b.a]
        ;; GT is a legal protocol name and a code name, which is the only way an
        ;; alternative parse can balance - see the next test
        protos  '[C IShape x-y I GT]
        methods '[m -area x-y >z ns_x -a>b x>z z]
        arities [1 2]
        names   (for [n nss, p protos, m methods, a arities]
                  [[n p m a] (names/protocol-method-name (symbol (str n) (str p)) m a)])
        markers (for [n nss, p protos]
                  [[n p] (names/protocol-name (symbol (str n) (str p)))])
        all     (concat names markers)]
    (is (< 100 (count all)))
    (is (= (count all) (count (distinct (map second all))))
        (str "collisions: "
             (pr-str (->> (group-by second all)
                          (filter #(< 1 (count (val %))))
                          (take 5)))))))

(deftest test-the-doubled-dollar-is-what-makes-the-namespace-boundary-findable
  ;; The forgery a single $ would allow, spelled out - this is the pair the sweep
  ;; above is built around, and it took a wrong first guess to find. The method is
  ;; the one piece that may contain a $, so it can lend one to a boundary; but
  ;; munge emits $ only in pairs, so the invented protocol has to be a CODE name
  ;; for the counts to balance. GT is both a code name and a name someone could
  ;; write.
  (let [one (names/protocol-method-name 'a.b/C 'x>z 1)
        two (names/protocol-method-name 'a.b.C.x/GT 'z 1)]
    (is (not= one two))
    (is (= "a$b$$C$x$GT$z$arity$1" one))
    (is (= "a$b$C$x$$GT$z$arity$1" two))
    ;; and with a single $ they are one name - which is what this is defending
    ;; against, said in the test rather than only in a docstring
    (is (= (str/replace one "$$" "$") (str/replace two "$$" "$")))))

(deftest test-a-marker-is-never-a-method
  ;; both land on the same object, so they have to differ whatever the names are
  (let [markers (for [n '[a a.b], p '[C IShape]]
                  (names/protocol-name (symbol (str n) (str p))))
        methods (for [n '[a a.b], p '[C IShape], m '[m arity C], a [1 2]]
                  (names/protocol-method-name (symbol (str n) (str p)) m a))]
    (is (empty? (filter (set markers) methods)))))

(deftest test-a-field-is-spelled-the-hosts-way
  ;; a field is read from outside as (.-x p), so it is the host's spelling that has
  ;; to be met - which is also why two fields can collide, and why the analyzer
  ;; refuses that pair rather than the naming scheme ruling it out
  (are [sym expected] (= expected (names/field-name sym))
    'x        "x"
    'foo-bar  "foo_bar"
    'foo_bar  "foo_bar"
    '__meta   "__meta")
  (is (= (names/field-name 'foo-bar) (names/field-name 'foo_bar)))
  (is (str/includes? (h/message #(names/field-name 'a.b)) "A dot separates names")))

;; --- the protocol shape, fuzzed ---------------------------------------------

(deftest test-protocol-names-are-injective-under-fuzzing
  ;; The sweep above is chosen by hand; this one is exhaustive over the shape a
  ;; forgery must HAVE, which is the lesson of having written a wrong one first.
  ;; Namespace segments an alternative parse could absorb, protocols that are also
  ;; code names, and methods over an alphabet that makes munge emit $.
  ;;
  ;; A quarter of a million names in about a second, and it reports 400 collisions
  ;; the moment the doubled $ becomes a single one - which is how it was checked.
  (let [segs   '[a C x GT arity]
        protos '[C x GT US arity P]
        alpha  [\a \- \> \_ \G]
        meths  (map symbol (distinct (concat (map str alpha)
                                             (for [a alpha b alpha] (str a b))
                                             (for [a alpha b alpha c alpha] (str a b c)))))
        nss    (distinct (concat (map str segs)
                                 (for [a segs b segs] (str a "." b))
                                 (for [a segs b segs c segs] (str a "." b "." c))))
        seen   (java.util.HashMap.)
        bad    (atom [])
        put!   (fn [nm k]
                 (let [prev (.get seen nm)]
                   (when (and prev (not= prev k)) (swap! bad conj [nm prev k]))
                   (.put seen nm k)))
        spell  (fn [f] (try (f) (catch Exception _ nil)))]
    (doseq [n nss, p protos
            :let [q (symbol n (str p))]
            :when (spell #(names/protocol-name q))]
      (put! (names/protocol-name q) [:marker n p])
      (doseq [m meths, a [1 2]
              :let [nm (spell #(names/protocol-method-name q m a))]
              :when nm]
        (put! nm [n p m a])))
    (is (< 250000 (.size seen)) (str "only " (.size seen) " names generated"))
    (is (empty? @bad) (pr-str (take 5 @bad)))))

;; --- end to end -------------------------------------------------------------

(h/deftest-when h/node? test-the-two-implementations-of-munge-agree
  ;; runtime.js states code-map a second time, because a var looked up by a name
  ;; that is a STRING at run time - lazy loading, where the module holding it has
  ;; not been fetched yet - has nothing to ask the JVM. Two statements of one rule
  ;; drift unless something runs them against each other, as output_test does for
  ;; urlFor, and a wrong answer here is a property that does not exist rather than
  ;; an error anything reports.
  ;;
  ;; THE SAME ALPHABET test-munge-is-injective uses, and for the same reason: the
  ;; characters that make munging hard are the escape, the separator, a mapped
  ;; character and a plain one. A handful of hand-picked names would agree by
  ;; accident over any map that got the common case right.
  (let [alphabet [\a \_ \- \> \$ \:]
        names    (loop [ns (map str alphabet), all []]
                   (if (> (count (first ns)) 3)
                     all
                     (recur (for [n ns, c alphabet] (str n c)) (into all ns))))
        js       (str "console.log(JSON.stringify(["
                      (str/join ", " (map #(str "\"" % "\"") names))
                      "].map((n) => $CLJS.munge(n))));")]
    (is (< 250 (count names)) "the alphabet should generate a real spread")
    (is (= (mapv names/munge names) (read-string (h/run-js js))))))

(h/deftest-when h/node? test-every-character-code-map-maps-agrees
  ;; the alphabet above is four characters wide and code-map is twenty-six, so
  ;; this is the other half: every entry, once, including the ones no ordinary
  ;; name contains. A transcription that dropped or misspelled one would pass the
  ;; test above and lose a var here.
  (let [chars (sort (keys names/code-map))
        names (map #(str "a" % "b") chars)
        js    (str "console.log(JSON.stringify(["
                   (str/join ", " (map #(str "\"" (str/escape % {\\ "\\\\" \" "\\\""}) "\"") names))
                   "].map((n) => $CLJS.munge(n))));")]
    (is (= 26 (count chars)) (pr-str chars))
    (is (= (mapv names/munge names) (read-string (h/run-js js))))))

(h/deftest-when h/node? test-two-vars-that-used-to-share-one-property
  ;; foo-bar and foo_bar are two vars. Under cljs.compiler's lossy map they were
  ;; one JavaScript property, and the second def silently clobbered the first.
  (let [src "(def foo-bar 1) (def foo_bar 2) (js* \"~{} + ' ' + ~{}\" foo-bar foo_bar)"]
    (is (= "1 2" (h/output src)))
    (is (str/includes? (h/js src) "foo$US$bar") (h/js src))))

(h/deftest-when h/node? test-a-module-whose-namespace-looks-like-a-temporary
  ;; t.1 would alias to t$1 without the suffix, which is exactly a temporary
  (let [src (str "(def x (let* [q 1] (if q 1 2)))\n"
                 "(def y (if x (let* [z 3] z) 4))\n"
                 "y")
        js  (h/js (h/fresh-env 't.1) src)]
    (is (str/includes? js "const t$1$ns = $ns(\"t.1\");") js)
    (let [declared (map second (re-seq #"(?m)^\s*(?:const|let) ([A-Za-z0-9_$]+)" js))]
      (is (= (count declared) (count (distinct declared))) js))
    (is (= "3" (h/output (h/fresh-env 't.1) src)))))

(h/deftest-when h/node? test-host-interop-still-reaches-host-properties
  ;; the split earns its keep here: a snake_case property must not be escaped
  (is (= "1" (h/output "(.-foo_bar (js* \"({foo_bar: 1})\"))")))
  ;; and kebab-case still reaches it, as it does in ClojureScript
  (is (= "1" (h/output "(.-foo-bar (js* \"({foo_bar: 1})\"))")))
  (is (= "0" (h/output "(let* [m (new js/Map)] (do (.set m \"k\" 1) (.delete m \"k\") (.-size m)))"))))

(deftest test-an-auto-gensym-keeps-only-its-legible-part
  ;; v# reads as v__11__auto__, and munge sends _ to $US$ - so without this the
  ;; local reached the output as v$US$$US$11$US$$US$auto$US$$US$__1. cljs.core is
  ;; macros nearly all the way down, so this is most of what M5 will emit.
  (names/with-name-scope
    (is (= "v__1" (names/local-name 'v__11__auto__)))
    (is (= "x_y__2" (names/local-name 'x-y__3__auto__)))
    ;; only the reader's own shape, and only as a whole suffix
    (is (= "v$US$$US$auto$US$$US$__3" (names/local-name 'v__auto__)))
    (is (= "tmp750__4" (names/local-name 'tmp750)))
    (is (= "v$US$$US$11$US$$US$auto$US$$US$x__5" (names/local-name 'v__11__auto__x))))
  ;; and it is safe because uniqueness was never the base's job: two bindings that
  ;; strip to the same base still differ, which is all the emitter needs
  (names/with-name-scope
    (is (= ["v__1" "v__2" "v__3"]
           [(names/local-name 'v__11__auto__)
            (names/local-name 'v__12__auto__)
            (names/local-name 'v)]))))

(deftest test-a-qualified-fn-name-is-what-demunge-inverts
  ;; §5.34. cljs.spec.alpha recovers a bare predicate's qualified symbol from the
  ;; emitted function's .name (alpha.cljs:123): split on $, demunge each piece,
  ;; join all but the last with dots. So this name is host-name's spelling - the
  ;; map demunge inverts - and $ stays a separator rather than an escape.
  (are [ns-sym sym expected] (= expected (names/var-fn-name ns-sym sym))
    'app.core    'f          "app$core$f"
    'cljs.core   'keyword?   "cljs$core$keyword_QMARK_"
    'cljs.core   '=          "cljs$core$_EQ_"
    'my-app.core 'foo-bar    "my_app$core$foo_bar"
    'core        'f          "core$f"
    ;; the two that read as another shape, which fn-self-name takes instead
    'app.core    'ns         nil
    'app.core    'fn         nil)

  (testing "and it round-trips through cljs.core/demunge's rule"
    ;; the rule spelled out here rather than run, because demunge is
    ;; ClojureScript's and lives in the runtime - what is checked is that the
    ;; pieces are what fn-sym needs: at least two, none of them blank
    (doseq [sym '[f keyword? = foo-bar + <= *print-fn*]]
      (let [pieces (str/split (names/var-fn-name 'cljs.core sym) #"\$")]
        (is (<= 2 (count pieces)) (pr-str sym pieces))
        (is (every? seq pieces) (pr-str sym pieces))))))
