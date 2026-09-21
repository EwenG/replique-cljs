;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "M4's oracle: the protocol calling convention, end to end.

  defprotocol / deftype / extend-type / satisfies? are cljs/core.cljc's macros;
  what the compiler contributes is deftype*, defrecord* and the property names. So
  these programs go the whole way - macroexpansion, analysis, emission, node - and
  check the value, which is the only thing that can tell a convention that works
  from one that merely compiles.

  THEY USED TO BE OURS. clojure/cljs/protocols.clj held a second, smaller
  implementation of the same four macros, written at M4 because vendoring
  core.cljc was M5 and a convention needs an oracle before it has a library. It is
  gone: §5.12's implicit require was the last thing standing between a deftype
  outside cljs.core and the real macros, and one implementation with the tests
  pointed at it beats two. Retiring it found two defects that the second
  implementation had been hiding - see doc/cljs-compiler.md §5.13.

  js* still supplies some of the arithmetic. It is left where it was rather than
  rewritten to (* x y) now that it could be: what these tests are about is the
  property a call reaches, and an expression with fewer moving parts says so more
  plainly.

  Skipped when node is not on PATH."}
  clojure.cljs.protocols-test
  (:require [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.names :as names]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]])
  (:import [java.io File]))

(use-fixtures :each h/cursor)

;; A COMPILED cljs.core behind every one of these, because the macros are now its
;; own: defprotocol expands into code that names cljs.core/Symbol and
;; cljs.core/-write, and deftype's ctorPrWriter names -write too. h/core-env hands
;; out a fresh NAMESPACE inside one shared environment, so tests still cannot see
;; each other's defs and core.cljs is still compiled once per JVM.
(defn- src [& forms] (str/join "\n" forms))
(defn- out [& forms] (h/output-with-core (h/core-env) (apply src forms)))
(defn- js  [& forms] (h/js (h/core-env) (apply src forms)))

(defn- js-in
  "js, in a NAMED namespace. A test that asserts on a property name has to know
  which namespace computed it, and the namespace h/core-env hands out is a
  counter. Named app.core because that is the name the assertions read best with,
  and two tests sharing it is harmless: each redefines what it needs."
  [& forms]
  (h/js (h/core-env 'app.core) (apply src forms)))

(def ^:private shape
  "(defprotocol IShape (-area [this]) (-scale [this k] [this kx ky]))")

(def ^:private point
  "(deftype Point [x y]
     IShape
     (-area [this] (js* \"~{} * ~{}\" x y))
     (-scale [this k] (new Point (js* \"~{} * ~{}\" x k) (js* \"~{} * ~{}\" y k)))
     (-scale [this kx ky] (new Point (js* \"~{} * ~{}\" x kx) (js* \"~{} * ~{}\" y ky))))")

;; --- the convention ---------------------------------------------------------

(h/deftest-when h/node? test-a-protocol-call-reaches-a-deftype
  (is (= "12" (out shape point "(-area (new Point 3 4))")))
  ;; each arity is a property of its own, so one method can have several
  (is (= "48" (out shape point "(-area (-scale (new Point 3 4) 2))")))
  (is (= "72" (out shape point "(-area (-scale (new Point 3 4) 2 3))"))))

(h/deftest-when h/node? test-the-property-name-is-computed-not-looked-up
  ;; The whole bargain, visible in the text: the call site spells the same name the
  ;; deftype installed, and nothing between them consults anything.
  (let [text (js-in shape point "(-area (new Point 1 2))")
        prop (names/protocol-method-name 'app.core/IShape '-area 1)]
    (is (= "app$core$$IShape$_area$arity$1" prop))
    (is (str/includes? text (str "Point.prototype." prop " =")) text)
    (is (str/includes? text (str "this__1." prop "(this__1)")) text)
    ;; and the fast path is first: what follows the ? is the property call, and
    ;; nothing is consulted to get there
    (is (str/includes? text (str "!= null) ? this__1." prop "(")) text)
    ;; the doubled $ is clojure.cljs.names', not cljs.compiler's single one, which
    ;; is the difference between injective and merely unique (§5.3) - and there is
    ;; no bitmask beside it, which §5.4 refused deliberately
    (is (not (str/includes? text "cljs$lang$protocol_mask")) text)))

(h/deftest-when h/node? test-a-field-is-in-scope-by-its-bare-name
  ;; and it is a property read of the object, not a copy: the emitted method has
  ;; no binding for the field at all
  (let [text (js-in shape point "(-area (new Point 1 2))")]
    (is (re-find #"return self__\d+\.x \* self__\d+\.y;" text) text))
  ;; an inner binding of the same name shadows the field, which is what going
  ;; through :locals buys over rewriting the body
  (is (= "7" (out "(deftype T [x] Object (get [this] (let* [x 7] x)))"
                  "(.get (new T 1))")))
  ;; and a nested fn closes over the object, because the object is an ordinary
  ;; local - the case JavaScript's `this` would get wrong
  (is (= "42" (out "(deftype T [v] Object (get [this] ((fn* [] v))))"
                   "(.get (new T 42))"))))

(h/deftest-when h/node? test-a-mutable-field-can-be-set
  (is (= "2" (out "(deftype Counter [^:mutable n]
                     Object
                     (bump [this] (set! n (js* \"~{} + 1\" n))))
                   (def c (new Counter 0))
                   (do (.bump c) (.bump c) (.-n c))")))
  ;; set! reaches the object, not a copy, so two methods see one another's writes
  (is (= "5" (out "(deftype Box [^:mutable v]
                     Object
                     (put [this x] (set! v x))
                     (get [this] v))
                   (def b (new Box 0))
                   (do (.put b 5) (.get b))"))))

(h/deftest-when h/node? test-an-object-method-is-called-by-the-host
  ;; toString has no explicit receiver: JavaScript calls it, so the object comes
  ;; from `this` - and the fields still read the same way
  (is (= "Point(3,4)"
         (out "(deftype Point [x y]
                 Object
                 (toString [this] (js* \"'Point(' + ~{} + ',' + ~{} + ')'\" x y)))
               (js* \"String(~{})\" (new Point 3 4))"))))

;; --- values with no prototype of ours ---------------------------------------

(h/deftest-when h/node? test-a-protocol-can-take-a-name-cljs-core-already-uses
  ;; A def shadowing a refer is ordinary Clojure, and cljs.core is referred into
  ;; every namespace - so `(defprotocol ICloneable ...)` of your own is a thing
  ;; people write. It compiled and then threw `No implementation of method` at run
  ;; time, because defprotocol asked what the name resolved to BEFORE interning it:
  ;; the dispatch was built around cljs$core$$ICloneable$, and the deftype below,
  ;; resolving the same name a form later, put its implementation under
  ;; app$tN$$ICloneable$. ClojureScript has the same line and the same defect
  ;; (their core.cljc:2084); the fix is not to ask - a defprotocol defines into the
  ;; namespace it is in and can mean nothing else.
  (is (= "cloned-1"
         (out "(defprotocol ICloneable (-clone [this]))"
              "(deftype T [x] ICloneable (-clone [this] (str \"cloned-\" x)))"
              "(-clone (new T 1))")))
  ;; and the shadowed one still works where it is not shadowed - two protocols of
  ;; one name, in two namespaces, each reaching its own
  (is (= "own other"
         (out "(defprotocol IDup (-gd [this]))"
              "(deftype A [] IDup (-gd [this] \"own\"))"
              "(str (-gd (new A)) \" other\")"))))

(h/deftest-when h/node? test-a-protocol-extends-to-native-types
  (is (= "5 3 0 -1 4 1"
         (out shape
              "(extend-type string  IShape (-area [this] (.-length this)))"
              "(extend-type number  IShape (-area [this] this))"
              "(extend-type nil     IShape (-area [this] 0))"
              "(extend-type default IShape (-area [this] -1))"
              "(extend-type array   IShape (-area [this] (.-length this)))"
              "(extend-type boolean IShape (-area [this] 1))"
              "(js* \"[~{},~{},~{},~{},~{},~{}].join(' ')\"
                 (-area \"hello\") (-area 3) (-area nil) (-area (js* \"({})\"))
                 (-area (js* \"[1,2,3,4]\")) (-area true))"))))

(h/deftest-when h/node? test-a-missing-implementation-says-what-was-missing
  (is (= "THREW: No implementation of method -area found for number: 3"
         (out shape "(-area 3)")))
  (is (= "THREW: No implementation of method -area found for null: nil"
         (out shape "(-area nil)"))))

(h/deftest-when h/node? test-extend-type-writes-on-a-host-prototype
  ;; not a base type, so it has a prototype and the ordinary path applies
  (is (= "1970" (out shape
                     "(extend-type js/Date IShape (-area [this] (.getUTCFullYear this)))"
                     "(-area (new js/Date 0))"))))

(h/deftest-when h/node? test-extend-type-outside-a-deftype-has-no-fields
  ;; deliberate, and the same answer ClojureScript gives: an extend-type is an
  ;; ordinary form that could be written anywhere, so there is no object to bind
  ;; a bare field name against
  (is (= "6" (out shape
                  "(deftype Point [x y])"
                  "(extend-type Point IShape (-area [this] (js* \"~{} * ~{}\" (.-x this) (.-y this))))"
                  "(-area (new Point 2 3))")))
  (is (str/includes?
       (h/message #(out shape "(deftype Point [x y])"
                        "(extend-type Point IShape (-area [this] x))"))
       "neither a local nor a var")))

;; --- satisfies? -------------------------------------------------------------

(h/deftest-when h/node? test-satisfies
  (is (= "true true true false"
         (out shape point
              "(extend-type string IShape (-area [this] 1))"
              "(extend-type nil IShape (-area [this] 0))"
              "(js* \"[~{},~{},~{},~{}].join(' ')\"
                 (satisfies? IShape (new Point 1 2)) (satisfies? IShape \"s\")
                 (satisfies? IShape nil) (satisfies? IShape 3))")))
  ;; default extends everything, so it answers for everything
  (is (= "true" (out shape "(extend-type default IShape (-area [this] 0))"
                     "(satisfies? IShape 3)")))
  ;; a protocol with no methods is still something a type can declare
  (is (= "true false" (out "(defprotocol IMarker)"
                           "(deftype T [] IMarker)"
                           "(deftype U [])"
                           "(js* \"[~{},~{}].join(' ')\"
                              (satisfies? IMarker (new T)) (satisfies? IMarker (new U)))")))
  ;; the subject is evaluated once, however many questions are asked of it
  (is (= "1 true" (out shape "(extend-type default IShape (-area [this] 0))"
                       "(def n 0)"
                       "(js* \"[~{},~{}].join(' ')\"
                          (do (satisfies? IShape (set! n (js* \"~{} + 1\" n))) n)
                          (satisfies? IShape 1))"))))

;; --- a protocol named with dots ---------------------------------------------

(deftest test-a-protocol-named-with-dots-spells-the-same-marker
  ;; 5.59. malli.registry writes (implements? malli.registry.Registry x) - a
  ;; SIMPLE symbol with dots, which is how ClojureScript names a protocol without
  ;; an alias or a refer. resolve-var reads one of those as a var of the CURRENT
  ;; namespace carrying a dotted name, so the marker came out as
  ;; app$user$$app.proto.Registry: the wrong namespace, and dots that JavaScript
  ;; then reads as a property chain - "Cannot read properties of undefined
  ;; (reading 'proto')" - where one property was meant.
  ;;
  ;; THE SET SITE WAS ALWAYS RIGHT, which is why nothing caught it. extend-type
  ;; spells the marker off a symbol it has already resolved, so a type carried
  ;; app$proto$$Registry while every test of it asked for something else.
  (let [cenv (h/core-env 'app.proto)]
    (h/analyze cenv '(ns app.proto))
    (h/analyze cenv '(defprotocol Registry (-schema [this])))
    ;; asked from ANOTHER namespace, because the wrong answer used the asking
    ;; namespace's own name and a same-namespace test cannot tell the two apart
    (h/analyze cenv '(ns app.user (:require [app.proto])))
    (let [slash  (h/js cenv "(cljs.core/implements? app.proto/Registry nil)")
          dotted (h/js cenv "(cljs.core/implements? app.proto.Registry nil)")
          sat    (h/js cenv "(cljs.core/satisfies? app.proto.Registry nil)")]
      (is (str/includes? slash "app$proto$$Registry") slash)
      (testing "the dotted spelling is the same protocol"
        (is (str/includes? dotted "app$proto$$Registry") dotted)
        (is (str/includes? sat "app$proto$$Registry") sat))
      (testing "and no dot survives into a property name"
        ;; the failure is not that the marker is wrong but that it is not one
        ;; NAME: x.a$$b.c.D reads three properties, and the first is undefined
        (is (not (str/includes? dotted "app.proto.Registry")) dotted)
        (is (not (str/includes? sat "app.proto.Registry")) sat)
        (is (not (str/includes? dotted "app$user$$")) dotted)))))

(h/deftest-when h/node? test-a-protocol-named-with-dots-answers-at-runtime
  ;; and the answers agree, which is the whole of what malli asked for
  ;; a NAMED namespace, because the source has to spell it out loud
  (is (= "true true true false"
         (h/output-with-core
          (h/core-env 'app.protodots)
          (src "(defprotocol P (-m [this]))"
               "(deftype T [] P (-m [_] 1))"
               "(js* \"[~{},~{},~{},~{}].join(' ')\"
                  (implements? P (new T))
                  (implements? app.protodots.P (new T))
                  (satisfies? app.protodots.P (new T))
                  (implements? app.protodots.P 42))")))))

;; --- across namespaces ------------------------------------------------------

(def ^:private program
  ;; NO :require-macros ANYWHERE, which is the shape of the thing after §5.12: the
  ;; macros come from cljs.core, and cljs.core is required by every namespace
  ;; whether or not its ns form says so. What each file still has to say for
  ;; itself is where IShape comes from, and that is the whole subject below.
  '{shapes.core "(ns shapes.core)
                 (defprotocol IShape (-area [this]))"

    shapes.point "(ns shapes.point
                    (:require [shapes.core :as s :refer [IShape -area]]))
                  (deftype Point [x y]
                    IShape
                    (-area [this] (js* \"~{} * ~{}\" x y)))"

    app.core "(ns app.core
                (:require [shapes.core :refer [-area]]
                          [shapes.point :as p]
                          [shapes.core :as s]))
              (js* \"console.log(~{})\" (-area (new p/Point 6 7)))
              (js* \"console.log(~{})\" (satisfies? s/IShape (new p/Point 1 1)))"})

(h/deftest-when h/node? test-three-namespaces-agree-on-one-property-name
  ;; The claim the convention rests on, and the only test that can make it: the
  ;; protocol is declared in one file, implemented in a second and called from a
  ;; third, and nothing is shared between them but the name each computes.
  ;; An alias and a :refer both reach it, which is why a macro needs the symbol
  ;; table (clojure.cljs.env/resolve-var).
  (let [source (h/write-sources! (h/temp-dir) program)
        target (h/temp-dir)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'app.core
                                 {:out-dir target :source-paths [source]})
      (let [prop   (names/protocol-method-name 'shapes.core/IShape '-area 1)
            marker (names/protocol-name 'shapes.core/IShape)]
        ;; the name is spelled twice, in two files that share nothing but the
        ;; protocol's symbol: once by the dispatch function shapes.core emits, and
        ;; once by the deftype in shapes.point that installs an implementation
        (is (str/includes? (slurp (io/file target "ns/shapes/core.js")) prop))
        (is (str/includes? (slurp (io/file target "ns/shapes/point.js")) prop))
        ;; app.core spells the marker for itself, through an alias this time
        (is (str/includes? (slurp (io/file target "ns/app/core.js")) marker)))
      (let [{:keys [out exit]} (sh/sh "node" (.getPath (io/file target "ns/app/core.js")))]
        (is (zero? exit))
        (is (= "42\ntrue" (str/trim out))))
      (finally (h/delete-tree! source) (h/delete-tree! target)))))

;; --- at the REPL ------------------------------------------------------------

(h/deftest-when h/node? test-an-implementation-can-be-added-to-a-live-type
  ;; §5.2's payoff reaches protocols too: a prototype is an object, so a form
  ;; evaluated later installs a method that instances created earlier already have
  (is (= ["false" "6" "true"]
         (h/session-output
          (h/core-env)
          [(str shape " (deftype Point [x y]) (def p (new Point 2 3))"
                " (satisfies? IShape p)")
           "(do (extend-type Point IShape (-area [this] (js* \"~{} * ~{}\" (.-x this) (.-y this))))
                (-area p))"
           "(satisfies? IShape p)"]))))

;; --- what it refuses --------------------------------------------------------

(deftest test-the-shape-of-a-deftype-is-enforced
  (are [form msg] (str/includes? (h/message #(h/analyze (h/fresh-env) form)) msg)
    '(deftype* 1 [] self nil)          "must be a simple symbol"
    '(deftype* a.b [] self nil)        "not a JavaScript name"
    '(deftype* T x self nil)           "needs a vector of fields"
    '(deftype* T [] 1 nil)             "needs a symbol to name the object"
    '(deftype* T [] self nil nil)      "Too many arguments"
    '(deftype* T [self] self nil)      "A field cannot be named self"
    '(deftype* T [a.b] self nil)       "not a JavaScript name"
    ;; host-name is lossy, so these two fields are one property. The second would
    ;; silently overwrite the first, which is the bug names/munge exists to have
    ;; fixed for vars - here the pair is refused instead.
    '(deftype* T [foo-bar foo_bar] self nil) "are one field"))

(deftest test-a-field-is-immutable-unless-declared
  (let [msg (h/message
             #(h/analyze (h/fresh-env)
                         '(deftype* T [x] self ((fn* [self] (set! x 1))))))]
    (is (str/includes? msg "declared ^:mutable") msg))
  ;; and the declaration is what lifts it
  (is (some? (h/analyze (h/fresh-env)
                        '(deftype* T [^:mutable x] self ((fn* [self] (set! x 1))))))))

(h/deftest-when h/node? test-a-protocol-symbol-that-does-not-resolve-warns
  ;; IT USED TO THROW. clojure.cljs.protocols refused the symbol outright - "No
  ;; such protocol: INoSuch" - and cljs.core's macros warn and carry on, because
  ;; ana/resolve-var answers a name for a var that is not there (its docstring
  ;; says why: defonce and extend-type both need one). That is a real loss of
  ;; strictness, taken deliberately: matching ClojureScript is what vendoring
  ;; core.cljc is for, and a warning that names the protocol and the method is
  ;; still the compiler saying so.
  (is (str/includes?
       (h/warnings #(out "(deftype T [] INoSuch (-m [this] 1)) 1"))
       "protocol-invalid-method {:protocol INoSuch, :fname -m, :no-such-method true}")))

;; --- recur inside a method ---------------------------------------------------

(h/deftest-when h/node? test-recur-in-a-method-does-not-rebind-the-object
  ;; A DEFTYPE METHOD IS A METHOD: the object it was called on is fixed for the
  ;; whole call, so recur rebinds the parameters after it and takes one argument
  ;; fewer than the method has parameters. Clojure's rule, and ClojureScript's -
  ;; reached from a different encoding, which is why it needed doing at all.
  ;; ClojureScript hides the object behind this-as and so can let recur assign a
  ;; dead parameter; here it is a live parameter that fields are read through
  ;; (doc/cljs-compiler.md 5.4), so assigning it would break the next iteration's
  ;; field reads. See 5.16.
  (testing "one argument fewer, and the fields survive the jump"
    (is (= ":b" (out "(defprotocol ISearch (search [this coll]))"
                     "(deftype T [n] ISearch
                        (search [this coll]
                          (when (seq coll)
                            (if (= n (first coll)) n (recur (rest coll))))))"
                     "(pr-str (search (T. :b) [:a :b :c]))")))
    ;; the object is read AFTER several iterations, which is the assertion the
    ;; whole design turns on
    (is (= "[1 2]" (out "(defprotocol ISearch (search [this coll]))"
                        "(deftype W [a b] ISearch
                           (search [this coll] (if (seq coll) (recur (rest coll)) [a b])))"
                        "(pr-str (search (W. 1 2) [:x :y :z]))"))))
  (testing "naming the object anyway is accepted, with a warning"
    ;; ClojureScript's own recur-test writes one of its four records this way and
    ;; says a warning is emitted, so refusing it would cost us the namespace
    (is (str/includes?
         (h/warnings #(out "(defprotocol ISearch (search [this coll]))"
                           "(deftype U [n] ISearch
                              (search [this coll]
                                (when (seq coll)
                                  (if (= n (first coll)) n (recur this (rest coll))))))"
                           "(pr-str (search (U. :c) [:a :b :c]))"))
         "protocol-impl-recur-with-target"))
    ;; and the value goes nowhere: the object is still the one the method was
    ;; called on, so the fields still read
    (is (= ":c" (out "(defprotocol ISearch (search [this coll]))"
                     "(deftype U [n] ISearch
                        (search [this coll]
                          (when (seq coll)
                            (if (= n (first coll)) n (recur this (rest coll))))))"
                     "(pr-str (search (U. :c) [:a :b :c]))"))))
  (testing "and everything else keeps every parameter it has"
    ;; an Object method takes no object parameter - the host passes the receiver -
    ;; so there is nothing for recur to skip. cljs.analyzer's marker sits on the fn
    ;; form and covers these too, which is why ours sits on the parameter instead.
    (is (= ":done" (out "(deftype V [n] Object (down [this k] (if (zero? k) n (recur (dec k)))))"
                        "(pr-str (.down (V. :done) 3))")))
    ;; a fn nested inside a method is an ordinary fn
    (is (= "[:n 0]" (out "(defprotocol ISearch (search [this coll]))"
                         "(deftype X [n] ISearch
                            (search [this coll]
                              (let [f (fn [c] (if (seq c) (recur (rest c)) [n (count c)]))]
                                (f coll))))"
                         "(pr-str (search (X. :n) [:a :b]))")))
    ;; and a method reached through extend-type is an ordinary function, so recur
    ;; rebinds the object like any other parameter - Clojure splits the same way,
    ;; and stock ClojureScript refuses the one-argument recur here
    (is (= ":b" (out "(defprotocol ISearch (search [this coll]))"
                     "(deftype A [n])"
                     "(extend-type A ISearch
                        (search [this coll]
                          (when (seq coll)
                            (if (= (.-n this) (first coll)) (.-n this) (recur this (rest coll))))))"
                     "(pr-str (search (A. :b) [:a :b]))")))))

(h/deftest-when h/node? test-a-wrong-recur-count-in-a-method-says-so
  ;; The count a method's recur wants is not its parameter count, so the message
  ;; has to say which one it means or it reads as a compiler bug.
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"recur expects 1 argument\(s\), got 3.*does not rebind the object"
       (out "(defprotocol ISearch (search [this coll]))"
            "(deftype T [n] ISearch (search [this coll] (recur this coll coll)))"
            "1"))))

;; --- defrecord* -------------------------------------------------------------

(h/deftest-when h/node? test-a-record-outside-cljs-core-is-a-map
  ;; THE GATE THIS RETIREMENT PASSED THROUGH, and the reason it found two defects.
  ;; A defrecord is fourteen extend-types on cljs.core protocols plus a special
  ;; form, so it exercises in one line everything a deftype does not: a core
  ;; protocol resolved from a namespace that is not cljs.core, and a field the
  ;; expansion writes to.
  ;; #app.t.R, with a DOT: that is the spelling core.cljc's defrecord builds into
  ;; pr-open, and Clojure on the JVM prints a record the same way.
  (is (= (str/join "\n" ["#app.t.R{:a 1, :b 2}" "#app.t.R{:a 1, :b 2, :c 3}"
                         "1" "true" "2" "{:a 1, :b 2}" "[:a :b]" "{:b 2}" "true"])
         (h/output-with-core
          (h/core-env 'app.t)
          "(defrecord R [a b])
           (def r (->R 1 2))
           (js/console.log (pr-str r))
           (js/console.log (pr-str (assoc r :c 3)))
           (js/console.log (:a r))
           (js/console.log (= r (->R 1 2)))
           (js/console.log (count r))
           (js/console.log (pr-str (into {} r)))
           (js/console.log (pr-str (vec (keys r))))
           (js/console.log (pr-str (dissoc r :a)))
           (record? r)"))))

(deftest test-a-core-protocol-resolves-the-same-way-for-a-macro
  ;; The first of the two defects, at the point it went wrong rather than at the
  ;; symptom. §5.12 put the refer half in analyze-symbol alone, so a MACRO asking
  ;; the same question got a different answer: ICloneable in app.t resolved to
  ;; app.t/ICloneable, extend-type spelled a property nobody dispatches on, and a
  ;; record quietly failed to satisfy any of the fourteen. Both callers now ask
  ;; clojure.cljs.env/resolve-var, so neither can drift from the other.
  (let [cenv (h/core-env 'app.t)]
    (is (= 'cljs.core/ICloneable (env/var-sym cenv 'ICloneable)))
    (is (= (names/protocol-name 'cljs.core/ICloneable)
           (names/protocol-name (env/var-sym cenv 'ICloneable))))
    (testing "and a def of the same name here still wins"
      (intern (env/cljs-ns cenv 'app.t) 'ICloneable)
      (is (= 'app.t/ICloneable (env/var-sym cenv 'ICloneable))))))

(h/deftest-when h/node? test-defrecord-adds-three-fields
  ;; the defrecord MACRO is core.cljc's and arrives with M5; the special form is
  ;; here, and the three names are not ours to choose - that macro reads them back
  (is (= "1 2 true"
         (out "(defrecord* R [a b] self nil)"
              "(def r (new R 1 2 nil nil nil))"
              "(js* \"[~{},~{},~{}].join(' ')\"
                 (.-a r) (.-b r) (js* \"~{} === null\" (.-__meta r)))")))
  (is (= '[a b __meta __extmap __hash]
         (:fields (meta (env/resolve-var (doto (h/fresh-env)
                                           (h/analyze '(defrecord* R [a b] self nil)))
                                         'R))))))

;; --- determinism ------------------------------------------------------------

(h/deftest-when h/node? test-a-type-compiles-to-the-same-text-twice
  ;; deftype's self symbol is an auto-gensym, minted when that macro was READ, so
  ;; it is a constant of the macro rather than fresh per expansion - and its number
  ;; never reaches the output anyway. A gensym here would rewrite every module that
  ;; defines a type on every compile.
  (let [cenv (h/core-env)
        text #(h/js cenv (src "(defprotocol IShape (-area [this]))"
                              "(deftype Point [x y] IShape (-area [this] (js* \"~{} * ~{}\" x y)))"
                              "(-area (new Point 1 2))"))]
    (is (= (text) (text)))
    (is (not (str/includes? (text) "__auto__")))))

(h/deftest-when h/node? test-a-multi-arity-method-does-not
  ;; AND THIS IS THE EXCEPTION, found by retiring clojure.cljs.protocols: our own
  ;; defprotocol built a multi-arity dispatch by hand, and cljs.core's builds one
  ;; through multi-arity-fn, whose body is a `case` - and cljs.core's case macro
  ;; mints a (gensym) for the value it tests. So the two compilations differ in one
  ;; name, `G__4233` against `G__4235`, and the module is rewritten every time.
  ;;
  ;; This is not new and it is not about protocols: EVERY multi-arity defn carries
  ;; it, which is a good deal wider than the "core.cljs uses macros that call
  ;; gensym" that doc/cljs-compiler.md §5.12 recorded. Pinned here rather than
  ;; fixed because the fix is to make gensym deterministic per compilation unit,
  ;; which is its own piece of work - and it has to come through this assertion
  ;; and through driver-test/test-a-second-compile-writes-nothing.
  (let [cenv (h/core-env)
        text #(h/js cenv (src shape point "(-area (new Point 1 2))"))
        [a b] [(text) (text)]]
    (is (not= a b))
    (is (= (str/replace a #"G\$US\$\$US\$\d+" "G")
           (str/replace b #"G\$US\$\$US\$\d+" "G"))
        "and in nothing else")))

;; --- fuzzing ----------------------------------------------------------------
;;
;; The tests above are cases someone thought of. These are not: a random program
;; is generated - protocols with random methods and arities, types implementing a
;; random subset of them, native extensions on a random subset of the base types -
;; and every call it could make is checked against a model written here.
;;
;; What makes it an oracle rather than a smoke test is that every implementation
;; returns a NUMBER THAT IDENTIFIES IT: tag*100 + field*10 + the sum of its extra
;; arguments. So a call reaching the wrong implementation - the whole class of bug
;; the calling convention can have - does not merely fail, it says which one it
;; reached instead. It found two while being written: a multi-arity extend-type on
;; a native type silently kept only its last arity, and a dotted method name
;; produced a property of a property.

(def ^:private proto-names  '[P Q GT US C IShape])
(def ^:private method-names '[-m m>n m-n a>b -q! nsx xarity])
(def ^:private field-names  '[x y a-b n __v])

(def ^:private samples
  "One sample value per $CLJS.typeOf answer. `symbol` is here as a VALUE only - it
  is not a base type, so it is what exercises the \"_\" default entry."
  [["string" "\"hi\""] ["number" "7"] ["null" "nil"] ["boolean" "true"]
   ["array" "(js* \"[1,2]\")"] ["object" "(js* \"({})\")"]
   ["symbol" "(js* \"Symbol('s')\")"]])

(defn- some-of [^java.util.Random r xs n] (take n (shuffle (vec xs))))
(defn- params-of [a] (into '[this] (map #(symbol (str "p" %)) (range 1 a))))
(def ^:private arg-values {1 [] 2 [3] 3 [3 5]})
(defn- argsum [a] (reduce + (arg-values a)))

(defn- body-form
  "tag*100 + field*10 + the sum of the extra arguments."
  [tag field params]
  (let [extra (rest params)]
    (list* 'js* (str "~{} * 100 + ~{} * 10" (apply str (repeat (count extra) " + ~{}")))
           tag (or field 0) extra)))

(defn- gen-program [^java.util.Random r]
  (let [pnames (some-of r proto-names (inc (.nextInt r 3)))
        mnames (some-of r method-names (+ 2 (.nextInt r 4)))
        ;; a protocol method is a var, so the names must be distinct across ALL
        ;; the protocols, not only within one
        split  (loop [ms mnames, out [], ps pnames]
                 (if (empty? ps) out
                     (let [n (max 1 (min (count ms) (inc (.nextInt r 2))))]
                       (recur (drop n ms) (conj out (vec (take n ms))) (rest ps)))))
        protos (mapv (fn [p ms]
                       {:name p
                        :methods (mapv (fn [m]
                                         {:name m
                                          :arities (vec (sort (distinct (repeatedly
                                                                         (inc (.nextInt r 2))
                                                                         #(inc (.nextInt r 3))))))})
                                       ms)})
                     pnames split)
        tag    (atom 0)
        types  (mapv (fn [i]
                       {:name (symbol (str "T" i))
                        :fields (vec (some-of r field-names (.nextInt r 3)))
                        :impls (into {} (for [p protos
                                              :when (zero? (.nextInt r 2))
                                              m (:methods p)
                                              a (:arities m)
                                              :when (zero? (.nextInt r 3))]
                                          [[(:name p) (:name m) a] (swap! tag inc)]))})
                     (range (inc (.nextInt r 3))))
        nat    (into {} (for [p protos, m (:methods p)
                              [k _] (remove #(= "symbol" (first %)) samples)
                              :when (zero? (.nextInt r 4))]
                          [[(:name p) (:name m) k] (swap! tag inc)]))
        nat    (into nat (for [p protos, m (:methods p) :when (zero? (.nextInt r 5))]
                           [[(:name p) (:name m) "_"] (swap! tag inc)]))]
    {:protos protos :types types :natives nat}))

(defn- arities-of [protos pn mn]
  (:arities (first (filter #(= mn (:name %))
                           (:methods (first (filter #(= pn (:name %)) protos)))))))

(defn- gen-source [{:keys [protos types natives]}]
  (str/join
   "\n"
   (concat
    (for [p protos]
      (str "(defprotocol " (:name p) " "
           (str/join " " (for [m (:methods p)]
                           (str "(" (:name m) " "
                                (str/join " " (map (comp pr-str params-of) (:arities m))) ")")))
           ")"))
    (for [t types]
      (str "(deftype " (:name t) " " (pr-str (:fields t)) " "
           (str/join
            " "
            (for [p protos
                  :let [ms (for [m (:methods p), a (:arities m)
                                 :when (get (:impls t) [(:name p) (:name m) a])]
                             [(:name m) a])]
                  :when (seq ms)]
              (str (:name p) " "
                   (str/join " " (for [[mn a] ms]
                                   (str "(" mn " " (pr-str (params-of a)) " "
                                        (pr-str (body-form (get (:impls t) [(:name p) mn a])
                                                           (first (:fields t)) (params-of a)))
                                        ")"))))))
           ")"))
    ;; every arity of one method arrives in ONE extend-type clause group, because
    ;; a native entry is keyed by the method alone - and because that is the only
    ;; shape extend-type accepts. cljs.core's own docstring spells it
    ;; `(baz ([x] ...) ([x y] ...))`, and repeating the clause name instead earns
    ;; an extend-type-invalid-method-shape warning and keeps only the LAST arity.
    ;; deftype above is the other way round and takes a clause per arity, which is
    ;; ClojureScript's asymmetry rather than ours.
    (for [[[pn key] entries] (group-by (fn [[[pn _ k] _]] [pn k]) natives)]
      (str "(extend-type " (cond (= "null" key) "nil" (= "_" key) "default" :else key)
           " " pn " "
           (str/join
            " "
            (for [[[_ mn _] tg] entries
                  :let [as   (arities-of protos pn mn)
                        arm  (fn [a] (str (pr-str (params-of a)) " "
                                          (pr-str (body-form tg nil (params-of a)))))]]
              (if (= 1 (count as))
                (str "(" mn " " (arm (first as)) ")")
                (str "(" mn " " (str/join " " (map #(str "(" (arm %) ")") as)) ")"))))
           ")"))
    (for [t types]
      (str "(def v" (:name t) " (new " (:name t) " "
           (str/join " " (map inc (range (count (:fields t))))) "))")))))

(defn- gen-values [{:keys [types]}]
  (concat (for [t types] {:expr (str "v" (:name t)) :type t :key "object"})
          (for [[k e] samples] {:expr e :key k})))

(defn- want-call
  "The model. A prototype implementation wins; otherwise the native table for this
  value's type, then the default entry; otherwise the call throws."
  [{:keys [natives]} v p mn a]
  (if-let [tag (and (:type v) (get (:impls (:type v)) [(:name p) mn a]))]
    (+ (* 100 tag) (* 10 (if (seq (:fields (:type v))) 1 0)) (argsum a))
    (if-let [nt (or (get natives [(:name p) mn (:key v)])
                    (get natives [(:name p) mn "_"]))]
      (+ (* 100 nt) (argsum a))
      "ERR")))

(defn- want-satisfies [{:keys [natives]} v p]
  (boolean
   (or (and (:type v) (some (fn [[pn _ _]] (= pn (:name p))) (keys (:impls (:type v)))))
       (some (fn [[pn _ k]] (and (= pn (:name p)) (#{(:key v) "_"} k))) (keys natives)))))

(defn- gen-calls
  "Only at DECLARED arities. Calling a single-arity protocol method with the wrong
  number of arguments is ordinary JavaScript under-application, not a question
  about protocols, and the emitter's own tests own it."
  [prog]
  (concat
   (for [v (gen-values prog), p (:protos prog), m (:methods p), a (:arities m)]
     {:src (str "(try (" (:name m) " " (:expr v)
                (when (seq (arg-values a)) (str " " (str/join " " (arg-values a))))
                ") (catch :default e \"ERR\"))")
      :want (str (want-call prog v p (:name m) a))})
   (for [v (gen-values prog), p (:protos prog)]
     {:src (str "(try (satisfies? " (:name p) " " (:expr v) ") (catch :default e \"ERR\"))")
      :want (str (want-satisfies prog v p))})))

(defn- fuzz-once [seed]
  (let [prog (gen-program (java.util.Random. seed))
        cs   (gen-calls prog)
        source (str (gen-source prog) "\n"
                    "(js* \"[" (str/join "," (repeat (count cs) "~{}")) "].join(' ')\" "
                    (str/join " " (map :src cs)) ")")]
    {:seed seed :calls (count cs) :source source
     :got (h/output-with-core (h/core-env) source)
     :want (str/join " " (map :want cs))}))

(h/deftest-when h/node? test-generated-programs-route-every-call-to-the-right-implementation
  (let [runs (map fuzz-once (range 1 13))]
    (doseq [{:keys [seed got want source calls]} runs]
      (is (= want got)
          (str "seed " seed ", " calls " calls\n"
               (when (not= want got)
                 (str/join "\n" (->> (map vector (str/split want #" ") (str/split got #" "))
                                     (keep-indexed (fn [i [w g]]
                                                     (when (not= w g)
                                                       (str "  call " i ": want " w ", got " g))))
                                     (take 5))))
               "\n" source)))
    (is (< 300 (reduce + (map :calls runs))))))
