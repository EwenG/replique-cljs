;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "AST -> JavaScript, destination-driven.

  Clojure's `if` is an expression; JavaScript's is a statement. ClojureScript
  resolves that by threading a :context (:expr / :statement / :return) through the
  analyzer and wrapping in an immediately-invoked function whenever an expression
  position needs statements - so (let* [x 1] (if x 1 2)) compiles to

      (function (){var x = (1);
      if(cljs.core.truth_(x)){ return (1); } else { return (2); }
      })()

  We do it the other way round. emit returns TWO channels (see ->result):

      {:stmts [\"...\" ...]   statements that must run first
       :expr  \"...\"}        a JavaScript expression holding the value

  A node emits its children, concatenates their :stmts before its own, and hands
  back an expression. Statements bubble up to the nearest enclosing statement
  position instead of being trapped behind a function boundary, so the same form
  needs nothing but:

      let x__1 = 1;
      // value: (truth_(x__1) ? 1 : 2)

  A temporary appears only when a branch really needs statements. Give the then
  branch a binding, and (let* [x 1] (if x (let* [y 2] y) 3)) is:

      let x__1 = 1;
      let t__3;
      if (truth_(x__1)) { let y__2 = 2; t__3 = y__2; } else { t__3 = 3; }
      // value: t__3

  This is destination-driven code generation. It costs a two-part return value and
  buys back the whole :context mechanism: statement-versus-return is decided once,
  per statement, by whoever consumes the result - not carried through every node.
  It matters more here than in ClojureScript, which leans on :advanced to clean the
  wrappers up afterwards; :optimizations :none is the only output we produce.

  One consequence to keep in mind: nested scopes flatten into one JavaScript scope,
  which is why the analyzer makes every local name unique.

  A note on the strings. When a source map is being made they are not strings but
  chunks that know which ClojureScript line each of their own lines came from, and
  this namespace does not notice: `str` below is clojure.cljs.source-map/cat, which
  is clojure.core/str plus that bookkeeping and is clojure.core/str exactly when
  there is no bookkeeping to do. Everything here builds text with `str` and reads
  it back with `str`, so the two cases are the same code (doc/cljs-compiler.md
  §5.43)."}
  clojure.cljs.emitter
  (:refer-clojure :exclude [str])
  (:require [clojure.cljs.names :as names]
            [clojure.cljs.source-map :as sm]
            ;; for JSValue alone, and for the same reason the analyzer requires
            ;; it: #js is a data reader, so a quoted #js form arrives here as the
            ;; marker type the reader wrapped it in
            [clojure.cljs.reader :as reader])
  (:import [cljs.tagged_literals JSValue]))

(def ^:private str
  "clojure.core/str, composing the source positions of what it concatenates.

  Referred as `str` on purpose: every line and every expression in this namespace
  is already built with it, so provenance travels through all of them without one
  of them being rewritten. It returns a plain String whenever no argument carries
  a position, which is every compile that did not ask for a source map. See
  clojure.cljs.source-map."
  sm/cat)

(def ^:dynamic ^:private *pos*
  "Where the node being emitted was written: {:file :line :column}, or nil.

  Bound by `emit` from the node's :env, which clojure.cljs.source-info fills in -
  so this is nil, and everything below it a plain string, unless that pass has
  run.

  It is read in exactly one place, ->result, which writes it onto every line the
  node produced that nothing deeper has already claimed. The rule is source-info's
  own: a line belongs to the nearest enclosing node that claims it."
  nil)

(defn- node-pos
  "The position on `node`, for the few callers that build a line from a node they
  are not currently inside - see emit-body and emit-bindings."
  [node]
  (let [e (:env node)]
    (when-let [l (:line e)]
      {:file (:file e) :line l :column (:column e)})))

(def ^:dynamic *static-dispatch*
  "Whether a call whose head is a var of KNOWN SHAPE may go straight to the arity
  that answers it - foo.cljs$core$IFn$_invoke$arity$2(a, b) - instead of through
  the function the var holds.

  FALSE, and it belongs to optimized compilation. ClojureScript draws the line in
  the same place: *cljs-static-fns* is false everywhere except :advanced and the
  builds that ask for it by name, so the mode with static call sites is the
  whole-program one, where nothing is redefined at runtime, and the mode where
  things are redefined has none. One axis, no overlap.

  WHAT A STATIC CALL SITE PINS IS THE ARITY. A redefinition is still SEEN either
  way - the property is read off whatever the var holds now, which is §5.2 doing
  its job. But the call site names an arity: redefine a two-arity foo as a
  one-argument one and it reads an undefined property, where the dispatch function
  would have answered `Invalid arity: 2` - the same program failing, but failing
  where the mistake is.

  IT WAS TRUE FOR FILES UNTIL §5.44, on the argument that a file is already on
  disk and cannot be protected. That argument is upstream's and does not hold
  here: driver/body-script exists to re-evaluate a file's body into a live runtime,
  so a file's call sites are as exposed to a redefinition as a REPL input's. What
  it cost to turn off was measured rather than guessed - 2.4% on the M6 slice, and
  1.4% of output size back - and the reason it was turned ON has since been fixed
  by something else (§5.35 gave a variadic function's body a closed-over delegate,
  so cljs.spec.test.alpha's instrument no longer sends `=` into infinite
  recursion). §5.33 built it, §5.44 reversed the default and says why.

  Bound true by the compilation driver on request (:static-dispatch), which is
  where doc/cljs-advanced.md's O-ladder will ask for it. Nothing else does, so what
  keeps the static path honest is emitter-test and core-test binding it by hand and
  the calling-convention suite's first property (§5.40), which compiles the same
  shape both ways and compares."
  false)

;; --- the destination-driven result ------------------------------------------

(defn- ->result
  "The destination-driven result. Two channels:

    :stmts  statements, which stop at the nearest enclosing statement position
    :expr   a JavaScript expression holding the value

  There used to be a third, :decls, for module-scope declarations that had to rise
  past any enclosing function: (def x 1) inside a function body needed `var x;` at
  module scope and the assignment where it was written. A var is a property of a
  namespace object now (see def-name), and a property needs no declaration, so the
  channel had no remaining producer."
  [stmts expr]
  (if *pos*
    {:stmts (mapv #(sm/fill *pos* %) stmts)
     :expr  (if expr (sm/fill *pos* expr) expr)}
    {:stmts (vec stmts) :expr expr}))

(defn- terminal
  "Mark a result as one control never leaves - recur jumps, and later throw. Its
  :expr is meaningless, so consumers must not use it: emit-do stops emitting after
  one, and emit-if skips the temporary assignment in a branch that ends in one."
  [r]
  (assoc r :terminal? true :expr nil))

(defn- effect-stmts
  "A result's statements, plus its value evaluated for whatever effects it has -
  unless the result says it has none (see no-effect)."
  [{:keys [stmts expr no-effect?]}]
  (cond-> (vec stmts)
    (not no-effect?) (conj (str expr ";"))))

(defn- short-circuit
  "Results whose values all feed one enclosing node, in order. If one of them never
  returns - a throw, or a recur - then nothing after it can run and the enclosing
  node's expression is never built, so the whole node becomes terminal too.

  This is what makes (f (throw e)) emit `throw e;` and stop, where ClojureScript
  needs a function wrapper. Returns nil when every result returns normally, which
  is the ordinary case."
  [results]
  (when (some :terminal? results)
    (let [kept (vec (take-while (complement :terminal?) results))
          cut  (nth results (count kept))]
      (terminal
       (->result
        ;; the values computed before the cut are still evaluated, for whatever
        ;; effects they have
        (-> (into [] (mapcat effect-stmts) kept)
            (into (:stmts cut)))
        nil)))))

(defn- stable
  "Mark a result whose expression yields the same value however late it is
  evaluated, so in-order need not pin it in place.

  Not the same as `has no side effects`, which is what this used to test, and the
  difference is a wrong answer: reading a var has no side effects, but a later
  sibling can set! it or def over it, and the read would then float past the write
  and see the new value. Only a literal and a local qualify - a local because
  nothing can assign one (set! refuses them, and a recur is terminal, so anything
  it could rebind is unreachable from here)."
  [r]
  (assoc r :stable? true))

(defn- no-effect
  "Mark a result whose expression does nothing observable, so that as a statement
  it can be dropped rather than emitted as a dead line.

  Also narrower than it looks. A property read is NOT included: o.x throws when o
  is null, and dropping the line would swallow the TypeError. What is included is
  a literal, a local, a var read - the namespace object always exists, so reading
  a property of it cannot throw - and a def, whose value is the property it just
  assigned. Without this, every top-level def would be followed by a dead line
  naming the var."
  [r]
  (assoc r :no-effect? true))

(defn runtime-import
  "The import an emitted module opens with.

  `specifier` is how that module reaches runtime.js from where it sits - a relative
  path within an output directory - so it belongs to the output layout, which is
  M3's to decide and not the emitter's. The names are bound as $ns and truth_
  because that is what emitted code spells them, and $CLJS because a namespace
  marks itself loaded through it whichever way it arrived (doc/cljs-repl.md 7.2)."
  [specifier]
  (str "import { $CLJS, ns as $ns, truth_ } from \"" specifier "\";"))

(defn ns-import
  "The import a module carries for a namespace it requires. For effect only: the
  vars are reached through $ns, not through a binding, so there is nothing to name
  here (doc/cljs-repl.md 3.1). What the line buys is ORDER - the module system
  evaluates the imported file before this one, which is how a cold load gets its
  dependencies in the right sequence without anything computing that sequence.

  Its script counterpart is the await $CLJS.require of script-prologue."
  [specifier]
  (str "import \"" specifier "\";"))

(defn js-import
  "The import a module carries for a JavaScript module it requires:

      import { $module as react$js } from \"../../npm/react.js\";

  `binding` is clojure.cljs.names/js-alias of the specifier and `specifier` is how
  this module reaches the file, which is the output layout's to compute - the same
  split the two imports above make.

  ONE IMPORT, WHATEVER THE ns FORM ASKED FOR, and one binding out of it. :as names
  the module, :refer names an export, :default names the export called `default`,
  and a $ in the specifier names a path into it; all four are property reads off
  the one object this line binds, exactly as a var of ours is a property of a
  namespace object and a goog var is a property of its provide. So :as and :refer
  of one specifier are one import between them, and every reference through either
  is a property read.

  THE OBJECT IS `$module`, WHICH IS NOT THE FILE'S NAMESPACE OBJECT, and that
  distinction is the whole of the CommonJS interop. npm/react.js is written by
  build_npm.mjs, which gives every module it builds exactly one export: the
  namespace object when the package is an ES module, and `module.exports` itself
  when it is CommonJS. `import * as` here would bind the wrapper esbuild puts round
  a CommonJS package instead - a fresh object with the exports copied onto it and a
  `default` added - and then (:require [\"debounce\" :as debounce]) would bind
  something uncallable, because that package's entire value IS the function it
  assigned to module.exports. See doc/cljs-npm.md §2.1.

  A NAMED IMPORT IS AFFORDABLE BECAUSE THERE IS ONLY EVER ONE. The objection to
  them is that a named import per :refer would bind a second kind of name in module
  scope and could not be spelled at all by the script counterpart below, which is
  the half of doc/cljs-repl.md §4 that keeps one body running two ways. Neither
  applies to a single fixed name: `$module` is the same word for every specifier,
  and the script path reads it as the property it is.

  Its script counterpart is the await $CLJS.requireJs of script-prologue."
  [binding specifier]
  (str "import { $module as " binding " } from \"" specifier "\";"))

(def runtime-globals
  "The line an evaluated script opens with, where runtime-import's is the line a
  module opens with.

  A script may not contain an import declaration at all, so the two callers of the
  prelude cannot reach it the same way; runtime.js installs itself on
  globalThis.$CLJS for exactly this one (doc/cljs-repl.md \u00a73.1). Binding the same
  three names here is what lets the BODY be identical either way (\u00a74), which is the
  whole reason a namespace can be shipped as a script instead of imported.

  It throws if the prelude was never loaded, and that is the point: the alternative
  is `$ns is not defined` thrown from somewhere in the middle of the form."
  "const $CLJS = globalThis.$CLJS, $ns = $CLJS.ns, truth_ = $CLJS.truth_;")

;; --- literals ---------------------------------------------------------------

(defn- emit-number
  "A JavaScript numeric literal, spelled as ClojureScript spells it.

  pr-str will not do: it round-trips CLOJURE syntax, and ##Inf, ##NaN, 10N and 1.5M
  are none of them things JavaScript can read. Verified against cljs.compiler:
  ##Inf/##NaN have JavaScript spellings, and a BigInt or BigDecimal goes through
  double - 10N is 10.0 and 1.5M is 1.5 - because JavaScript has one number type and
  a ClojureScript program cannot observe the difference. A Ratio has no such
  reading, and the analyzer refuses it, as cljs.compiler does."
  [val]
  (let [d (double val)]
    (cond
      (Double/isNaN d)      "NaN"
      (Double/isInfinite d) (if (pos? d) "Infinity" "-Infinity")
      ;; An integer keeps its exact spelling, PARENTHESISED, which is not
      ;; decoration: 42.toString() is a syntax error where (42).toString() is not,
      ;; because the dot after an integer reads as a decimal point. A double needs
      ;; no such help - 1.5.toFixed(1) is already legal - and cljs.compiler
      ;; parenthesises exactly these.
      (or (instance? Long val) (instance? Integer val)
          (instance? Short val) (instance? Byte val)) (str "(" val ")")
      :else (str d))))

;; --- the collections cljs.core builds ----------------------------------------
;;
;; A vector, map, set or list is an OBJECT OF A TYPE cljs.core defines, so
;; building one is a call into cljs.core and nothing else will do - which is why
;; every one of these was refused until core.cljs existed to define the types
;; (doc/cljs-compiler.md §5.7). The spellings below are cljs.compiler's, chosen
;; deliberately: they are the constructors core.cljs actually exports, and the
;; fast paths (a small vector built directly, a small map built as an array map)
;; are what its own reader and its own emitted code rely on.
;;
;; Only #js and the regex are free of cljs.core, because a JavaScript array,
;; object and regex are the host's own.

(defn- core-name
  "The JavaScript for a cljs.core var the COMPILER names, rather than the program:
  PersistentVector, list, and the handful of others below.

  def-name's rule, applied one namespace earlier than def-name can see it - a var
  is a property of its namespace object, so this is cljs$core$ns.PersistentVector
  and the prologue is what binds cljs$core$ns (see ns-prologue, which binds it in
  every module for exactly this reason)."
  [sym]
  (str (names/ns-alias 'cljs.core) "." (names/munge sym)))

(defn- static-name
  "A property hung on one of those vars: PersistentVector.EMPTY_NODE.

  Written in the Clojure spelling core.cljs writes, and put through host-name to
  get there, because a property is the host's name and not ours (§5.3) - so
  .-EMPTY-NODE, with a hyphen, is what core.cljs sets and EMPTY_NODE is what both
  sides read.

  On today's five names munge would agree, since none of them holds a _ or a $;
  what the rule buys is that a name that did would go the same way as every other
  property access, rather than becoming EMPTY$US$NODE and landing somewhere no
  reader of core.cljs could find it."
  [sym]
  (names/host-name sym))

(def ^:private array-map-threshold
  "Above this many entries a map literal is built as a hash map rather than an
  array map. cljs.core/PersistentArrayMap's own threshold, and it has to be: a
  larger array map would be one that no cljs.core operation would ever produce."
  8)

(defn- comma [xs] (sm/join ", " xs))

(defn- vector-js [items]
  (cond
    (empty? items) (str (core-name 'PersistentVector) "." (static-name 'EMPTY))
    ;; one node holds 32 elements, so a vector of fewer than that is its own tail
    ;; and can be built without the trie walk fromArray does
    (< (count items) 32)
    (str "new " (core-name 'PersistentVector) "(null, " (count items) ", 5, "
         (core-name 'PersistentVector) "." (static-name 'EMPTY-NODE) ", ["
         (comma items) "], null)")
    :else
    (str (core-name 'PersistentVector) "." (static-name 'fromArray)
         "([" (comma items) "], true)")))

(defn- map-js
  "A map literal. `distinct-keys?` says whether the keys are known to be distinct
  AS JAVASCRIPT VALUES - see const-key, which is what decides it for constants."
  [ks vs distinct-keys?]
  (cond
    (empty? ks) (str (core-name 'PersistentArrayMap) "." (static-name 'EMPTY))
    (<= (count ks) array-map-threshold)
    (if distinct-keys?
      (str "new " (core-name 'PersistentArrayMap) "(null, " (count ks) ", ["
           (comma (interleave ks vs)) "], null)")
      ;; two keys that turn out equal at run time have to collapse into one entry,
      ;; and only assoc knows how to do that
      (str (core-name 'PersistentArrayMap) "." (static-name 'createAsIfByAssoc)
           "([" (comma (interleave ks vs)) "])"))
    :else
    (str (core-name 'PersistentHashMap) "." (static-name 'fromArrays)
         "([" (comma ks) "],[" (comma vs) "])")))

(defn- set-js [items distinct?]
  (cond
    (empty? items) (str (core-name 'PersistentHashSet) "." (static-name 'EMPTY))
    distinct?
    (str "new " (core-name 'PersistentHashSet) "(null, new "
         (core-name 'PersistentArrayMap) "(null, " (count items) ", ["
         (comma (interleave items (repeat "null"))) "], null), null)")
    :else
    (str (core-name 'PersistentHashSet) "." (static-name 'createAsIfByAssoc)
         "([" (comma items) "])")))

(defn- list-js [items]
  (if (empty? items)
    (str (core-name 'List) "." (static-name 'EMPTY))
    ;; .call(null, ...), because cljs.core/list is an ordinary ClojureScript
    ;; function and that is how emit-invoke calls one. cljs.compiler writes
    ;; cljs.core.list(...) instead; both work on a function our fn* emits, and
    ;; agreeing with our own calling convention is worth more than agreeing with
    ;; theirs, since a change to it should reach this line too.
    (str (core-name 'list) ".call(" (comma (cons "null" items)) ")")))

(defn- js-array-js [items] (str "[" (comma items) "]"))

(defn- js-object-js
  "#js {:a 1}. The key is a property name, so (name k) is the whole of it - a
  keyword, a symbol and a string all name the same property."
  [ks vs]
  (str "({" (comma (map (fn [k v] (str (pr-str (name k)) ": " v)) ks vs)) "})"))

(defn- regex-js
  "A JavaScript regex literal, /.../ with its flags.

  Clojure spells its flags as an inline (?idmsux) group at the front, which
  JavaScript has no reading for, so they move to the end where JavaScript keeps
  them. The slashes inside the pattern are escaped because an unescaped one would
  close the literal; the empty pattern gets a constructor call, because // opens a
  comment."
  [^java.util.regex.Pattern re]
  (let [s (str re)]
    (if (= "" s)
      "(new RegExp(\"\"))"
      (let [[_ flags pattern] (re-find #"^(?:\(\?([idmsux]*)\))?(.*)" s)]
        (str "/" (clojure.string/replace pattern "/" "\\/") "/" flags)))))

;; --- keywords and symbols ---------------------------------------------------
;;
;; Both are OBJECTS OF A TYPE cljs.core defines, reached the same way the
;; collections above are reached: core-name, so the spelling is right from a
;; module and from a REPL script alike (§5.2).
;;
;; THE HASH IS COMPUTED HERE, on the JVM, and baked into the literal - which is
;; only sound because Clojure's hash of a keyword and cljs.core's hash of the
;; keyword a program builds at runtime are the same number. That is by design on
;; both sides rather than by luck, and the test below pins it, because if it ever
;; drifted the symptom would be a map that has a key and cannot find it.

(defn- keyword-js
  "A Keyword: (ns, name, fqn, hash).

  fqn is the whole name with its slash - what toString and (name k) are read off -
  and it is stored rather than computed because every keyword carries it and
  rebuilding it per call would cost more than the string does."
  [kw]
  (let [ns (namespace kw), nm (name kw)]
    (str "(new " (core-name 'Keyword) "("
         (if ns (pr-str ns) "null") ", " (pr-str nm) ", "
         (pr-str (if ns (str ns "/" nm) nm)) ", "
         (emit-number (hash kw)) "))")))

(defn- symbol-js
  "A Symbol: (ns, name, str, hash, meta).

  The trailing null is the metadata slot, and it is always null even though
  const-js does carry metadata now (§5.21): it carries it the way every other
  value gets it, as a with-meta call around this expression, so (quote ^:x a) is
  with_meta(new Symbol(...), {:x true}) and the slot stays empty. cljs.compiler
  emits the same shape."
  [sym]
  (let [ns (namespace sym), nm (name sym)]
    (str "(new " (core-name 'Symbol) "("
         (if ns (pr-str ns) "null") ", " (pr-str nm) ", "
         (pr-str (if ns (str ns "/" nm) nm)) ", "
         (emit-number (hash sym)) ", null))")))

(declare const-js)

(defn- const-key
  "What decides whether two CONSTANT keys of a map, or two constant members of a
  set, are distinct as JavaScript values.

  Not =, and the difference is a wrong answer rather than a missed optimisation.
  1 and 1.0 are two Clojure keys and one JavaScript number, so {1 :a 1.0 :b} read
  as having distinct keys emits an array map holding the same key twice - a map
  that every later lookup disagrees with. Normalising a number to its double
  catches that pair; comparing everything else by its EMITTED SPELLING catches the
  rest, \\a and \"a\" included, and errs toward saying `not distinct`, which costs
  a createAsIfByAssoc and is always correct.

  cljs.compiler compares the analyzed nodes instead, and has the 1/1.0 bug."
  [val]
  (if (number? val) (double val) (const-js val)))

(defn- all-distinct? [vals]
  (apply distinct? ::one (map const-key vals)))

(declare const-js)

(defn- const-js*
  "The JavaScript for a constant - a literal, or a whole quoted structure.

  Recursive, and it can be: nothing inside a constant evaluates, so every piece
  is a string and the whole thing is one expression with no statements to order.
  A collection LITERAL is the other case, where the elements are expressions, and
  it gets a node of its own for exactly that reason (emit-vector and friends).

  A keyword and a symbol are ALLOCATIONS, not the strings they used to be - see
  keyword-js and symbol-js. They were placeholders for as long as no program had
  run cljs.core, and stopped being so the moment one could (doc/cljs-compiler.md
  §5.10).

  METADATA IS CARRIED, and const-meta below is what makes that affordable: the
  reader hangs :line and :column on every collection it reads, so the position
  keys come off first and what is left - usually nothing - becomes a with-meta
  call around the value. ClojureScript's arrangement. It bought nothing until a
  program could observe meta at all, and now one can (doc/cljs-compiler.md 5.21).

  RECURSIVE THROUGH THE STRUCTURE, unlike a literal: nothing inside a constant
  evaluates, so the metadata of a nested value is as much a constant as the value
  is, and '[^{:a 1} [x]] keeps the inner map."
  [val]
  (cond
    (nil? val)     "null"
    (true? val)    "true"
    (false? val)   "false"
    (string? val)  (pr-str val)
    (char? val)    (pr-str (str val))   ; ClojureScript has no character type
    (keyword? val) (keyword-js val)
    (symbol? val)  (symbol-js val)
    (number? val)  (emit-number val)
    (instance? java.util.regex.Pattern val) (regex-js val)
    ;; #inst - a host Date, from the epoch milliseconds of the Instant our reader
    ;; built. `Date` is a JavaScript global and is written as one, exactly as
    ;; regex-js writes `new RegExp`.
    ;;
    ;; AN INSTANT AND NOT A java.util.Date, which this used to take and which was
    ;; wrong before 1582: a Date is parsed with the JVM's hybrid Julian/Gregorian
    ;; calendar and a JavaScript Date is proleptic Gregorian, so #inst
    ;; "1500-01-10" came out nine days early. See clojure.cljs.reader's
    ;; cljs-data-readers. A Date reaching here now could only come from a data
    ;; reader a user registered, and it falls through to the message below rather
    ;; than being converted on a guess about which calendar they meant.
    (instance? java.time.Instant val)
    (str "(new Date(" (emit-number (.toEpochMilli ^java.time.Instant val)) "))")
    ;; #uuid - a cljs.core type, so it goes through core-name like Keyword and
    ;; Symbol. THE HASH IS THE HASH OF ITS STRING, computed here for the reason
    ;; the note above keywords gives, and it is the string's hash rather than the
    ;; UUID's: cljs.core has no UUID hash of its own, it hashes the text, and
    ;; Clojure's hash of that same text is the same number. ClojureScript emits
    ;; exactly this pair.
    (instance? java.util.UUID val)
    (str "(new " (core-name 'UUID) "(" (pr-str (str val)) ", "
         (emit-number (hash (str val))) "))")
    ;; Tested before the map test, which it no longer has to be: JSValue was a
    ;; defrecord of ours and a record is a map (doc/cljs-compiler.md 5.68). The
    ;; order stays as the defence it used to be the fix for.
    (instance? JSValue val)
    (let [v (.-val ^JSValue val)]
      (if (map? v)
        (js-object-js (keys v) (map const-js (vals v)))
        (js-array-js (map const-js v))))
    (map? val)    (map-js (map const-js (keys val)) (map const-js (vals val))
                          (all-distinct? (keys val)))
    (vector? val) (vector-js (map const-js val))
    (set? val)    (set-js (map const-js val) (all-distinct? val))
    (seq? val)    (list-js (map const-js val))
    :else
    ;; reached only through (quote x), which does not walk what it quotes - so
    ;; this is a value the reader produced and nothing here knows how to spell.
    ;; Saying so beats emitting its Clojure printed form and letting JavaScript
    ;; make what it can of it.
    (throw (ex-info (str "Not implemented yet: " (pr-str val) ", a "
                         (.getSimpleName (class val)) " constant")
                    {:val val}))))

(defn- const-js
  "const-js*, plus the metadata the value carries.

  Split from it so that the recursion goes through here: every piece of a quoted
  structure is a constant, and so is the metadata on every piece.

  A keyword and a symbol are IObj too, and a symbol can carry metadata a program
  reads - '^{:a 1} foo - so this is asked of the value rather than of the
  collections alone."
  [val]
  (let [js (const-js* val)]
    (if-let [m (reader/program-meta val)]
      (str (core-name 'with-meta) ".call(null, " js ", " (const-js m) ")")
      js)))

;; A refusal that has not happened yet. toString is the whole mechanism: the only
;; way to use an expression here is to put it in a string, so reading one of these
;; is exactly the event that should refuse. See `unspellable` below.
(deftype Unspellable [val]
  Object
  (toString [_]
    (throw (ex-info (str "Not implemented yet: " (pr-str val) ", a "
                         (.getSimpleName (class val)) " constant")
                    {:val val}))))

(defn- unspellable
  "The expression channel of a constant that has no JavaScript spelling.

  There is one such value today - a clojure.lang.Var, which reaches a form as the
  accidental expansion of a macro whose body ended in a def (analyzer/analyze says
  which macro and why). What is interesting is not that it cannot be spelled, but
  that NOT SPELLING IT IS USUALLY RIGHT: the macro was called for its effect, so
  its expansion sits where a value is discarded, and a discarded expression is one
  this emitter never reads. `no-effect` on the :const result is what drops it.

  So the refusal is DEFERRED rather than thrown: built eagerly, it would refuse a
  form that compiles to nothing at all. Dropped, this costs a line of JavaScript
  that was never going to exist. Read - bound in a let*, passed to a function,
  returned from a body - the `str` that reads it throws, and names what it could
  not spell. Both halves stay honest, and they match cljs.compiler in both
  positions: emit* :const there skips a :statement context before reaching
  emit-constant*, which has no Var method either.

  IT BYPASSES ->result DELIBERATELY. There is no text for a source position to be
  written onto, and sm/fill would force the very string this exists not to build."
  [val]
  {:stmts [] :expr (Unspellable. val)})

(defn- emit-const [{:keys [val]}]
  (if (instance? clojure.lang.Var val)
    (unspellable val)
    (->result [] (const-js val))))

;; --- emit -------------------------------------------------------------------

(defn- indent
  "Indent each statement by two spaces - the FIRST line of it, and no other.

  The interior of a multi-line statement is not ours to reflow, and this used to
  reflow it. A statement spans lines two ways: a nested function expression, which
  emit-fn has already indented relative to its own start, and a js* template
  holding a JavaScript literal that spans lines. Rewriting the second CHANGES WHAT
  IT MEANS - `a<newline>b` is a template literal whose value holds no spaces, and
  indenting its inner line put two there; a string continued with a trailing
  backslash goes the same way. Both were silent wrong answers.

  So indentation stops at the first newline. It costs a nested function two spaces
  of alignment, and it makes emission incapable of altering what the code means."
  [lines]
  (mapv #(str "  " %) lines))

(declare emit)

(defn- in-order
  "Statements for `results` that preserve Clojure's left-to-right evaluation, and
  the expressions to build the enclosing node from.

  The care is needed because statements and expressions travel separately. Hoisting
  every sibling's statements above the whole expression - which is what this used
  to do - runs a later sibling's statements BEFORE an earlier sibling's expression:

      (f (js* \"g()\") (let* [y (js* \"h()\")] y))
        let y__1 = h();          <- h before g. Wrong.
        f(g(), y__1);

  So as soon as any later sibling contributes statements, an earlier sibling whose
  value is not already stable is spilled into a temporary, pinning it in place.

  `spill-all?` spills every sibling regardless, stable ones included. recur needs
  it rebinds simultaneously, so (recur b a) must not read a b that the rebinding of
  a has already overwritten."
  ([results] (in-order results false))
  ([results spill-all?]
   (let [v (vec results)]
     (loop [i 0, stmts [], exprs []]
       (if (= i (count v))
         {:stmts stmts :exprs exprs}
         (let [{:keys [expr stable?] :as r} (nth v i)
               later-stmts? (some #(seq (:stmts %)) (subvec v (inc i)))
               stmts        (into stmts (:stmts r))]
           (if (or spill-all? (and later-stmts? (not stable?)))
             (let [t (names/temp-name)]
               (recur (inc i) (conj stmts (str "let " t " = " expr ";")) (conj exprs t)))
             (recur (inc i) stmts (conj exprs expr)))))))))


;; --- the collection literals -------------------------------------------------

(defn- const-vals
  "The values behind `nodes` when every one of them is a constant, else nil.

  A :quote is unwrapped, because 'a and :a are equally constant and the node
  shapes differ only in which one the reader wrote."
  [nodes]
  (let [ns (map #(if (= :quote (:op %)) (:expr %) %) nodes)]
    (when (every? #(= :const (:op %)) ns)
      (map :val ns))))

(defn- distinct-consts?
  "Whether `nodes` are constants known to be distinct as JavaScript values.

  False when they are not all constants, and that is the answer rather than a
  refusal to look: {a 1 b 2} may have one key or two depending on what a and b
  evaluate to, and only assoc can decide at run time."
  [nodes]
  (boolean (some-> (const-vals nodes) all-distinct?)))

(defn- emit-items
  "The shared shape of every collection literal: elements evaluated left to right,
  then `f` applied to their expressions.

  args-result's argument, one level down - the same in-order spilling, the same
  short-circuit when an element never returns, so ([1 (throw e)] emits the throw
  and stops. What it adds is the no-effect rule, which is exact here: allocating
  a collection does nothing observable, so a literal has an effect precisely when
  one of its elements does, and [1 2] as a statement is a dead line."
  [nodes f]
  (let [rs (mapv emit nodes)]
    (or (short-circuit rs)
        (let [{:keys [stmts exprs]} (in-order rs)]
          (cond-> (->result stmts (f exprs))
            (every? :no-effect? rs) no-effect)))))

(defn- emit-with-meta
  "(with-meta value m) for a literal that was written with metadata.

  in-order, and it matters: the metadata is a map literal whose values are
  expressions, so `^{:a (f)} [(g)]` has to call g before f. Evaluating the
  collection first and the metadata second is Clojure's order and the order the
  analyzer built the node in.

  no-effect when both halves are, for emit-items' reason: with-meta allocates and
  nothing else observes it."
  [{:keys [expr meta]}]
  (let [rs [(emit expr) (emit meta)]]
    (or (short-circuit rs)
        (let [{:keys [stmts exprs]} (in-order rs)]
          (cond-> (->result stmts
                            (str (core-name 'with-meta) ".call(null, "
                                 (comma exprs) ")"))
            (every? :no-effect? rs) no-effect)))))

(defn- emit-vector [{:keys [items]}]
  (emit-items items vector-js))

(defn- emit-set [{:keys [items]}]
  (emit-items items #(set-js % (distinct-consts? items))))

(defn- emit-map [{ks :keys vs :vals}]
  ;; interleaved, because that is Clojure's evaluation order for {k1 v1 k2 v2} -
  ;; and in-order's whole job is to keep it. Taken apart again afterwards, since
  ;; a hash map wants the two arrays separately.
  (emit-items (interleave ks vs)
              (fn [exprs]
                (map-js (take-nth 2 exprs) (take-nth 2 (rest exprs))
                        (distinct-consts? ks)))))

(defn- emit-js-array [{:keys [items]}]
  (emit-items items js-array-js))

(defn- emit-js-object [{ks :keys vs :vals}]
  ;; the keys are property names rather than nodes (see analyze-js-value), so
  ;; only the values are emitted and only they can contribute statements
  (emit-items vs #(js-object-js ks %)))

(defn- emit-do [{:keys [statements ret]}]
  (let [rs   (mapv emit statements)
        ;; everything after a terminal statement is unreachable
        kept (vec (take-while (complement :terminal?) rs))
        cut  (first (drop (count kept) rs))
        head (into [] (mapcat effect-stmts) kept)]
    (if cut
      (terminal (->result (into head (:stmts cut)) nil))
      (let [r (emit ret)]
        ;; a do's value IS its ret's value, so it is dead as a statement exactly
        ;; when the ret is - otherwise (do (def x 1)) emits the assignment and
        ;; then a bare app$core$ns.x; on the next line
        (cond-> (->result (into head (:stmts r)) (:expr r))
          (:no-effect? r) no-effect
          (:terminal? r) terminal)))))

(defn- emit-bindings
  "The bindings of a let* or loop*, in order: each is one statement, and each init
  may need statements of its own first. Stops at an init that never returns -
  nothing after it, the body included, can run.

  `names-of` says what each binding is spelled as. It is :js-name for a let*, and
  for a loop* that is recurred to it is the CARRIER - see emit-loop.

  `alias?` is for that second case only, and it is not cosmetic. LOOP BINDINGS ARE
  SEQUENTIAL, exactly as a let's are: (loop [strs strs, one? (= 1 (count strs))]
  ...) binds one? from the LOOP's strs, not from whatever strs meant outside. The
  analyzer resolves it that way and emits the binding's own name for it - but a
  recurring loop's inits are computed into carriers, and the own name is only
  declared inside the while, so the reference was to a variable that did not exist
  yet. cljs/pprint.cljc has one and it cost every cl-format directive that pads
  (`ReferenceError: strs__2222 is not defined`, 18 of pprint-test's assertions).
  So each binding is followed by its own name, declared from the carrier, and a
  later init reads it.

  The line is skipped for the LAST binding, which nothing after it can read, and
  the ones it does emit are shadowed inside the loop by fresh-bindings - a
  different variable per iteration, which is the whole point of carriers!."
  ([bindings] (emit-bindings bindings (mapv :js-name bindings) false))
  ([bindings names-of] (emit-bindings bindings names-of false))
  ([bindings names-of alias?]
   (loop [bs (seq bindings), ns (seq names-of), stmts []]
     (if-let [b (first bs)]
       (let [{:keys [expr terminal?] :as r} (emit (:init b))
             stmts (into stmts (:stmts r))]
         (if terminal?
           {:stmts stmts :terminal? true}
           (recur (next bs) (next ns)
                  (cond-> (conj stmts (sm/fill (node-pos (:init b))
                                               (str "let " (first ns) " = " expr ";")))
                    (and alias? (next bs))
                    (conj (str "let " (:js-name b) " = " (first ns) ";"))))))
       {:stmts stmts}))))

(defn- emit-let [{:keys [bindings body]}]
  (let [{:keys [stmts terminal?]} (emit-bindings bindings)]
    (if terminal?
      (terminal (->result stmts nil))
      ;; No wrapper: a let's value is its body's value, and the bindings are just
      ;; statements that have to run first.
      (let [r (emit body)]
        (cond-> (->result (into stmts (:stmts r)) (:expr r))
          (:no-effect? r) no-effect
          (:terminal? r) terminal)))))

(defn- boolean-tagged?
  "Does this node's tag say its value is already a JavaScript boolean?

  ^boolean is an ASSERTION BY THE PROGRAM, not something inferred: cljs.core writes
  it on 86 predicates and cljs/binding_test.cljs writes it on a dynamic var, and
  taking it at its word is what ClojureScript does (compiler.cljc's safe-test?,
  which also accepts a `seq` tag its infer-tag produces and we cannot).

  It matters because truth_ and JavaScript are not the same question: truth_(x) is
  x != null && x !== false, so \"\" and 0 are true, while `if (x)` makes both false.
  A wrong tag is therefore a wrong answer, which is why nothing here guesses one."
  [node]
  (= 'boolean (:tag node)))

(defn- emit-if*
  "The three shapes an if takes once its test is known to return: two jumps, two
  pure expressions, or a temporary."
  [t th el]
  (let [cond-expr (if (:boolean? t) (:expr t) (str "truth_(" (:expr t) ")"))]
    (cond
      ;; both branches jump: nothing to assign, and nothing follows the if
      (and (:terminal? th) (:terminal? el))
      (terminal
       (->result (-> (vec (:stmts t))
                     (conj (str "if (" cond-expr ") {"))
                     (into (indent (:stmts th)))
                     (conj "} else {")
                     (into (indent (:stmts el)))
                     (conj "}"))
                 nil))

      ;; both branches are pure expressions - no temporary needed
      (and (empty? (:stmts th)) (empty? (:stmts el))
           (not (:terminal? th)) (not (:terminal? el)))
      (->result (:stmts t)
                (str "(" cond-expr " ? " (:expr th) " : " (:expr el) ")"))

      :else
      (let [v      (names/temp-name)
            branch (fn [r] (cond-> (vec (:stmts r))
                             (not (:terminal? r)) (conj (str v " = " (:expr r) ";"))))]
        (->result
         (-> (vec (:stmts t))
             (conj (str "let " v ";"))
             (conj (str "if (" cond-expr ") {"))
             (into (indent (branch th)))
             (conj "} else {")
             (into (indent (branch el)))
             (conj "}"))
         v)))))

(defn- emit-if [{:keys [test then else]}]
  (let [t (cond-> (emit test)
            (boolean-tagged? test) (assoc :boolean? true))]
    (or (short-circuit [t])
        (emit-if* t (emit then) (emit else)))))

(defn- emit-try
  "try, with a temporary for the value - the fourth place, after if, case and throw,
  where ClojureScript needs an immediately-invoked function and we do not.

  AND HERE THE WRAPPER IS NOT MERELY UNTIDY, IT IS WRONG. A function wrapper is a
  function boundary, and `await` is a syntax error inside one that is not itself
  async - so a try whose body awaits, which is legal in an evaluation unit that is
  itself an async IIFE (doc/cljs-repl.md 5), becomes uncompilable the moment a
  second, ordinary wrapper goes round it. Destination-driven emission has no wrapper to
  introduce: the value is assigned to a temporary inside the try and read after it,
  and the destination is applied to that.

  (try x) with neither catch nor finally is (do x), and emits as one."
  [{:keys [body binding catch finally]}]
  (let [b (emit body)
        c (when catch (emit catch))
        f (when finally (emit finally))]
    (if (and (nil? c) (nil? f))
      b
      ;; nothing after the statement can run when the body never returns and either
      ;; there is no catch or the catch does not return either
      (let [dead? (and (:terminal? b) (or (nil? c) (:terminal? c)))
            v     (when-not dead? (names/temp-name))
            arm   (fn [r] (cond-> (vec (:stmts r))
                            (and v (not (:terminal? r))) (conj (str v " = " (:expr r) ";"))))
            lines (cond-> (if v [(str "let " v ";")] [])
                    :always (-> (conj "try {")
                                (into (indent (arm b)))
                                (conj "}"))
                    c       (-> (conj (str "catch (" (:js-name binding) ") {"))
                                (into (indent (arm c)))
                                (conj "}"))
                    ;; a finally's value is discarded, so it is emitted purely for
                    ;; whatever it does
                    f       (-> (conj "finally {")
                                (into (indent (effect-stmts f)))
                                (conj "}")))]
        (cond-> (->result lines v)
          dead? terminal)))))

(defn- emit-case
  "switch, with a temporary for the value - the third place after if and throw
  where ClojureScript needs an immediately-invoked function and we do not.

  Each clause is braced, and a clause that jumps - recur, throw - emits no break:
  a break inside a switch leaves the switch, which for a recur would be exactly
  wrong, since the continue it already emitted is meant for the enclosing loop."
  [{:keys [test nodes default]}]
  (let [t (emit test)]
    (or (short-circuit [t])
        (let [clauses (mapv (fn [n] [(mapv #(:expr (emit (:test %))) (:tests n))
                                     (emit (:then (:then n)))])
                            nodes)
              dr      (emit default)
              rs      (conj (mapv second clauses) dr)
              all-jump? (every? :terminal? rs)
              v       (when-not all-jump? (names/temp-name))
              ;; v is nil only when every branch jumps, and then this arm of the
              ;; cond-> is never taken
              branch  (fn [r] (cond-> (vec (:stmts r))
                                (not (:terminal? r))
                                (into [(str v " = " (:expr r) ";") "break;"])))
              clause  (fn [labels r]
                        (-> (mapv #(str "case " % ":") labels)
                            (update (dec (count labels)) str " {")
                            (into (indent (branch r)))
                            (conj "}")))
              body    (-> [(str "switch (" (:expr t) ") {")]
                          (into (mapcat (fn [[labels r]] (clause labels r))) clauses)
                          (conj "default: {")
                          (into (indent (branch dr)))
                          (conj "}")
                          (conj "}"))
              stmts   (cond-> (vec (:stmts t))
                        v (conj (str "let " v ";"))
                        :always (into body))]
          (if all-jump?
            (terminal (->result stmts nil))
            (->result stmts v))))))

(defn- emit-body
  "A function body: its statements, then `return <expr>;`. This is the other
  destination besides an expression - and, with emit-top, the only other one."
  [node]
  (let [{:keys [stmts expr terminal?]} (emit node)]
    (cond-> (vec stmts)
      (not terminal?) (conj (sm/fill (node-pos node) (str "return " expr ";"))))))

(defn- carriers!
  "Allocate the names a recur assigns to, and leave them on `frame` for the
  emit-jump that will read them.

  A RECUR MUST NOT ASSIGN THE NAME THE BODY READS, and that is the whole of it. A
  Clojure loop binding is immutable and recur starts a new iteration with new
  values, so a fn made in one iteration keeps that iteration's values; assigning
  the body's own variable makes every such fn see the LAST values instead -
  JavaScript's var-in-a-loop problem, arrived at from Clojure semantics. So the
  loop keeps two names per binding: a carrier, which recur assigns, and the
  binding's own name, re-declared from the carrier at the top of every iteration
  and therefore fresh per iteration.

  ClojureScript answers the same question differently, by wrapping every fn made
  inside a loop in an IIFE that takes the loop locals as parameters
  (cljs/compiler.cljc:1043). That is a fix at each closure rather than at the
  loop, which costs an allocation per closure per iteration and needs the analyzer
  to tell the emitter which enclosing bindings are loop locals. This costs one
  `let` per binding per iteration, which an engine elides when nothing captures it.

  temp-name and not a new shape: its docstring already names a recur's rebinding
  as one of the three things it is for (doc/cljs-compiler.md §5.3)."
  [frame params]
  (reset! (:carriers frame) (mapv (fn [_] (names/temp-name)) params)))

(defn- fresh-bindings
  "The line that opens every iteration: the body's own names, re-declared from the
  carriers. See carriers!."
  [params carriers]
  (when (seq params)
    [(str "let " (sm/join ", " (map (fn [b c] (str (:js-name b) " = " c))
                                    params carriers))
          ";")]))

(defn- bind-params
  "Statements binding a method's parameters out of `arguments`, used when several
  arities share one JavaScript function. `from` is the first index to take.

  `names-of` says what each is spelled as - the parameter's own name, or, for a
  method that recurs, its carrier (see carriers!)."
  [params from names-of]
  (into []
        (map-indexed (fn [i n] (str "let " n " = arguments[" (+ from i) "];")))
        (subvec (vec names-of) from)))

(defn- rest-param
  "The variadic parameter, bound to the arguments past the fixed ones: nil when
  there are none, and a cljs.core/IndexedSeq over them when there are.

  A SEQ, not an array, and that is the whole of what a rest argument is in
  ClojureScript - (fn [& xs] (first xs)) has to work, and so does destructuring a
  rest argument, which is what {:keys [a b]} after an & really is. This emitted a
  plain array until M6, and its docstring said so and said it was provisional
  until the core library arrived; the core library arrived at M5 and nothing came
  back here. Nothing could catch it either: with no cljs.core there was no seq to
  build, so every test written before M5 was written to expect the array.
  ClojureScript's own destructuring-test is what noticed (§5.14).

  Constructed directly rather than through cljs.core/array-seq, which is
  cljs.compiler's choice too (compiler.cljc:1010) and for a good reason: this is
  the entry to every variadic call in a program, so it should not itself be one.

  NIL AND NOT AN EMPTY SEQ when nothing was passed, which is Clojure's answer as
  well - ((fn [& xs] xs)) is nil - and the reason the assignment needs a
  conditional rather than being one expression."
  [js-name fixed-arity]
  [(str "let " js-name " = null;")
   (str "if (arguments.length > " fixed-arity ") {")
   (str "  " js-name " = (new " (core-name 'IndexedSeq)
        "(Array.prototype.slice.call(arguments, " fixed-arity "), 0, null));")
   "}"])

(defn- method-names
  "What each of a method's parameters is spelled as where it is BOUND - as a
  formal, or out of `arguments`, or as the rest parameter.

  Its own name when the method does not recur. Its carrier when it does, because
  then the parameter is what recur assigns and the body must read something
  fresher - carriers! has the argument, and it is the same one loop* answers.

  A PROTOCOL METHOD'S FIRST PARAMETER IS EXCEPT: recur does not rebind the object
  the method was called on, so it keeps its own name and needs no carrier. The
  frame says how many leading parameters that is (analyzer/recur-frame)."
  [{:keys [params recurs? frame]}]
  (if recurs?
    (let [k (:offset frame 0)]
      (into (mapv :js-name (subvec params 0 k))
            (carriers! frame (:params frame))))
    (mapv :js-name params)))

(defn- loop-wrap
  "A body that is recurred to, wrapped in the loop its recur jumps to: each
  iteration opens by re-declaring the parameters from their carriers, so a closure
  made in one iteration keeps that iteration's values. See carriers!.

  A body nobody recurs to is returned unchanged, and so is a parameter recur does
  not rebind - a protocol method's object stays a plain formal outside the loop
  (see method-names)."
  [{:keys [recurs? frame]} ns lines]
  (if recurs?
    (let [k (:offset frame 0)]
      (-> ["while (true) {"]
          (into (indent (into (vec (fresh-bindings (:params frame) (subvec (vec ns) k)))
                              lines)))
          (conj "}")))
    lines))

(defn- emit-method-lines
  "The body of one FIXED arity, with its parameters already in scope. `param-from`
  is the first parameter to pull out of `arguments` rather than take as a formal,
  and `ns` the names from method-names - passed in rather than computed here
  because emit-fn needs the same ones for the formal list, and carriers!
  allocates.

  Fixed only: a variadic arity's body is emitted by emit-fn, into a property
  rather than into the function, and does not come through here."
  [method param-from ns]
  (-> (bind-params (:params method) param-from ns)
      (into (loop-wrap method ns (emit-body (:body method))))))

(def ^:private variadic-prop
  "The property a variadic function's BODY hangs on, taking the rest argument as an
  ordinary parameter that is already a seq.

  ClojureScript's spelling, and deliberately so: cljs.core's own defn macro builds
  this same property by hand for a variadic defn (core.cljc:3298), so a defn and a
  fn* have to mean the same thing by it or apply would work on one and not the
  other."
  "cljs$core$IFn$_invoke$arity$variadic")

(defn- variadic-shim
  "The lines of a variadic function's ENTRY POINT: gather the arguments past the
  fixed ones into a seq and hand the lot to `delegate`, which is where the body
  lives.

  Positional - arguments[0], not a named formal - because the entry point does
  nothing with the fixed arguments except pass them along, and naming them here
  would be a second binding of names that already name the body's parameters.

  THE DELEGATE IS A LOCAL, not the property it is also assigned to, and the
  difference is what §5.35 is about: variadic-prop is a REPLACEABLE entry point -
  cljs.spec.test.alpha's instrument overwrites it on purpose - and a function whose
  own dispatcher read it there would have its body replaced rather than its callers
  redirected. ClojureScript calls a closed-over `__delegate` here for the same
  reason (compiler.cljc:1012)."
  [delegate fixed-arity]
  (let [t (names/temp-name)]
    (conj (vec (rest-param t fixed-arity))
          (str "return " delegate ".call("
               (comma (into ["this"]
                            (conj (mapv #(str "arguments[" % "]") (range fixed-arity)) t)))
               ");"))))

(defn- apply-to-lines
  "`cljs$lang$applyTo`: invoke the function on a SEQ of arguments, peeling the
  fixed ones off the front and handing what is left along as it stands.

  THE SEQ IS NEVER REALIZED, and that is the whole point of the property existing.
  Without it cljs.core/apply falls back to apply-to-simple, which walks the
  argument sequence to the end to build an argument array, so
  (apply (fn [& xs] ...) (iterate inc 0)) exhausts the heap instead of returning.
  With it, apply counts only as far as cljs$lang$maxFixedArity (through
  bounded-count) and then hands the unrealized seq here, where it becomes the rest
  parameter unchanged. ClojureScript emits the same two properties for the same
  reason (compiler.cljc:1112).

  `seq` when nothing is peeled off, because then the argument arrives as apply
  received it and may be any collection; after a `next` it is already a seq or
  nil. That is cljs.core's own case split too (core.cljc:3286).

  Closes over the delegate rather than reading `this`, which is what ClojureScript
  does instead (it emits `var self__ = this` under a @this annotation). Both are
  right when the property is called as a method, which is the only way
  cljs.core/apply calls it; this one is also right when it is not - and it reaches
  the body through the same local the entry point does, for the reason
  variadic-shim gives."
  [delegate self fixed-arity]
  (let [s  (names/temp-name)
        as (mapv (fn [_] (names/temp-name)) (range fixed-arity))
        rest-arg (if (zero? fixed-arity) (str (core-name 'seq) ".call(null, " s ")") s)]
    (-> [(str self ".cljs$lang$applyTo = (function (" s ") {")]
        (into (indent
               (-> (into [] (mapcat (fn [a]
                                      [(str "let " a " = " (core-name 'first) ".call(null, " s ");")
                                       (str s " = " (core-name 'next) ".call(null, " s ");")]))
                         as)
                   (conj (str "return " delegate ".call("
                              (comma (into ["this"] (conj as rest-arg))) ");")))))
        (conj "});"))))

(defn- emit-fn
  "A function.

  A VARIADIC one is not a single expression, and that is the only real complexity
  here. Its body has to be reachable with the rest argument ALREADY A SEQ, so that
  cljs$lang$applyTo can hand one over without realizing it (see apply-to-lines);
  so the body moves to variadic-prop and the function itself becomes an entry
  point that gathers `arguments` and delegates. Properties are assigned by
  statements, so the result carries statements and its expression is the name they
  were assigned through - the function's own local name when it has one, so that a
  self-recursive variadic fn can still see itself from the body's new home, and a
  temporary otherwise.

  This is one call deeper on every variadic invocation than the body being the
  function. ClojureScript pays the same call for the same reason.

  A fn that is not variadic is untouched by any of it: one expression, no
  properties, as before.

  ^:ASYNC IS ONE KEYWORD HERE and nothing else, which is what the destination-driven
  emitter buys. `await` is legal anywhere lexically inside an async function, and
  this emitter never puts a function boundary where the source had none: a let, a
  loop, a case or a try in expression position becomes STATEMENTS in the enclosing
  function plus an expression (see the namespace docstring), so an await nested in
  one is still an await in this function's body.

  ClojureScript has to work for it. Every such form there is an IIFE, so an async
  fn's IIFEs all become `(await (async function (){...})())` - iife-open and
  iife-close read (:async env) for exactly that - and the await propagates outward
  through each wrapper. cljs/async_await_test.cljs is largely a list of the places
  that has to hold: a case inside a case, a throw inside a throw, a finally, a
  letfn inside a letfn. Here they are the same code they would be without the
  keyword.

  Both halves of a variadic fn are marked, as ClojureScript marks them: the entry
  point returns what the delegate returned, so if only the delegate were async the
  caller would still get the promise - but cljs$lang$applyTo would hand back a
  promise from a function nothing declared to make one, and `await` on the result
  of apply is what variadic-defn-test asks for."
  [{:keys [methods variadic? local async? method-target?]}]
  (let [self    (when variadic? (or (:js-name local) (names/temp-name)))
        ;; where the body actually lives. The property below is assigned FROM it
        ;; rather than being it, so that replacing the property redirects callers
        ;; without rewriting this function - see variadic-shim (§5.35).
        deleg   (when variadic? (names/temp-name))
        a       (if async? "async " "")
        ;; the arity a CALLER wrote, which is one fewer than the arguments this
        ;; function got when the first of them is the object it was called on.
        ;; ({} 1 2 3) is PersistentArrayMap.prototype.call(map, 1, 2, 3), and
        ;; cljs/core_test.cljs asks for the message to say 3. Same expression
        ;; cljs.compiler emits (compiler.cljc:1096).
        arity-js (if method-target? "(arguments.length - 1)" "arguments.length")
        nm      (if local (str " " (:js-name local)) "")
        ;; ONCE per method, because carriers! allocates: the formal list below and
        ;; the body have to agree about what each parameter is called
        named   (into {} (map (fn [m] [m (method-names m)])) methods)
        single? (= 1 (count methods))
        lines-of (fn [m]
                   (if (:variadic? m)
                     (variadic-shim deleg (:fixed-arity m))
                     (emit-method-lines m (if single? (count (:params m)) 0) (get named m))))
        expr
        (if single?
          ;; one arity: the parameters are real formals, so the function reads as
          ;; one - unless it is the variadic arity, whose entry point takes none
          (let [m (first methods)]
            (str "(" a "function" nm "(" (comma (if (:variadic? m) [] (get named m))) ") {\n"
                 (sm/join "\n" (indent (lines-of m)))
                 "\n})"))
          ;; several arities dispatch on arguments.length; every parameter comes out
          ;; of `arguments`, so the arities cannot disagree about formals
          (let [fixed (remove :variadic? methods)
                var-m (first (filter :variadic? methods))]
            (str "(" a "function" nm "() {\n"
                 (sm/join
                  "\n"
                  (indent
                   (-> ["switch (arguments.length) {"]
                       (into (mapcat (fn [m]
                                       (-> [(str "case " (:fixed-arity m) ": {")]
                                           (into (indent (lines-of m)))
                                           (conj "}"))))
                             fixed)
                       (into (when var-m
                               (-> [(str "default: if (arguments.length >= " (:fixed-arity var-m) ") {")]
                                   (into (indent (lines-of var-m)))
                                   (conj "}"))))
                       (conj "}")
                       (conj (str "throw new Error(\"Invalid arity: \" + " arity-js ");")))))
                 "\n})")))]
    (if-not variadic?
      (->result [] expr)
      (let [var-m (first (filter :variadic? methods))
            fa    (:fixed-arity var-m)
            ns    (get named var-m)]
        (-> (->result
             (-> [(str "let " self " = " expr ";")
                  (str "let " deleg " = (" a "function (" (comma ns) ") {")]
                 (into (indent (loop-wrap var-m ns (emit-body (:body var-m)))))
                 (conj "});")
                 ;; the entry point for a caller that already knows the arity -
                 ;; and the one this function does NOT read to find its own body
                 (conj (str self "." variadic-prop " = " deleg ";"))
                 (conj (str self ".cljs$lang$maxFixedArity = " fa ";"))
                 (into (apply-to-lines deleg self fa)))
             self)
            ;; the expression is a local now, not a function expression: reading it
            ;; later yields the same object, and reading it and dropping the value
            ;; does nothing
            stable
            no-effect)))))

(defn- emit-jump
  "Rebind the recur point's bindings and jump.

  The CARRIERS are assigned, not the names the body reads - carriers! has why.

  With more than one binding the new values go through temporaries first, because
  recur rebinds simultaneously: (recur b a) must not assign a from an already
  overwritten b. A single binding cannot alias itself, so it assigns directly."
  [rs frame]
  (let [names @(:carriers frame)
        ;; spill-all? with more than one binding: that IS the simultaneity, and it
        ;; gets left-to-right evaluation at the same time
        {:keys [stmts exprs]} (in-order rs (> (count rs) 1))]
    (terminal
     (->result (-> stmts
                   (into (map (fn [n e] (str n " = " e ";")) names exprs))
                   (conj "continue;"))
               nil))))

(defn- emit-recur
  "A recur.

  `:target` is the object a recur inside a protocol method named when it did not
  have to (analyzer/parse-recur): it is evaluated first, where it was written, and
  its value is dropped. Nothing else about the jump changes."
  [{:keys [exprs frame target]}]
  (let [t  (when target (emit target))
        rs (mapv emit exprs)]
    (or (short-circuit (cond->> rs t (cons t)))
        (let [j (emit-jump rs frame)]
          (cond-> j
            t (assoc :stmts (into (vec (effect-stmts t)) (:stmts j))))))))

(defn- emit-loop
  "Bindings, then `while (true) { ... }`. No function wrapper: ClojureScript needs
  one because a loop in expression position must return a value, and we have a
  temporary for that instead.

  A loop nobody recurs to is a let, and is emitted as one - and it keeps the
  binding's own name, because with no recur there is nothing to assign it and so
  nothing to make it stale.

  One that IS recurred to binds the carriers instead, and re-declares the body's
  names from them at the top of every iteration. carriers! has why."
  [{:keys [bindings body recurs? frame]}]
  (let [cs (when recurs? (carriers! frame bindings))
        {:keys [stmts terminal?]} (if recurs?
                                    (emit-bindings bindings cs true)
                                    (emit-bindings bindings))]
    (if terminal?
      (terminal (->result stmts nil))
      (let [r (emit body)]
        (if-not recurs?
          (cond-> (->result (into stmts (:stmts r)) (:expr r))
            (:no-effect? r) no-effect
            (:terminal? r) terminal)
          (let [v (names/temp-name)]
            (->result
             (-> stmts
                 (conj (str "let " v ";"))
                 (conj "while (true) {")
                 (into (indent (-> (vec (fresh-bindings bindings cs))
                                   (into (:stmts r))
                                   (cond-> (not (:terminal? r))
                                     (into [(str v " = " (:expr r) ";")
                                            "break;"])))))
                 (conj "}"))
             v)))))))

(defn- emit-ns
  "The ns form emits one line: the loaded mark.

  Set by the body rather than inferred from the registry, and that distinction is
  the whole of doc/cljs-repl.md 7.2 - $ns creates a namespace object on demand, so
  an object exists as soon as anything REFERENCES the namespace, which is exactly
  the case require exists to catch. Testing for the object would say yes there.

  Marked here, at the ns form, rather than at the end of the body: in a REPL the
  body is however many forms get typed next, and from the moment (ns app.core ...)
  is evaluated, another namespace requiring app.core must not fetch the file it was
  last written from.

  A module gets the mark in the same place - first line of its body rather than
  last, where doc/cljs-repl.md 7.1 draws it - and the one consequence is narrow and
  known: a module that throws part way through leaves a mark saying it is loaded.
  Nothing that could act on that survives it, because the module that imported it
  threw too; a REPL attached afterwards would see a half-defined namespace, and
  its way out is R1's :reload, which refetches whatever the mark says."
  [{:keys [name]}]
  (->result [(str "$CLJS.loaded.add(\"" name "\");")] "null"))

(defn- def-name
  "The JavaScript for a var: a PROPERTY of its namespace object, app$core.answer,
  not a module-scoped variable (doc/cljs-repl.md \u00a73.1).

  This is the decision that makes a REPL possible at all. A module's own
  `var`/`let`/`const` cannot be reached from outside it, and an imported binding is
  read-only by the module system's own rule - so with a module-scoped variable
  nothing evaluated later could ever redefine a var, reload a namespace, or set! a
  var in another namespace. A property has none of those restrictions: assigning it
  is an ordinary assignment, and every reference already resolves at call time, so
  code loaded earlier sees the new definition.

  It costs a property lookup per reference at :optimizations :none, which is the
  only output this compiler produces, and it closes the door on :advanced renaming
  - already closed by dropping goog.provide, and out of scope either way."
  [qsym]
  (str (names/ns-alias (namespace qsym)) "." (names/munge (name qsym))))

(defn- emit-def
  "An assignment to a property of the namespace object.

  There is nothing to declare and so nothing to hoist, which is why (def x 1)
  works at any depth: inside a function body the assignment simply happens when
  the function runs, and the property exists from then on.

  (def x) with no init emits nothing at all. It must not assign - `(declare x)`
  expands to it, and on a reload an assignment would wipe the definition the
  declaration is only promising.

  A :test rides along as a second assignment, onto the VALUE rather than the var:
  `foo.cljs$lang$test = function(){...}`. cljs.test's deftest is what puts it
  there and cljs.test/test-var is what reads it back, and it hangs off the value
  because that is where a Var taken later finds it (see parse-var's metadata map).
  Emitted after the init and never instead of it."
  [{:keys [name init test]}]
  (let [js (def-name name)
        r  (when init (emit init))
        t  (when test (emit test))]
    (cond
      (:terminal? r) (terminal (->result (:stmts r) nil))
      init           (->result (cond-> (conj (vec (:stmts r)) (str js " = " (:expr r) ";"))
                                 t (into (conj (vec (:stmts t))
                                               (str js ".cljs$lang$test = " (:expr t) ";"))))
                               js)
      :else          (->result [] js))))

(defn- emit-deftype
  "A constructor assigned to a var, and then the body that installs whatever the
  type implements.

  There is very little here, and that is the design rather than an omission: this
  emitter knows nothing about protocols. Everything the calling convention consists
  of - the marker property, the method properties, the dispatch chain - is written
  by the macros in terms of set!, fn* and js*, over names clojure.cljs.names
  computes. See doc/cljs-compiler.md §5.4.

  The field parameters are ordinary locals and the properties they are stored in
  are spelled the host's way, because (.-x p) has to reach them from anywhere.

  The function carries its own name so that a stack trace, and node printing an
  instance, say Point$fn rather than <anonymous>: a function assigned to a PROPERTY
  infers no name in JavaScript, unlike one assigned to a variable.

  The $fn is the fn self-name shape, and a bare Point would in fact be safe here -
  a constructor body is generated, holds nothing but parameter reads, and so has
  nothing for the name to shadow. It keeps the suffix anyway, because the shapes
  are what let this compiler have no reserved-word list at all (clojure.cljs.names):
  a bare name we own would bring one back for (deftype delete [...]) alone."
  [{:keys [fields body] qname :name}]
  (let [js    (def-name qname)
        ctor  (-> [(str js " = (function " (names/fn-self-name (name qname)) "("
                       (sm/join ", " (map :js-name fields)) ") {")]
                  (into (indent (map (fn [{:keys [field js-name]}]
                                       (str "this." field " = " js-name ";"))
                                     fields)))
                  (conj "});"))
        r     (when body (emit body))]
    (cond-> (->result (into ctor (if r (effect-stmts r) [])) js)
      (:terminal? r) terminal)))

(defn- goog-var-name
  "The JavaScript for a goog var: a property of its namespace object, exactly like
  a ClojureScript var - goog$object$ns.get - and reached the same way, because
  base.js registers each provide into $CLJS.namespaces so $ns(\"goog.object\") IS
  goog.object (doc/cljs-compiler.md §5.5).

  The one difference from def-name is the spelling after the dot. A ClojureScript
  var is munged, because we own the name; a goog var is not, because goog owns it
  and it is already a JavaScript name. §5.3 is the rule, and js-global below is the
  other side of it.

  The analyzer has already refused anything that would not be a name here."
  [qsym]
  (str (names/ns-alias (namespace qsym)) "." (names/host-name (name qsym))))

(defn- js-module-var-name
  "The JavaScript for a name drawn out of a JavaScript module: a property of the
  object the import bound - react$js.useState.

  The same three-part rule as goog-var-name, and for the same reasons. The object
  is named by clojure.cljs.names/js-alias rather than ns-alias, because a module is
  reached through an import binding rather than through $ns; the property is spelled
  the HOST's way, because the export is JavaScript's name and not ours (§5.3); and
  the analyzer has already refused anything that would not be a name here.

  `default` needs no case of its own. It is a reserved word and a perfectly good
  property name, so the export :default asks for is read like any other.

  Neither does a DOTTED export, which is what the $ sugar in a specifier produces:
  [\"date-fns/sub$default\" :as sub] gives the export path `default`, and host-name
  leaves the dots between segments alone because a dot is not a character it
  maps. One property read or three is a difference JavaScript makes and this does
  not."
  [specifier export]
  (str (names/js-alias specifier) "." (names/host-name export)))

(defn- js-global
  "The JavaScript name of a js/foo reference.

  Spelled the host's way, because js/foo names something that already exists in
  JavaScript: js/foo-bar is the global foo_bar, exactly as in ClojureScript. The
  one exception is js/-Infinity, whose leading minus is part of the name and which
  ClojureScript special-cases here too - munging it would give _Infinity, which is
  a different global and does not exist.

  The analyzer has already refused anything that would not be a name here."
  [qsym]
  (if (= 'js/-Infinity qsym)
    "-Infinity"
    (names/host-name (name qsym))))

(defn- args-result
  "The shape shared by every node that combines a head expression with argument
  expressions - invoke, the two host forms, new, set!. `f` builds the expression
  from the parts. Short-circuits if one of them never returns, and evaluates them
  left to right (see in-order)."
  [head-result arg-results f]
  (or (short-circuit (cons head-result arg-results))
      (let [{:keys [stmts exprs]} (in-order (cons head-result arg-results))]
        (->result stmts (f (first exprs) (rest exprs))))))

(defn- emit-host-field [{:keys [target field]}]
  (args-result (emit target) [] (fn [t _] (str t "." (names/host-name field)))))

(defn- emit-host-call [{:keys [target method args]}]
  (args-result (emit target) (mapv emit args)
               (fn [t as] (str t "." (names/host-name method)
                               "(" (sm/join ", " as) ")"))))

(defn- emit-new [{:keys [args] :as node}]
  ;; parenthesised: `new Foo()` binds looser than the member access or call that
  ;; may enclose it, and (new Foo()).bar is what is meant.
  (args-result (emit (:class node)) (mapv emit args)
               (fn [c as] (str "(new " c "(" (sm/join ", " as) "))"))))

(defn- emit-qualified-method
  "String/.toUpperCase, Object/new - a host member as a value.

  A CLOSURE, and the same closure ClojureScript emits (compiler.cljc:1318). Not an
  arrow function and not a bound method: Reflect.apply takes the receiver as an
  ordinary first argument, so (map String/.toUpperCase coll) hands each string to
  a function of one argument, which is what the form is for.

  `new` is Reflect.construct rather than a wrapper doing `new C(...)`, because
  spreading arguments into a constructor has no other spelling.

  The class expression lands INSIDE the closure body, so the type is looked up per
  call - again matching ClojureScript. Any statements computing it are hoisted
  out, which evaluates that part once instead; nothing in the analyzer can produce
  a class node with statements today, and doing the work once is the better of the
  two answers if something ever does.

  no-effect: building a closure is unobservable, so as a statement it is dropped.
  Its statements are not - see effect-stmts."
  [{:keys [class kind method]}]
  (let [r (emit class)]
    (or (short-circuit [r])
        (no-effect
         (->result (:stmts r)
                   (if (= :new kind)
                     (str "(function (...args) { return Reflect.construct("
                          (:expr r) ", args); })")
                     (str "(function (x, ...args) { return Reflect.apply("
                          (:expr r) ".prototype." (names/host-name (name method))
                          ", x, args); })")))))))

(defn- emit-the-var
  "(var foo) - `new cljs.core.Var(function(){return foo;}, sym, meta)`.

  The THUNK is the part worth pointing at: the Var holds a function that reads the
  var rather than the value the var held when the Var was made, so a redefinition
  is visible through a Var taken before it. §5.2 is what makes the thunk a
  one-liner - a var is a property of a namespace object, so reading it late is an
  ordinary property read.

  Not through args-result: the first argument is not an expression to be ordered
  against the others, it is a function body that runs later."
  [{:keys [var sym meta]}]
  (args-result (->result [] (core-name 'Var)) [(emit sym) (emit meta)]
               (fn [c [s m]]
                 (str "(new " c "(function(){return " (:expr (emit var)) ";}, "
                      s ", " m "))"))))

(defn- emit-throw [{:keys [exception]}]
  (let [r (emit exception)]
    (or (short-circuit [r])
        (terminal (->result (conj (vec (:stmts r)) (str "throw " (:expr r) ";"))
                            nil)))))

(defn- emit-set!
  "Parenthesised, because a set! is an expression: JavaScript assignment yields the
  assigned value, which is what ClojureScript's set! returns.

  The target is an LVALUE, and so cannot go through args-result: as soon as the
  value contributed statements, in-order would spill the target into a temporary
  and the assignment would land on the temporary, losing the write entirely. What
  can be ordered against the value is the object a property hangs off - that is an
  ordinary expression - so a property target is taken apart and only its object
  goes through in-order. A var target has nothing to evaluate at all."
  [{:keys [target val]}]
  (let [vr (emit val)]
    (if (= :host-field (:op target))
      (let [obj (emit (:target target))]
        (or (short-circuit [obj vr])
            (let [{:keys [stmts exprs]} (in-order [obj vr])]
              (->result stmts
                        (str "(" (first exprs) "." (names/host-name (:field target))
                             " = " (second exprs) ")")))))
      (or (short-circuit [vr])
          (->result (:stmts vr)
                    (str "(" (:expr (emit target)) " = " (:expr vr) ")"))))))

(defn- js-receiver
  "The object and the property of a dotted js/ name: js/console.log is the property
  log OF console. nil for an undotted name, which has no receiver to keep."
  [qsym]
  (let [js (js-global qsym)
        i  (.lastIndexOf js ".")]
    (when (pos? i) [(subs js 0 i) (subs js (inc i))])))

(defn- arity-target
  "Which of a var's arities answers a call of `argc` arguments, given the shape
  cljs.core's defn recorded on it - or nil, meaning call the function itself.

    n           the fixed arity n, reached as .cljs$core$IFn$_invoke$arity$n
    :variadic   the rest arity, reached as .cljs$core$IFn$_invoke$arity$variadic

  The same three questions cljs.compiler asks (compiler.cljc, emit* :invoke), in
  the same order, because the answer has to agree with what core.cljc EMITS:
  multi-arity-fn sets one property per fixed method and variadic-fn* sets the
  variadic one, and nothing sets a property for a function that has only one
  method - which is why a single-method shape answers nil here rather than
  naming an arity nobody wrote.

  nil is always safe: it is the call this compiler made before there was an
  alternative, and it goes through the dispatch function, which knows every
  arity by construction."
  [{:keys [variadic? max-fixed-arity method-params]} argc]
  (cond
    (and (not variadic?) (= 1 (count method-params))) nil
    (and variadic? (> argc max-fixed-arity))          :variadic
    (some #{argc} (map count method-params))          argc
    ;; a call the shape does not answer - (f) on a two-arity f, or an argc at or
    ;; below max-fixed-arity that no fixed method has. Left to the dispatch
    ;; function, whose job is to throw `Invalid arity` with the name in it.
    :else                                             nil))

(defn- variadic-args
  "The arguments to .cljs$core$IFn$_invoke$arity$variadic: the fixed ones as they
  are, and everything past them as ONE seq - which is what the dispatch function
  would have built out of `arguments`, built here instead because the call site
  already knows how many there are."
  [mfa as]
  (concat (take mfa as)
          [(str (core-name 'array-seq) ".call(null, ["
                (sm/join ", " (drop mfa as)) "], (0))")]))

(defn- emit-invoke
  "A call, whose head is called with NO receiver - f.call(null, ...), which is what
  ClojureScript emits for every call to a ClojureScript function.

  The .call is not ceremony. Emitting f(...) makes the callee's `this` whatever the
  head expression hung off, and a var is a property of its namespace object: (f 1)
  emitted app$core$ns.f(1), so f ran with the namespace object as `this`, and a body
  doing (js* \"this.x = 1\") would have written a var. Worse, it was not even
  consistent - as soon as a later argument contributed statements, in-order spilled
  the head into a temporary and `this` became undefined, so one call meant two
  things depending on a sibling. null in both places is the only spelling that
  survives spilling, which is why matching ClojureScript here also makes us
  self-consistent.

  A js/ head is the exception, and the same exception ClojureScript makes:
  js/console.log names a host METHOD, and a host method's receiver is part of what
  it is - console.log.call(null) is an Illegal invocation in a browser. So a dotted
  js/ name is taken apart and emitted as a call on its object. That spills the
  OBJECT rather than the method, which keeps both the receiver and the order.

  A VAR OF KNOWN SHAPE is the other exception, and the one that is about speed
  rather than correctness. foo.cljs$core$IFn$_invoke$arity$2(a, b) skips the
  dispatch function that would have read `arguments`, switched on its length and
  forwarded - and it is a method call on the function object, so `this` is the
  same object the dispatch function would have passed along. See arity-target for
  which calls qualify and *static-dispatch* for when the question is asked at all."
  [{:keys [args] :as node}]
  (let [head (:fn node)
        rs   (mapv emit args)
        join #(sm/join ", " %)
        arity (when (and *static-dispatch* (:top-fn head))
                (arity-target (:top-fn head) (count args)))]
    (case (:op head)
      :js-var
      (if-let [[obj prop] (js-receiver (:name head))]
        (args-result (->result [] obj) rs
                     (fn [o as] (str o "." prop "(" (join as) ")")))
        (args-result (emit head) rs
                     (fn [f as] (str f "(" (join as) ")"))))

      ;; a goog function is a plain JavaScript function, not one of ours: it has no
      ;; arity dispatch to go through and no reason to be called with a null
      ;; receiver. Emitted as the method call it is - goog$object$ns.get(o, k) -
      ;; which is also what ClojureScript emits, and which spills the OBJECT rather
      ;; than the function if an argument contributes statements, keeping the
      ;; receiver and the order together exactly as the js/ case does.
      :goog-var
      (args-result (->result [] (names/ns-alias (:ns head))) rs
                   (fn [o as] (str o "." (names/host-name (name (:name head)))
                                   "(" (join as) ")")))

      ;; goog.math.Long called as a function. Rare - it is usually `new` - but a
      ;; Closure provide can be a plain function, and it is the host's either way.
      :goog-ns
      (args-result (emit head) rs (fn [f as] (str f "(" (join as) ")")))

      ;; an export of a JavaScript module, called: react$js.useState(x). Emitted as
      ;; the method call it is, for the goog case's reasons and one more of its own -
      ;; a package bundled from CommonJS is a rewritten object literal, and a function
      ;; on it may well read `this`. Nothing is gained by detaching it from its
      ;; module, and correctness can be lost.
      :js-module-var
      (args-result (->result [] (names/js-alias (:specifier head))) rs
                   (fn [o as] (str o "." (names/host-name (:export head))
                                   "(" (join as) ")")))

      ;; the arity property is appended by the COMBINING function, not made part
      ;; of the head expression, for the reason the js/ case above spells out: if
      ;; an argument contributes statements, in-order spills what it is given, and
      ;; what must be spilled is the function - the receiver - not the property
      ;; read off it.
      (cond
        (integer? arity)
        (args-result (emit head) rs
                     (fn [f as] (str f ".cljs$core$IFn$_invoke$arity$" arity
                                     "(" (join as) ")")))

        (= :variadic arity)
        (args-result (emit head) rs
                     (fn [f as]
                       (str f ".cljs$core$IFn$_invoke$arity$variadic("
                            (join (variadic-args (:max-fixed-arity (:top-fn head))
                                                 as))
                            ")")))

        :else
        (args-result (emit head) rs
                     (fn [f as] (str f ".call(" (join (cons "null" as)) ")")))))))

(defn- emit-js [{:keys [segs args]}]
  (let [rs (mapv emit args)]
    (or (short-circuit rs)
        (let [{:keys [stmts exprs]} (in-order rs)]
          (->result stmts
                    (apply str (interleave segs (concat exprs (repeat "")))))))))

(defn- emit*
  "emit, without the position binding it puts round this - see emit below."
  [node]
  (case (:op node)
    ;; stable and no-effect even when it is a whole quoted structure: building one
    ;; allocates, but nothing else holds the result, so evaluating it late or not
    ;; at all is unobservable
    :const (-> (emit-const node) stable no-effect)
    ;; a literal is NOT stable - its elements are expressions, and a var among
    ;; them can be assigned by a later sibling
    ;; metadata written on a literal, which is part of the value (§5.21)
    :with-meta (emit-with-meta node)
    :vector    (emit-vector node)
    :map       (emit-map node)
    :set       (emit-set node)
    :js-array  (emit-js-array node)
    :js-object (emit-js-object node)
    :local (-> (->result [] (:js-name node)) stable no-effect)
    :do    (emit-do node)
    :let   (emit-let node)
    :if    (emit-if node)
    :js    (emit-js node)
    :fn    (emit-fn node)
    :loop  (emit-loop node)
    :recur (emit-recur node)
    :invoke (emit-invoke node)
    ;; (ns ...) does its real work during analysis; what reaches JavaScript is the
    ;; mark that says this namespace is here, so a later require does not fetch a
    ;; stale copy of it from disk over the top
    :ns    (no-effect (emit-ns node))
    :def   (no-effect (emit-def node))
    ;; like a def, its value is the property it just assigned
    :deftype (no-effect (emit-deftype node))
    ;; a var read is dropped as a statement (the namespace object always exists,
    ;; so it cannot throw) but is NOT stable: a later sibling can set! it
    :var   (no-effect (->result [] (def-name (:name node))))
    ;; js/foo is neither: reading it can throw, and it can be assigned
    :js-var (->result [] (js-global (:name node)))
    ;; a goog var is a var - a property of a namespace object - so it is dropped as
    ;; a statement like one. What differs is the SPELLING of the name after the
    ;; dot: goog is the host's, so it is not munged (doc/cljs-compiler.md §5.3)
    :goog-var (no-effect (->result [] (goog-var-name (:name node))))
    ;; goog.math.Long names the class itself, not a var in it: base.js registers a
    ;; provide under its own name as well as under its container's
    :goog-ns  (no-effect (->result [] (names/ns-alias (:name node))))
    ;; a JavaScript module and a name in one. Both are property reads off an object
    ;; the prologue bound, so both are dropped as statements like a var is - the
    ;; import cannot fail here, because a module that would not load threw before
    ;; this body ran at all
    :js-module (no-effect (->result [] (names/js-alias (:specifier node))))
    :js-module-var (no-effect
                    (->result [] (js-module-var-name (:specifier node)
                                                     (:export node))))
    :quote  (emit (:expr node))
    :try    (emit-try node)
    :throw  (emit-throw node)
    :set!   (emit-set! node)
    :host-field (emit-host-field node)
    :host-call  (emit-host-call node)
    :new        (emit-new node)
    :qualified-method (emit-qualified-method node)
    :the-var    (emit-the-var node)
    :case       (emit-case node)
    ;; letfn* differs from let* only in what is in scope while the inits are
    ;; analysed; by emission time the node shapes are identical
    :letfn      (emit-let node)
    (throw (ex-info (str "No emitter for :op " (:op node)) {:node node}))))

(defn emit
  "JavaScript for `node`, as {:stmts [...] :expr \"...\"}.

  Binds *pos* to where this node was written, so every line the node produces and
  nothing deeper claims is attributed to it. Costs a binding per node when
  clojure.cljs.source-info has run and nothing at all when it has not."
  [node]
  (if-let [p (node-pos node)]
    (binding [*pos* p] (emit* node))
    (emit* node)))

;; --- consuming a result ------------------------------------------------------

(defn- ns-binding
  [ns-sym]
  (str "const " (names/ns-alias ns-sym) " = $ns(\"" ns-sym "\");"))

(defn- other-namespaces
  [ns-sym required]
  (sort (disj (set required) ns-sym)))

(def ^:private nameable-namespaces
  "Namespaces every body can name, whatever its ns form says.

  One of them, and it is cljs.core: a vector literal is a call to
  cljs.core/PersistentVector whether or not the file mentions cljs.core, so the
  object holding cljs.core's vars has to be bound wherever a literal can appear -
  which is everywhere (see core-name).

  This is a NAMING statement and not a load-order one, which is why it lives here
  and not in the require list. $ns creates an object on demand, so binding it
  costs a line and cannot fail; what it does not do is make anything load
  cljs.core first. That is the implicit require, and it is still waiting on a
  cljs/core.js to import (doc/cljs-compiler.md §5.7)."
  '#{cljs.core})

(defn fetched-mark
  "The line a MODULE carries and a script does not: this file has been through the
  module system, so the module system will never evaluate it again.

  Set by the module's own body, which is the only complete rule - a module body
  runs if and only if the file was evaluated, whether that was $CLJS.require asking
  for it or another module's static import pulling it in. A runtime function
  marking what it fetched would miss the second, which is most of a cold load."
  [ns-sym]
  (str "$CLJS.fetched.add(\"" ns-sym "\");"))

(defn delete-var
  "The line that removes a var from a namespace object - the runtime half of
  clojure.cljs.repl's remove-var, and the half a whole-file sweep will use too
  (doc/cljs-repl.md 7.3).

  Nothing has to be found out first: delete on an absent property is a no-op, so
  there is no question to ask the runtime and the JVM can decide this alone. That
  is what makes removal shippable at all; what it does NOT supply is the decision
  of WHICH vars to remove, which is why the sweep waits for an analysis model and
  remove-var, being told, does not."
  [ns-sym sym]
  (str "delete " (names/ns-alias ns-sym) "." (names/munge sym) ";"))

(defn ns-prologue
  "The lines a MODULE opens with after its imports: one namespace object per
  namespace its body can name - its own, every namespace it requires, and
  cljs.core (see nameable-namespaces), because a var in any of them is a property
  of one of these objects.

  Idempotent by construction: $ns creates an object once, ever, so re-running a
  body rebinds the same object every existing reference already holds.

  One compilation unit, one namespace. The prologue is computed from the cursor
  AFTER the unit is analysed, so a second (ns ...) in the same unit would leave the
  first one's object unbound - which is a file with two ns forms, and not a thing
  ClojureScript has.

  What is not here yet is the import per required namespace, which is what carries
  the cold-load order on the module path (doc/cljs-repl.md 7.1) and which needs the
  compilation driver that writes modules to disk. A script needs no such line and
  has script-prologue instead."
  ([ns-sym] (ns-prologue ns-sym nil))
  ([ns-sym required]
   (mapv ns-binding
         (cons ns-sym (other-namespaces ns-sym (into (set required)
                                                     nameable-namespaces))))))

(defn script-prologue
  "ns-prologue for a script, preceded by one require per required namespace.

  This is the import statement's counterpart: a script may not contain one, so it
  asks the runtime to fetch what it does not have (doc/cljs-repl.md 7.2). It goes
  in EVERY script rather than only in the one that carried the ns form, and that is
  the point - a runtime restarted underneath a REPL session refetches from disk
  instead of quietly binding an empty namespace object and failing much later at
  `foo$baz.helper is not a function`.

  await, so the requires have completed before the body runs; legal because the
  script is an async function (5).

  A JAVASCRIPT MODULE IS AWAITED AND BOUND, where a namespace is only awaited: a
  namespace's vars are reached through $ns, which needs no import to name them,
  while a module's exports are properties of the object the import statement binds
  - so the script has to bind the same name js-import does, to the same object.
  $CLJS.requireJs resolves the FILE, whose one export is `$module`, so what
  js-import spells as a named import is spelled here as the property read it is.
  The line count is why they interleave the way they do:
  one line per specifier either way, so a body sits at the same line number in the
  module and in the script that reloads it (see `script`)."
  ([ns-sym] (script-prologue ns-sym nil nil))
  ([ns-sym required] (script-prologue ns-sym required nil))
  ([ns-sym required js-required]
   (-> (mapv #(str "await $CLJS.require(\"" % "\");")
             (other-namespaces ns-sym required))
       (into (map #(str "const " (names/js-alias %)
                        " = (await $CLJS.requireJs(\"" % "\")).$module;"))
             js-required)
       (into (ns-prologue ns-sym required)))))

(defn emit-top-lines
  "Emit `node` as a top-level unit: the statements it needs, then `f` applied to
  its value expression. `f` is what makes this a statement, a return, or a
  console.log - the one place the statement/expression distinction is decided, and
  it is called exactly once. `f` may return nil to discard the value; omit it for
  the default, which evaluates the value for effect unless it has none.

  The statements, as statements. A caller putting the form inside something -
  `script` below - needs those boundaries, because indentation is per statement and
  what is inside a multi-line one must not be touched (see `indent`); joining first
  destroys exactly that information. emit-top is this plus the join."
  ([node] (emit-top-lines node nil))
  ([node f]
   ;; the analyzer's counter, continued: temporaries and locals are one sequence.
   ;; Emitting several forms into one JavaScript scope needs ONE
   ;; analyzer/with-name-scope around all of them, analysis and emission alike.
   (names/with-name-scope*
    (fn []
      (let [{:keys [stmts expr terminal? no-effect?]} (emit node)
            ;; f exactly once: it is the REPL's statement/return/wrap seam
            ;; (doc/cljs-repl.md 5), and one that allocated a name or recorded
            ;; state would otherwise fire twice
            line (when-not terminal?
                   (if f
                     (f expr)
                     ;; the default destination: evaluate for effect, unless there
                     ;; is none to have
                     (when-not no-effect? (str expr ";"))))]
        (cond-> (vec stmts)
          (some? line) (conj (sm/fill (node-pos node) line))))))))

(defn emit-top
  "emit-top-lines as one piece, for a caller that is going to print it rather than
  place it.

  A String when nothing carries a position, and a source-map chunk when something
  does - see clojure.cljs.source-map. Either prints as the same JavaScript."
  ([node] (emit-top node nil))
  ([node f] (sm/join "\n" (emit-top-lines node f))))

;; --- the evaluation unit -----------------------------------------------------

(defn return-value
  "The emit-top `f` that makes a form's value the value of the script it is the
  last form of. The REPL's destination, where a file's is the default one.

  Not called for a terminal node, because emit-top does not call `f` for one: a
  form that ends in a throw or a recur has no value to return, and control has
  already left."
  [expr]
  (str "return " expr ";"))

(defn script
  "`lines` as one unit to evaluate: an async IIFE, opening with the prelude
  bindings a script cannot import.

  This is doc/cljs-repl.md \u00a75, and it is an expression, not a statement - its value
  is a promise, which is what the runtime's eval hook awaits to get either the
  value or the throw. It carries no try/catch of its own for that reason: a
  rejected promise is already catchable at the one place that knows what to do
  with a failure, and a catch here would only have to rethrow.

  Four things follow from it being a function rather than a run of top-level
  statements:

    - `await` is legal, so loading is an ordinary expression rather than a REPL
      special form (\u00a75) and `$CLJS.require` can be a line like any other (\u00a77.2).
    - Its scope is its own, so the analyzer restarting local numbering at each top
      level form cannot collide two forms' `x__1` - they are in different scopes
      and cannot see each other. Do not 'fix' this by emitting `var`.
    - Nothing escapes but the namespace-object properties that are meant to.
    - One place for a `//# sourceURL`, and for a `//# sourceMappingURL` beside it.
      Each is a comment, so anything after one on its line is a comment too, and
      each gets a line of its own; sourceURL goes last.

  `lines` is a whole script, not one form: a REPL form is the one-element case, and
  \u00a77.1 ships a namespace body through this same function with `require` calls and a
  prologue in front and nothing returned. That is why it takes lines rather than a
  node."
  ([lines] (script lines nil nil))
  ([lines source-url] (script lines source-url nil))
  ([lines source-url source-map-url]
   ;; runtime-globals SHARES THE OPENING LINE, which looks like a formatting choice
   ;; and is an arithmetic one. A module's prologue is one runtime import, one
   ;; import per require, one const per alias, and two registry lines; a script's is
   ;; this opener, one await per require, one const per alias, and two more - the
   ;; fetch guard and one registry line. Those come to the same number only if the
   ;; opener and the globals are one line, and when they do, a namespace body sits
   ;; at the SAME line number in the module and in the script that reloads it. That
   ;; is what makes driver/body-script's //# sourceURL able to name the module
   ;; (doc/cljs-output-layout.md §4) without pointing a line off by one.
   ;; emitter-test pins the count rather than trusting this comment.
   (str "(async function () { " runtime-globals "\n"
        (sm/join "\n" (indent lines))
        "\n})()"
        ;; sourceMappingURL first and sourceURL last, so the one that has to be the
        ;; last line of the script still is.
        (when source-map-url (str "\n//# sourceMappingURL=" source-map-url))
        (when source-url (str "\n//# sourceURL=" source-url)))))
