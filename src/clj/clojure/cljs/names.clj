;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Every JavaScript name the compiler emits.

  Two spellings, and which one a name gets depends on WHO OWNS IT.

  A name the HOST owns - a property in (.-innerHTML e), a method in (.toUpperCase
  s), a global in js/Math - must be spelled the way the host spells it. We do not
  get to choose: o.delete is the property called delete, and o.delete$ is a
  different property that does not exist. host-name does that, with
  cljs.compiler's character map, so (.-foo-bar o) reaches a foo_bar property the
  way it does in ClojureScript.

  A name WE own - a local, a temporary, a var, the object a namespace's vars live
  on - only has to be legal, legible and distinct from every other name we emit.
  munge does that, and it is INJECTIVE: distinct Clojure names always give distinct
  JavaScript names.

  That is the whole trick, and it replaces a name allocator. cljs.compiler's map is
  lossy - it sends both - and _ to _ - so foo-bar and foo_bar collide. Two
  consequences, one of them a bug we shipped: (def foo-bar 1) (def foo_bar 2) made
  two vars and one property, and the second silently clobbered the first; and two
  required namespaces a.b-c and a.b_c would want the same alias at M3. Escaping the
  escape character makes the encoding decodable, therefore injective, therefore
  collision-free with no bookkeeping at all - though not the way it first looks:
  see code-map, where the obvious attempt is recorded along with the test that
  disproved it.

  The five kinds of name we own that share one JavaScript scope are then kept
  apart BY SHAPE, so no two can ever be equal:

    local        <munged>__<n>     ends in digits, always contains __
    temporary    t$<n>             ends in digits, never contains __
    ns alias     <munged>$…$ns     ends in `ns`
    fn self-name <munged>$fn       ends in `fn`
    js module    <munged>$js       ends in `js`

  A sixth is not a variable but a PROPERTY, so it shares a scope with none of
  those - what it must not collide with is another property of the same object:

    protocol     <ns-path>$$<Proto>[$<munged method>$arity$<n>]

  and it is injective for the same reason a var name is, by a construction spelled
  out in protocol-name. Anything emitted later must keep to a shape of its own.

  Note what this buys that a reserved-word list used to: nothing we own is ever a
  bare identifier that could BE a reserved word. A local ends in digits, an alias
  in `ns`, and a var is a property, where `if` is a perfectly good name. So there
  is no js-reserved here; the shapes make it unnecessary.

  SCOPE. Locals and temporaries are numbered, and the counter's scope is one
  JavaScript scope - a whole file, or a single REPL form, which is its own
  function. Our emitter flattens: every top-level form's statements land in module
  scope, so a whole file is one scope. Compile two of its forms in separate scopes
  and both counters start at one, both mint x__1, and the file dies with
  `Identifier 'x__1' has already been declared`. Erring the other way is harmless -
  one scope spanning several JavaScript scopes only makes the numbers larger - so
  when in doubt use fewer, larger scopes."}
  clojure.cljs.names
  (:refer-clojure :exclude [munge])
  (:require [clojure.string :as str]))

;; --- spelling ---------------------------------------------------------------

(def char-map
  "cljs.compiler's mapping. Used as-is for host names, and extended for our own."
  {\- "_" \: "_COLON_" \+ "_PLUS_" \> "_GT_" \< "_LT_" \= "_EQ_" \~ "_TILDE_"
   \! "_BANG_" \@ "_CIRCA_" \# "_SHARP_" \' "_SINGLEQUOTE_" \" "_DOUBLEQUOTE_"
   \% "_PERCENT_" \^ "_CARET_" \& "_AMPERSAND_" \* "_STAR_" \| "_BAR_"
   \{ "_LBRACE_" \} "_RBRACE_" \[ "_LBRACK_" \] "_RBRACK_" \/ "_SLASH_"
   \\ "_BSLASH_" \? "_QMARK_"})

(def code-map
  "char-map with its codes delimited by $ instead of _, which is what makes munge
  injective.

  Escaping the escape is not enough, and the exhaustive test in names-test says so:
  with - to _ and _ to __, the two-character name -- also gives __. As long as a
  hyphen produces a bare underscore, every _CODE_ can be forged by writing -CODE-.

  Delimiting with $ breaks that, because $ is a character no munged name can
  otherwise contain:

      -     _        the common case stays legible: foo-bar is foo_bar
      _     $US$     so an underscore in the output came from a hyphen, always
      $     $DL$     the delimiter, spelled like every other code
      >     $GT$     and so on, for every character char-map maps

  One rule each way, with no special case: a $ always delimits a code, and a _
  always came from a hyphen. Decoding is a left-to-right scan - $ characters pair
  off, and what lies between a pair is a code name."
  (into {\- "_", \_ "$US$", \$ "$DL$"}
        (map (fn [[c code]] [c (str "$" (subs code 1 (dec (count code))) "$")]))
        (dissoc char-map \-)))

(defn host-name
  "The JavaScript spelling of a name the HOST owns: a property, a method.

  Lossy on purpose. foo-bar and foo_bar both reach the property foo_bar, which is
  ClojureScript's convention for naming a snake_case host property from Clojure,
  and the host has the last word on how its own names are spelled. Never suffixed
  for reserved words: o.delete is legal, and o.delete$ is a different property."
  [sym]
  (apply str (map #(get char-map % %) (str sym))))

(def ^:private identifier-re
  "A legal JavaScript identifier."
  #"^[A-Za-z_$][A-Za-z0-9_$]*$")

(defn munge
  "The JavaScript spelling of a name WE own: a local, a var, a namespace alias.

  Injective - distinct Clojure names give distinct JavaScript names - which is why
  a var can be a property named after it without two vars ever sharing one, and
  why names-test proves it by exhaustion rather than by example."
  [sym]
  (apply str (map #(get code-map % %) (str sym))))

(defn check-own-name!
  "Refuse a name we cannot own, and say which name and why.

  Injectivity is about names that DIFFER; this is about the one thing munge does
  not fix. Every character a symbol may hold is mapped except the dot, which passes
  through - and a dot is not part of a JavaScript identifier, it is what separates
  two of them. So `a.b` reads as a property of `a`, and a name containing one has
  to be refused wherever we would emit it as a name of our own: `let a.b__1 = 1` is
  a syntax error, and `ns.a.b = 1` writes onto whatever `ns.a` happens to hold.

  The check is on the munged form and asks for a legal identifier outright, so it
  also catches a leading digit and anything else exotic a constructed symbol can
  carry - rather than enumerating what to reject."
  [sym what]
  (let [js (munge sym)]
    (when-not (re-matches identifier-re js)
      (throw (ex-info (str "Cannot use " (pr-str sym) " as " what
                           ": it spells " js ", which is not a JavaScript name."
                           (when (str/includes? (str sym) ".")
                             " A dot separates names rather than belonging to one."))
                      {:sym sym})))
    js))

;; --- the name scope ---------------------------------------------------------

(def ^:dynamic *counter*
  "The number behind locals and temporaries, or nil outside any scope. Aliases and
  var names need no scope: both are pure functions of the name."
  nil)

(defn scoped*
  "Run `f` in a fresh name scope, replacing any already in effect."
  [f]
  (binding [*counter* (atom 0)] (f)))

(defmacro with-name-scope
  "Run `body` with one name scope, shared by every form it compiles. One scope is
  one JavaScript scope - see this namespace's docstring for what breaking that
  looks like."
  [& body]
  `(scoped* (fn [] ~@body)))

(defn with-name-scope*
  "with-name-scope as a function, and a no-op when a scope already exists. A single
  form compiled alone is self-contained; several forms sharing one JavaScript scope
  need one scope around all of them."
  [f]
  (if *counter* (f) (scoped* f)))

(defn- next-n! []
  (when-not *counter*
    (throw (ex-info (str "No name scope. Locals and temporaries are numbered within"
                         " one JavaScript scope, so compiling anything needs a"
                         " with-name-scope around it - see this namespace's"
                         " docstring, and use analyze-top / emit-top, which"
                         " establish one when there is none.")
                    {})))
  (swap! *counter* inc))

;; --- the names --------------------------------------------------------------

(def ^:private auto-gensym-re
  "What the reader appends to x# inside a syntax quote: v# becomes v__11__auto__,
  minted once when the macro's body is READ, so it is a constant of the macro
  rather than fresh per expansion."
  #"^(.+)__\d+__auto__$")

(defn- legible-base
  "The part of a binding's name worth carrying into JavaScript.

  An auto-gensym's decoration is dropped, and dropping it is safe for the reason
  local-name gives: uniqueness comes from the counter, and the base is legibility
  only. What it buys is legibility, which is not a small thing here - munge sends
  _ to $US$, so v__11__auto__ reached the output as
  v$US$$US$11$US$$US$auto$US$$US$__1, and cljs.core is macros nearly all the way
  down (M5). It also drops the one part of the name that a JVM's load order can
  change, so a file using such a macro compiles to the same text twice.

  An explicit gensym call is NOT stripped and cannot be: the tmp750 it returns
  carries no mark saying it was minted, and such a macro does mint a new name on
  every expansion. Such a macro makes its callers' output differ between compiles - see
  clojure.cljs.driver, which writes a module only when its text changed."
  [sym]
  (if-let [[_ base] (re-matches auto-gensym-re (str sym))]
    (symbol base)
    sym))

(defn local-name
  "The JavaScript name for a local binding of `sym`.

  The counter is what makes it unique, and the trailing __<n> is what makes that
  legible: n appears only there and is digits-only, so the name determines n, and
  distinct n gives distinct names whatever the base names are. legible-base leans
  on exactly that, and on nothing else."
  [sym]
  (str (check-own-name! (legible-base sym) "a local name") "__" (next-n!)))

(defn temp-name
  "A name for a value that needs somewhere to live - an if's result, a recur's
  simultaneous rebinding, a spilled argument. Never contains __, so it cannot be
  a local however a local is spelled."
  []
  (str "t$" (next-n!)))

(defn fn-self-name
  "The name on the emitted function of (def f (fn* ...)), so that f reaches a stack
  trace instead of <anonymous>.

  A FOURTH shape, and it has to be one: a bare `f` would shadow a js/f global
  inside the body, and the obvious `$f` collides with the runtime's own $ns as soon
  as someone writes (def ns (fn* ...)). The $fn suffix keeps it clear of the other
  three the same way $ns keeps aliases clear, and names-test sweeps all four
  together.

  The fallback shape. var-fn-name below is what a def normally gets."
  [sym]
  (str (check-own-name! sym "a var name") "$fn"))

(defn var-fn-name
  "The name on the emitted function of (def f (fn* ...)), qualified with its
  namespace the way ClojureScript qualifies it: app$core$f, cljs$core$keyword_QMARK_.
  nil when that spelling is not ours to use, and fn-self-name is the fallback.

  A FUNCTION'S NAME IS READ BY PROGRAMS, not only by people. cljs.spec.alpha
  recovers the qualified symbol of a bare predicate from it (alpha.cljs:123,
  fn-sym): it splits the name on $, demunges each piece and joins all but the last
  with dots, so (s/form keyword?) can answer cljs.core/keyword? for a value that
  carries no other trace of where it came from. Our $fn shape gave
  keyword$QMARK$$fn, which splits to a blank piece and no symbol at all, and six of
  cljs/spec_test.cljs's assertions say so. §5.34.

  So this is HOST-NAME's spelling, not munge's - _QMARK_ rather than $QMARK$ -
  because demunge is the inverse of exactly that map, and $ has to stay a
  separator rather than an escape. Lossy, therefore: a-b and a_b are one name here,
  as they are for any host name, and two functions sharing a diagnostic name costs
  nothing because each is in scope only inside its own body.

  WHAT MAKES IT DISJOINT from the other four shapes, which is the property this
  namespace exists to keep:

    local  <munged>__n  munge escapes $ as $DL$, so no munged base can be a
                        multi-segment path, and this name never ends in __<digits>
                        unless its last piece does - which needs a $ in the base
    temp   t$<n>        the last piece is a NAME, never digits: a symbol cannot
                        start with one and host-name introduces none
    alias  <path>$ns    refused below
    self   <munged>$fn  refused below

  Those last two are refused rather than argued away, and the refusal is one rule:
  a result that reads as another shape is not ours. Two names ask for it - (def ns
  ...), whose app$core$ns IS the alias of the namespace the body reads its vars
  through, and (def fn ...), whose app$core$fn is the self-name shape - and both
  get fn-self-name instead. Nothing else can: a suffix is the last piece, and the
  only symbols host-spelling `ns` and `fn` are ns and fn.

  The identifier check is not the same as check-own-name!'s: that one is about a
  name we must own, and refusing a program over one would be right. This name is
  diagnostic, so anything it cannot spell falls back rather than throws."
  [ns-sym sym]
  (let [js (str (str/join "$" (map host-name (str/split (str ns-sym) #"\.")))
                "$" (host-name sym))]
    (when (and (re-matches identifier-re js)
               (not (str/ends-with? js "$ns"))
               (not (str/ends-with? js "$fn")))
      js)))

(defn ns-path
  "The namespace part of every name built from a namespace: app.core -> app$core,
  my-app.core -> my_app$core.

  A pure function - no scope, no allocation, no memo - and injective, given the
  precondition below. Splitting on $ recovers the segments, because the
  precondition says none of them contains one, and munge is injective per segment.

  THE PRECONDITION. A namespace segment must munge without producing a $, which
  rules out _, $ and every character char-map maps - in practice, a segment must
  look like a namespace segment. Without it the join is ambiguous: a.b_c and
  a.b.US.c would both give a$b$US$c.

  It costs nothing real, and the reason is the filesystem, not convention.
  cljs.util/ns->relpath munges a namespace into its path, so my-lib.core and
  my_lib.core are both my_lib/core.cljs - two namespaces differing only by - and _
  cannot coexist as files, and the collision this rules out is already impossible
  for anything with a source file. Of the 69 namespaces in the ClojureScript
  distribution, every segment matches [a-z0-9-]+.

  What it does reject is foo.core$macros, which self-hosted ClojureScript mints for
  a macro namespace and which users write in :require forms there. That is a naming
  scheme for a problem we solved differently - macros live in real JVM namespaces
  reached through a macro-side view (clojure.cljs.macroexpand) - so such a name has
  no meaning here, and saying so is better than aliasing it to something arbitrary.

  One property is worth naming on its own, because protocol-name leans on it and
  nothing else could supply it: the result never contains $$. Segments are joined
  by a single $ and none of them is empty, so a doubled $ can only come from
  somewhere else."
  [ns-sym]
  ;; -1 keeps trailing empty segments, which the default drops - and dropping them
  ;; is a collision: a.b. and a.b would both give a$b, the very thing the
  ;; precondition below promises cannot happen. The filesystem does not rule this
  ;; one out either, the way it rules out my-lib vs my_lib: cljs.util/ns->relpath
  ;; sends a.b to a/b.cljs and a.b. to a/b/.cljs, which are different files.
  (let [raw  (str/split (str ns-sym) #"\." -1)
        segs (map munge raw)]
    (when (or (empty? raw) (some str/blank? raw))
      (throw (ex-info (str "Bad namespace name: " (pr-str ns-sym)
                           " - a namespace needs at least one segment and none of"
                           " them may be empty.")
                      {:ns ns-sym})))
    (when-let [bad (first (filter #(str/includes? % "$") segs))]
      (throw (ex-info (str "Bad namespace name: " ns-sym
                           " - the segment munging to " bad " would not survive"
                           " being joined into a JavaScript name. A namespace"
                           " segment cannot contain _, $ or a character that munges"
                           " (write my-lib.core, not my_lib.core).")
                      {:ns ns-sym})))
    (let [path (str/join "$" segs)]
      ;; the whole path, not each segment: segments are joined with $, which is a
      ;; legal identifier character, so only the FIRST has to start like a name.
      ;; That leaves t.1 alone - a legal namespace whose path t$1 is a legal name -
      ;; while refusing 1a.core, whose 1a$core is not.
      (when-not (re-matches identifier-re path)
        (throw (ex-info (str "Bad namespace name: " (pr-str ns-sym)
                             " - it spells " path
                             ", which is not a JavaScript name.")
                        {:ns ns-sym})))
      path)))

(defn ns-alias
  "The name of the object a namespace's vars are properties of: app.core ->
  app$core$ns, my-app.core -> my_app$core$ns.

  The $ns suffix keeps an alias clear of locals, temporaries and fn self-names by
  shape; everything else about it is ns-path."
  [ns-sym]
  (str (ns-path ns-sym) "$ns"))

;; --- the name of a JavaScript module -----------------------------------------

(def ^:private specifier-code-map
  "code-map, with the dot mapped as well.

  A namespace name is spelled with dots and so is many a specifier - \"sse.js\" is
  a package, \"date-fns/locale/en-GB\" is a file - so the one character munge lets
  through has to be escaped here, where the result is a variable rather than a
  path. $DOT$ is a code like every other, so code-map's decodability argument is
  untouched: a $ still delimits a code, and the set of codes merely gained one."
  (assoc code-map \. "$DOT$"))

(defn js-alias
  "The name bound to the module a STRING require names: \"react\" -> react$js,
  \"react-dom/client\" -> react_dom$SLASH$client$js.

  A FIFTH VARIABLE SHAPE, and the fifth entry of this namespace's table. It ends
  in `js`, so it is no local (digits), no temporary (digits), no alias (`ns`) and
  no fn self-name (`fn`) - and two specifiers give two names, because
  specifier-code-map is injective for the reason code-map is.

  A module is a namespace object here, exactly as a Closure provide is and as a
  ClojureScript namespace is: the import binds the module's namespace object, and
  every reference through it is a property read off that object (react$js.useState).
  One import per specifier, whatever the ns form asked of it - :as, :refer or
  :default - which is what lets the module path and the REPL's script path bind the
  same name and share one body (doc/cljs-repl.md §4).

  Not a path: clojure.cljs.output/js->path is where a specifier becomes a file, and
  the two escape different things because one has to be a JavaScript name and the
  other has to be a URL."
  [specifier]
  (when-not (and (string? specifier) (not (str/blank? specifier)))
    (throw (ex-info (str "Bad JavaScript module specifier: " (pr-str specifier)
                         " - a string require names a module, and an empty name"
                         " names nothing.")
                    {:specifier specifier})))
  (let [munged (apply str (map #(get specifier-code-map % %) specifier))
        ;; A PACKAGE MAY BEGIN WITH A DIGIT - 3d-view is on npm - and a JavaScript
        ;; name may not. One $ in front fixes it and forges nothing: every code is
        ;; a $ followed by a capital, so a $ followed by a digit can only have come
        ;; from this rule, and the result stays injective.
        head   (if (re-find #"^[0-9]" munged) (str "$" munged) munged)
        js     (str head "$js")]
    (when-not (re-matches identifier-re js)
      (throw (ex-info (str "Cannot use " (pr-str specifier) " as a module"
                           " specifier: it spells " js ", which is not a"
                           " JavaScript name.")
                      {:specifier specifier})))
    js))

;; --- the protocol calling convention ----------------------------------------

(defn- protocol-segment
  "The munged name of a protocol, which - like a namespace segment, and for the
  same reason - may not produce a $.

  protocol-name terminates the namespace part with $$ and the protocol part with a
  single $, and both of those separators are only unforgeable while the pieces
  around them are $-free. A method name is under no such restriction, because it
  is the LAST variable-length piece: see protocol-method-name."
  [qsym]
  (let [js (munge (name qsym))]
    (when (str/includes? js "$")
      (throw (ex-info (str "Bad protocol name: " qsym
                           " - the name munging to " js " would not survive being"
                           " joined into a JavaScript name. A protocol name cannot"
                           " contain _, $ or a character that munges (write"
                           " IEditableCollection, not I-editable$collection).")
                      {:protocol qsym})))
    js))

(defn protocol-name
  "The property that marks an object as satisfying a protocol, and the prefix every
  one of that protocol's method properties is built on:

      app.core/IShape  ->  app$core$$IShape

  A FIFTH name shape, and the first one that lands on an object we do not own - a
  deftype instance is ours, but (extend-type js/Date ...) writes onto Date's
  prototype and (extend-type default ...) reaches everything. So it has to be both
  injective, like a var name, and implausible as a host property, like nothing else
  here.

  THE DOUBLED $ IS THE WHOLE TRICK. ns-path never contains $$, so the first $$ in
  the string is always the namespace boundary, whatever the namespace is; the
  protocol segment is $-free, so it ends at the next $.

  A single $ there is not enough, and the forgery is worth spelling out because it
  is narrower than it looks. Joining with one $ everywhere,

      a.b/C      method x>z    ->  a$b$C$x$GT$z$arity$1
      a.b.C.x/GT method z      ->  a$b$C$x$GT$z$arity$1

  and the two mean different things. What makes it possible is that the method is
  the one piece that may contain a $, so it can lend its opening $ to a boundary
  and its closing $ to the next one. What makes it RARE is parity: munge emits $
  only in pairs, so an alternative parse can only balance if the protocol it
  invents is a code name - GT here, US, QMARK, and the two dozen others in
  code-map. Rare is not absent, and the collision would be one protocol answering
  for another silently. names-test sweeps for exactly this pair."
  [qsym]
  (when-not (namespace qsym)
    (throw (ex-info (str "A protocol needs a namespace, and " qsym " has none."
                         " Resolve it before spelling it.")
                    {:protocol qsym})))
  (str (ns-path (namespace qsym)) "$$" (protocol-segment qsym)))

(defn protocol-method-name
  "The property holding one arity of one protocol method:

      app.core/IShape, -area, 1  ->  app$core$$IShape$_area$arity$1

  This is the calling convention. A call site computes it from the protocol and the
  method alone - the same way a var reference computes a property name from a
  symbol (see clojure.cljs.emitter/def-name) - so nothing is allocated and nothing
  has to be looked up: an implementation installed by deftype in one file is found
  by a call in another because both spell the name the same way.

  The method needs no precondition, because it is the last variable-length piece
  and $arity$<n> closes it off. Reading right to left, the digits and the literal
  arity are fixed, and a munged name cannot end with them: munge emits $ only to
  delimit a code, codes are UPPERCASE, and a name ending in an unclosed $ is not
  munge output at all. So the boundary is determined, and -a>b (which munges to
  _a$GT$b, full of $) is as safe here as -area.

  The DOT is the one thing munge does not fix, here as everywhere - a.b would give
  the property app$core$$P$a.b$arity$1, which JavaScript reads as a property of a
  property, so the implementation would be installed somewhere no call could find
  it. A protocol method is a var, so defprotocol refuses the name first; this is
  the check for a deftype naming a method its protocol never declared, which
  nothing else looks at."
  [proto-qsym method-sym arity]
  (str (protocol-name proto-qsym) "$"
       (check-own-name! method-sym "a protocol method name")
       "$arity$" arity))

(defn field-name
  "The property a deftype field is stored in: (deftype Point [x y]) puts x at
  this.x.

  host-name, not munge, and that is not a slip. A field is READ FROM OUTSIDE as
  (.-x p), which is an ordinary property access spelled the host's way, so the two
  have to agree and the host has the last word (see the two spellings in this
  namespace's docstring). The price is host-name's lossiness: foo-bar and foo_bar
  are one property, so two fields differing only there would silently be one.
  clojure.cljs.analyzer refuses that pair outright rather than letting the second
  field overwrite the first, which is the same answer check-own-name! gives for a
  var and a better one than cljs.compiler's, which has the collision."
  [sym]
  (let [js (host-name sym)]
    (when-not (re-matches identifier-re js)
      (throw (ex-info (str "Cannot use " (pr-str sym) " as a field name"
                           ": it spells " js ", which is not a JavaScript name."
                           (when (str/includes? (str sym) ".")
                             " A dot separates names rather than belonging to one."))
                      {:sym sym})))
    js))
