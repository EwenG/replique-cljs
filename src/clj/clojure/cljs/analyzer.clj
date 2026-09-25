;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "ClojureScript form -> AST.

  The AST is a tree of maps with an :op, mirroring cljs.analyzer's node shapes so
  that analysing the same form both ways and diffing is a usable oracle
  (doc/cljs-compiler.md §6). Mirrored: :op names, the structural keys (:test
  /:then/:else, :bindings/:body, :statements/:ret, :segs/:args) and :children.
  Not mirrored: everything tag inference produces - :tag, :inferred-ret-tag,
  :numeric, :jsdoc - which §7 defers, and which would make every diff noisy.

  Still partial, though much less so than it was: every special form is here except
  var and ns*. analyze throws, naming what it saw, on anything not yet handled,
  rather than guessing - the special forms arrived one at a time, each with the
  oracle behind it.

  Three jobs beyond shape. Locals are named here, not in the emitter: every binding
  gets its final JavaScript name from clojure.cljs.names, because the emitter
  flattens nested scopes - and top-level forms - into one JavaScript scope, so two
  `x`es would collide. The name is allocated rather than merely formed, so it
  cannot clash with a temporary or a namespace alias either; clojure.cljs.names
  says why a naming convention is not enough.

  A deftype field is RESOLVED here into the property access it stands for, so that
  the emitter never learns what a field is - see parse-deftype, which has the
  argument for why that is where the work belongs.

  And macroexpansion runs here, so an analyzed form has already been through the
  two macro worlds (clojure.cljs.macroexpand)."}
  clojure.cljs.analyzer
  (:require [clojure.cljs.env :as env]
            [clojure.cljs.goog :as goog]
            [clojure.cljs.macroexpand :as mx]
            [clojure.cljs.names :as names]
            ;; for js->path alone, and for its preconditions rather than its
            ;; value: a string require names a file under the output root, so what
            ;; may be written in one is the output layout's rule and is asked
            ;; where the ns form is read (plan-js-require)
            [clojure.cljs.output :as output]
            ;; for JSValue alone: #js is a data reader, so what the reader hands
            ;; back for #js [1 2] is a marker type someone has to interpret, and
            ;; the reader's own docstring says that someone is not the reader
            [clojure.cljs.reader :as reader])
  ;; ClojureScript'S JSValue, which is the one our reader constructs: the type is
  ;; shared with every macro that has to recognise a #js literal in a body it is
  ;; rewriting (clojure.cljs.reader/read-js, doc/cljs-compiler.md 5.68)
  (:import [cljs.tagged_literals JSValue]
           [clojure.lang Namespace Var]))

(declare analyze warning wrap-meta)

(def ^:dynamic *load-tests*
  "Whether a test is compiled in at all. cljs.test's deftest expands to nothing
  when it is false, and parse-def drops the ^{:test ...} property to match - the
  two have to agree, or a var would carry a test nothing generated. cljs.analyzer
  holds the same var and cljs.compiler reads it in the same place."
  true)

(def ^:dynamic *source-file*
  "The file the forms being analysed were read from, as a var's :file records it,
  or nil where they were not read from a file at all.

  A PATH UNDER A SOURCE DIRECTORY - my_lib/core.cljs - and not where the file was
  found on this machine, which is clojure.cljs.driver/source-label's rule and the
  same one Clojure follows: (:file (meta #'clojure.string/join)) is
  \"clojure/string.clj\", because *file* is bound to the resource a load went
  through rather than to a path somebody's checkout happens to have. An editor
  resolves it against the classpath, which is the one thing that can, and an
  absolute path here would be the one thing that cannot be resolved by anyone
  else.

  DYNAMIC, because there is no other way for it to arrive. The var is interned
  during analysis and the file is the driver's to know: the reader does not read
  it out of the text, no enclosing form carries it - the (ns ...) form is one form
  among the rest and a def is not inside it - and threading it through analyze
  would put a parameter on every pass for the two that use it. Clojure answers the
  same question the same way, with Compiler/SOURCE_PATH bound by load.

  NIL AT A REPL, deliberately. A form typed at a prompt was not read from a file,
  and Clojure's answer there - \"NO_SOURCE_PATH\", a string that names no file
  and that every tool then has to know is a lie - is worse than an absent key. A
  client asking where such a var was written is told nothing, which is the truth,
  and clojure.cljs.repl binds nothing."
  nil)

(def ^:dynamic *cljs-ns*
  "The namespace being compiled, as a symbol.

  clojure.cljs.env/*current-ns* is the authority and this is a copy of it, kept
  because cljs.analyzer keeps one under this name and cljs.test reads it as a
  VALUE - `'~ana/*cljs-ns*` - rather than calling anything.

  Two vars where cljs.analyzer has one, and the reason is only where the authority
  lives: the cursor is read by the reader, by macro expansion and by env itself,
  all of which are underneath this namespace, so it cannot be interned here. Bound
  by analyze-top, which is the one place that is sound: an ns form moves the
  cursor DURING its own analysis and is refused anywhere but the top level, so a
  rebinding per top-level form is exactly a rebinding per move."
  'cljs.user)

;; --- literals ---------------------------------------------------------------

(defn- const-node [env form]
  {:op :const :val form :form form :env env :children []})

(defn- analysis-error
  "A form this analyzer understands and refuses, as against `unsupported` below,
  which is a form it does not understand yet. The distinction is the reader's: one
  message says fix the code, the other says wait for a milestone."
  [form msg]
  (throw (ex-info msg {:form form})))

;; --- special forms ----------------------------------------------------------

(defn- binding-node [env sym local-kind]
  (when-not (simple-symbol? sym)
    (throw (ex-info (str "Bad binding form: " sym) {:sym sym})))
  ;; a.b is a simple symbol, and munge leaves the dot alone, so `let a.b__1 = 1`
  ;; would reach JavaScript as a syntax error. cljs.analyzer refuses dotted local
  ;; names for the same reason. Every other character a symbol may hold, char-map
  ;; turns into something legal.
  (when (clojure.string/includes? (name sym) ".")
    (throw (ex-info (str "A local name cannot contain a dot: " sym) {:sym sym})))
  (cond-> {:op :binding :name sym :js-name (names/local-name sym) :local local-kind
           :form sym :env env :children []}
    (:tag (meta sym)) (assoc :tag (:tag (meta sym)))))

(defn- not-tail
  "Sub-forms whose value is consumed cannot be in tail position, so recur cannot
  appear there. Tracked only to reject a misplaced recur - emission does not
  consult it, which is the whole point of destination-driven output."
  [env]
  (assoc env :tail? false))

(defn- parse-if [cenv env form]
  (let [[_ test then else] form]
    (when (< (count form) 3)
      (throw (ex-info "Too few arguments to if" {:form form})))
    (when (> (count form) 4)
      (throw (ex-info "Too many arguments to if" {:form form})))
    {:op :if :form form :env env
     :test (analyze cenv (not-tail env) test)
     :then (analyze cenv env then)
     :else (analyze cenv env else)
     :children [:test :then :else]}))

(defn- parse-do [cenv env form]
  (let [exprs (rest form)
        stmts (butlast exprs)
        ret   (last exprs)]
    {:op :do :form form :env env
     :statements (mapv #(analyze cenv (not-tail env) %) stmts)
     :ret (if (seq exprs) (analyze cenv env ret) (const-node env nil))
     :children [:statements :ret]}))

(defn- parse-bindings
  "The binding vector of a let* or loop*, left to right - each init sees the ones
  before it, not itself. Returns the binding nodes and the env they establish."
  [cenv env form bindings local-kind]
  (when-not (and (vector? bindings) (even? (count bindings)))
    (throw (ex-info (str local-kind "* requires a vector of an even number of forms")
                    {:form form})))
  (loop [pairs (partition 2 bindings), env env, nodes []]
    (if-let [[sym init] (first pairs)]
      (let [init-node (analyze cenv (not-tail env) init)
            node      (assoc (binding-node env sym local-kind)
                             :init init-node :children [:init])]
        (recur (rest pairs) (assoc-in env [:locals sym] node) (conj nodes node)))
      [nodes env])))

(defn- parse-let [cenv env form]
  (let [[_ bindings & body] form
        [nodes env'] (parse-bindings cenv env form bindings :let)]
    {:op :let :form form :env env
     :bindings nodes
     :body (parse-do cenv env' (cons 'do body))
     :children [:bindings :body]}))

(defn- recur-frame
  "A recur point: the bindings recur rebinds, a flag saying whether anything did,
  and a slot for the names the emitter will rebind them THROUGH.

  Both mutable cells are here for the same reason - they are answers only one side
  knows and the other needs. Whether a loop is recurred to is discovered by
  analysing its body, after the frame exists; what a recur assigns to is decided by
  the emitter, and read by an emit-jump that may be deep inside the body with no
  other channel back. See clojure.cljs.emitter/carriers!.

  `:offset` is how many of the enclosing method's parameters come BEFORE the ones
  recur rebinds - 0 everywhere except a protocol method, where it is 1 and the
  parameter it skips is the object the method was called on (see parse-fn-method).
  The emitter needs it to leave that parameter alone."
  ([params] (recur-frame params 0))
  ([params offset]
   {:params params :offset offset :flag (atom false) :carriers (atom nil)}))

(defn- parse-loop
  "loop* is let* plus a recur point. The frame carries the bindings recur rebinds
  and a flag the emitter reads: a loop nobody recurs to needs no while at all."
  [cenv env form]
  (let [[_ bindings & body] form
        [nodes env'] (parse-bindings cenv env form bindings :loop)
        frame        (recur-frame nodes)
        ;; the body is a tail position for this loop, whatever encloses the loop
        body         (parse-do cenv (assoc env' :tail? true
                                           :recur-frames (cons frame (:recur-frames env')))
                               (cons 'do body))]
    {:op :loop :form form :env env
     :bindings nodes
     :body body
     :recurs? @(:flag frame)
     ;; the emitter needs the frame, not only the flag: it is where the carrier
     ;; names go, and a recur deep in the body reads them back off it
     :frame frame
     :children [:bindings :body]}))

(defn- parse-recur
  "recur, whose argument count must match the recur point.

  A PROTOCOL METHOD IS THE ONE PLACE WHERE THAT COUNT IS NOT THE PARAMETER COUNT.
  Its first parameter is the object the method was called on, recur does not
  rebind it - Clojure's deftype methods do not either - so (search [this coll] ...)
  recurs with one argument, not two.

  Writing the object out anyway is accepted, with a warning, because
  ClojureScript accepts it: their recur-with-target lands in a parameter their
  this-as has already shadowed, so it is evaluated and dropped, and their own
  recur-test relies on the leniency. This does the same thing for the same reason -
  the expression is evaluated where it was written, and its value goes nowhere. It
  cannot be assigned to the target here: the object is a live parameter in this
  encoding, and fields are read through it (doc/cljs-compiler.md 5.4)."
  [cenv env form]
  (let [frames (:recur-frames env)
        frame  (first frames)
        exprs  (rest form)]
    (when-not frame
      ;; a nil frame in front means a try stands between here and the loop, which
      ;; is a different mistake from there being no loop at all
      (throw (ex-info (if (seq frames)
                        "Cannot recur across a try"
                        "recur outside of a loop* or fn* method")
                      {:form form})))
    (when-not (:tail? env)
      (throw (ex-info "Can only recur from tail position" {:form form})))
    (let [n       (count (:params frame))
          method? (pos? (:offset frame 0))
          target? (and method? (= (count exprs) (inc n)))]
      (when-not (or target? (= (count exprs) n))
        (throw (ex-info (str "recur expects " n " argument(s), got " (count exprs)
                             (when method?
                               (str " - a protocol method does not rebind the object"
                                    " it was called on, so its recur takes one"
                                    " argument fewer than it has parameters")))
                        {:form form})))
      (when target?
        (warning :protocol-impl-recur-with-target env {:form (first exprs)}))
      (reset! (:flag frame) true)
      {:op :recur :form form :env env
       ;; evaluated for whatever effects it has, and dropped - see above
       :target (when target? (analyze cenv (not-tail env) (first exprs)))
       :exprs (mapv #(analyze cenv (not-tail env) %) (cond-> exprs target? rest))
       :frame frame
       :children (cond-> [:exprs] target? (conj :target))})))

(defn- parse-js
  "(js* \"~{} + ~{}\" a b) - the escape hatch into raw JavaScript, and the reason
  this seed needs no core library to compute anything."
  [cenv env form]
  (let [[_ tmpl & args] form]
    (when-not (string? tmpl)
      (throw (ex-info "js* requires a string template" {:form form})))
    (let [segs (vec (.split ^String tmpl "~\\{\\}" -1))]
      ;; The emitter interleaves segments with arguments, and interleave stops at
      ;; the shorter of the two - so a mismatch is silent, and one argument too
      ;; many makes (js* "~{}" 1 2) emit `12`. A plausible wrong number is worse
      ;; than any syntax error.
      (when-not (= (count args) (dec (count segs)))
        (throw (ex-info (str "js* template has " (dec (count segs))
                             " placeholder(s) but was given " (count args)
                             " argument(s)")
                        {:form form})))
      (cond-> {:op :js :form form :env env
               :segs segs
               :args (mapv #(analyze cenv (not-tail env) %) args)
               :children [:args]}
        ;; ^boolean ON THE js* FORM ITSELF, which is how cljs.core spells the
        ;; annotation for everything it inlines: cljs.core/bool-expr (core.cljc:952)
        ;; is (vary-meta e assoc :tag 'boolean), and it wraps the js* of
        ;; coercive-=, ==, <, instance? and twenty more. Those are the hot tests -
        ;; (nil? x) is a MACRO expanding to (coercive-= x nil), so it never reaches
        ;; an :invoke and the return tag on the var of the same name never sees it.
        (:tag (meta form)) (assoc :tag (:tag (meta form)))))))

(defn- parse-fn-method
  "One ([params] body...) of an fn*. The rest parameter, if any, is the last entry
  of :params - :fixed-arity counts the ones before it, exactly as cljs.analyzer
  does, so arity dispatch reads off the node without re-scanning the params."
  [cenv env form]
  ;; before the destructuring, which is what sees this first: (fn* 1) and
  ;; (fn* ([x] 1) 2) used to fail with "Don't know how to create ISeq from
  ;; java.lang.Long", a Clojure error about our own implementation rather than a
  ;; sentence about the form
  (when-not (seq? form)
    (throw (ex-info (str "fn* method must be a list of a parameter vector and a"
                         " body, got " (pr-str form))
                    {:form form})))
  (let [[params & body] form]
    (when-not (vector? params)
      (throw (ex-info "fn* method requires a parameter vector" {:form form})))
    (let [amp       (.indexOf ^java.util.List params '&)
          variadic? (not (neg? amp))
          _         (when (and variadic? (not= amp (- (count params) 2)))
                      (throw (ex-info "& must be followed by exactly one parameter"
                                      {:form form})))
          fixed     (if variadic? (subvec params 0 amp) params)
          rest-sym  (when variadic? (peek params))
          ;; the rest parameter must be a symbol, and the guard tests variadic?
          ;; rather than rest-sym: (fn* [& nil] 1) has a rest position holding nil,
          ;; which is falsey, so testing rest-sym would silently produce a method
          ;; that is :variadic? with no rest binding - and the emitter would then
          ;; pop an empty vector rather than report anything
          _         (when (and variadic? (not (simple-symbol? rest-sym)))
                      (throw (ex-info (str "& must be followed by a symbol, got "
                                           (pr-str rest-sym))
                                      {:form form})))
          bindings  (mapv #(binding-node env % :arg) (cond-> fixed variadic? (conj rest-sym)))
          env'      (update env :locals into (map (juxt :name identity)) bindings)
          ;; A PROTOCOL METHOD'S FIRST PARAMETER IS THE OBJECT IT WAS CALLED ON,
          ;; and recur does not rebind it, so the recur point starts after it.
          ;; cljs.core's adapt-proto-params marks the parameter as it introduces
          ;; it - the one place that knows, since it is the same place that decides
          ;; a method takes the object as a parameter at all (doc §5.4). Marked
          ;; there rather than a flag on the fn form, which is what cljs.analyzer
          ;; reads: their marker sits on every method of a deftype, Object methods
          ;; included, and an Object method has no such parameter to skip.
          offset    (if (-> (first fixed) meta ::method-target) 1 0)
          frame     (recur-frame (subvec bindings offset) offset)
          ;; :top-level? clears here and only here. A do keeps it, because
          ;; (do (ns a) ...) IS top level; a function body is where an
          ;; analysis-time effect and a run-time one part company. See parse-ns.
          body      (parse-do cenv (assoc env' :tail? true :top-level? false
                                          :recur-frames (cons frame (:recur-frames env')))
                              (cons 'do body))]
      {:op :fn-method :form form :env env
       :params bindings
       ;; whether the first parameter is the OBJECT the method was called on
       ;; rather than an argument anyone passed. The emitter needs it for one
       ;; thing: `Invalid arity: n` must count what the caller wrote, and
       ;; ({} 1 2 3) reaches PersistentArrayMap.prototype.call with four.
       ;;
       ;; Two ways to know, and both are here because they cover different shapes.
       ;; ::method-target is ours, put on the parameter by whichever of
       ;; cljs.core's adapt-*-params introduced it (see method-target's docstring),
       ;; and it is the one `offset` above already trusts. `self__` is the name
       ;; adapt-ifn-params uses when the deftype named no self, and it is what
       ;; cljs.compiler tests for at compiler.cljc:1096 - literally
       ;; (= 'self__ (-> ms first val :params first :name)). A user who names a
       ;; parameter self__ gets ClojureScript's answer to that, which is this one.
       :method-target? (boolean (or (pos? offset) (= 'self__ (first fixed))))
       :fixed-arity (count fixed)
       :variadic? variadic?
       :recurs? @(:flag frame)
       :frame frame
       :body body
       :children [:params :body]})))

(defn- async-fn?
  "Whether this fn* form was marked ^:async - a JavaScript async function, whose
  body may `await`.

  TWO PLACES TO LOOK, and both are where the reader actually puts the metadata:

    (^:async fn [x] ...)      on the SYMBOL `fn`, which is (first form) once
                              cljs.core/fn has carried its own metadata onto the
                              fn* symbol it emits (core.cljc's fn-sym-meta)
    (letfn [(^:async f [] ...)])  on the self-NAME, because ^:async there sits
                              inside the spec list, in front of f

  (defn ^:async foo ...) is the third spelling and arrives through neither: the
  metadata is on the DEF's name, so parse-def moves it onto the init form's head
  before analysing it. See the note there.

  cljs.analyzer reads the same two places (analyzer.cljc:2317) and deliberately
  does NOT read the fn form's own metadata - ^:async (fn ...) is not the spelling."
  [form fn-name]
  (boolean (or (:async (meta (first form)))
               (:async (meta fn-name)))))

(defn- parse-fn [cenv env form]
  (let [more     (rest form)
        fn-name  (when (simple-symbol? (first more)) (first more))
        more     (if fn-name (rest more) more)
        ;; (fn* [x] body) is sugar for (fn* ([x] body))
        method-forms (if (vector? (first more)) (list more) more)
        async?   (async-fn? form fn-name)
        ;; the name is in scope inside the methods, so a self-call resolves
        name-b   (when fn-name (binding-node env fn-name :fn))
        ;; :async IS SET ON EVERY FN, true or false, and the false matters as much
        ;; as the true: an env is inherited by everything analysed inside it, so a
        ;; plain (fn [] 20) nested in an async one has to say so or `await` would
        ;; still expand there. cljs.analyzer assocs it unconditionally for the same
        ;; reason. Between fns it is inherited on purpose - a let, a loop, a try or
        ;; a case inside an async fn is still inside it, and awaiting there is
        ;; exactly what the tests do.
        env'     (cond-> (assoc env :async async?)
                   name-b (assoc-in [:locals fn-name] name-b))
        methods  (mapv #(parse-fn-method cenv env' %) method-forms)]
    (when (empty? methods)
      (throw (ex-info "fn* requires at least one method" {:form form})))
    (when (< 1 (count (filter :variadic? methods)))
      (throw (ex-info "fn* can have only one variadic method" {:form form})))
    ;; :fixed-arity counts the parameters before the &, so the variadic method's
    ;; is not an arity anything can clash with: (fn* ([x] ..) ([x & ys] ..)) is
    ;; legal and is the shape of conj, assoc and str. What is illegal is a fixed
    ;; method taking MORE parameters than the variadic one, since then no call
    ;; could ever reach the variadic method. Both rules are Clojure's, and
    ;; cljs.analyzer warns on the second.
    (let [fixed   (remove :variadic? methods)
          arities (map :fixed-arity fixed)
          var-m   (first (filter :variadic? methods))]
      (when-not (or (empty? arities) (apply distinct? arities))
        (throw (ex-info "fn* methods cannot have the same arity" {:form form})))
      (when (and var-m (some #(> (:fixed-arity %) (:fixed-arity var-m)) fixed))
        (throw (ex-info (str "fn* cannot have a fixed arity with more parameters "
                             "than the variadic method")
                        {:form form}))))
    ;; THREE KEYS THAT ARE NOT THE PROGRAM'S. cljs.core/dt->et annotates every
    ;; method form of a deftype/extend-type with ::ana/type, ::ana/protocol-impl
    ;; and ::ana/protocol-inline, and they ride on the fn* form the spec becomes.
    ;; cljs.analyzer reads all three and then drops them at exactly this point
    ;; (analyzer.cljc:2359); we read none of them - a recur point is found from
    ;; the parameter instead, see cljs.core/method-target - but they still have to
    ;; go, or every protocol method in cljs.core would be built by calling
    ;; with-meta, most of them before with-meta exists.
    ;; WRAPPED LIKE ANY OTHER LITERAL. A fn is a value a program can hang
    ;; metadata on - (meta ^:foo (fn [])) is {:foo true} in ClojureScript, where
    ;; parse 'fn* ends in analyze-wrap-meta (analyzer.cljc:2399) exactly as the
    ;; collection parsers do. This used to be skipped on the grounds that the only
    ;; metadata reaching an fn* form is ^:once; that is not so - ^:once appears
    ;; nowhere in the vendored tree, and what does reach here is what a program
    ;; wrote. The two marks this compiler reads itself, :async and the fn's own
    ;; name, live on the HEAD symbol rather than on the form (see async-fn?), so
    ;; they do not turn into a with-meta call.
    ;;
    ;; The cost is that (def f ^:foo (fn ...)) is no longer an :op :fn init, so
    ;; name-defd-fn does not fire and the emitted function is anonymous.
    ;; cljs.analyzer loses fn-var? at the same place for the same reason.
    (wrap-meta cenv env (vary-meta form dissoc
                                   ::type ::protocol-impl ::protocol-inline)
      (cond-> {:op :fn :form form :env env
             :methods methods
             :async? async?
             ;; read off the first method: every method of one fn agrees about it,
             ;; because they come from one adapt-*-params call
             :method-target? (boolean (:method-target? (first methods)))
             :variadic? (boolean (some :variadic? methods))
             :max-fixed-arity (apply max (map :fixed-arity methods))
             :children [:methods]}
      name-b (assoc :name name-b :local name-b :children [:local :methods])))))

(defn- name-defd-fn
  "Give (def f (fn* ...)) a self-name of f, as cljs.analyzer does.

  Emission only: the name is NOT added to :locals, so a self-call inside the body
  still resolves to the var, exactly as it does in ClojureScript. What it buys is a
  named JavaScript function instead of an anonymous one, so the name reaches a
  stack trace.

  The spelling is names/var-fn-name - app$core$f, the name ClojureScript gives it,
  because a program reads it: cljs.spec.alpha recovers a bare predicate's qualified
  symbol from the function's .name and can only do that from this shape (§5.34).
  names/fn-self-name is the fallback for the one name that spelling is not ours to
  use, which is (def ns ...). A bare `f` would do for neither: it would shadow a
  js/f global inside the body.

  An fn* that named itself keeps its own name, which IS in scope."
  [cenv sym node]
  (if (and (= :fn (:op node)) (nil? (:local node)))
    (let [js (or (names/var-fn-name env/*current-ns* sym)
                 (names/fn-self-name sym))
          b {:op :binding :name sym :js-name js
             :local :fn :form sym :env (:env node) :children []}]
      (assoc node :name b :local b :children [:local :methods]))
    node))

(defn- parse-def
  "def interns a ClojureScript Var - root-unbound, metadata only - in the current
  namespace of cenv's ClojureScript world. That happens during analysis, not after,
  so a later form in the same file can refer to it.

  This is the first thing that puts anything in a NamespaceWorld by compiling."
  [cenv env form]
  (let [[_ sym0 & more] form
        ;; A NAME QUALIFIED WITH THE NAMESPACE BEING COMPILED IS THAT NAME.
        ;; Clojure's own rule (Compiler.java: "Can't refer to qualified var that
        ;; doesn't exist" only for a FOREIGN namespace), and cljs.analyzer's -
        ;; parse 'def refuses only (and sym-ns (not= sym-ns ns-name)), with the
        ;; message "Can't def ns-qualified name in namespace". A macro reaches it
        ;; without meaning to: a syntax-quoted (def ~name ...) resolves `name`
        ;; against the namespace expanding it, which is how test.check's defspec
        ;; arrives here as (def cljs.core-test/foo-1274 ...).
        sym    (if (and (qualified-symbol? sym0)
                        (= (symbol (namespace sym0)) env/*current-ns*))
                 (with-meta (symbol (name sym0)) (meta sym0))
                 sym0)]
    (when-not (simple-symbol? sym)
      (throw (ex-info (str "First argument to def must be a simple symbol"
                           (when (qualified-symbol? sym)
                             (str " or one qualified with " env/*current-ns*))
                           ", got: " (pr-str sym))
                      {:form form})))
    ;; simple-symbol? is not enough: a.b is one, and a var is emitted as a property
    ;; named after it, so (def a.b 1) would write onto whatever the var a holds.
    ;; The same gate a local goes through (cljs.analyzer has no equivalent - it
    ;; emits a bare global there, which is a different wrong answer).
    (names/check-own-name! sym "a var name")
    (when (> (count more) 2)
      (throw (ex-info "Too many arguments to def" {:form form})))
    (let [doc?      (= 2 (count more))
          doc       (when doc? (first more))
          ;; (def x 1 2): the doc position holds something that is not a doc, so
          ;; this is one argument too many. cljs.analyzer says the same, and says
          ;; it with this message - silently dropping the extra form would be the
          ;; worst of the three options.
          _         (when (and doc? (not (string? doc)))
                      (throw (ex-info "Too many arguments to def" {:form form})))
          init-form (if doc? (second more) (first more))
          ;; (defn ^:async foo ...) is (def ^:async foo (fn foo ...)), so the mark
          ;; is on the DEF's name and the fn never sees it. Moved onto the head of
          ;; the init form - the symbol `fn`, which cljs.core/fn carries onto the
          ;; fn* it emits - so that async-fn? finds it in one of the two places it
          ;; looks, and so that the body is analysed with :async set rather than
          ;; discovered to be async after the fact. cljs.analyzer has no such step
          ;; because its `name` is a parameter of parse and travels down on its own.
          init-form (if (and (:async (meta sym))
                             (seq? init-form)
                             (instance? clojure.lang.IObj (first init-form)))
                      (with-meta
                        (cons (vary-meta (first init-form) assoc :async true)
                              (rest init-form))
                        (meta init-form))
                      init-form)
          init?     (pos? (count more))
          qname     (symbol (str env/*current-ns*) (str sym))
          ^Namespace ns (env/cljs-ns cenv)
          ^Var v    (.intern ns sym)
          m         (meta form)
          ;; A DEF OF A CORE NAME TAKES THAT NAME OVER, MACRO INCLUDED (5.32).
          ;; Interning is enough for resolution - resolve-var asks this namespace
          ;; first - but a macro is expanded before anything is resolved, so a
          ;; namespace that defines `/` would still see (/ x y) expand to
          ;; cljs.core's division. Recorded as an exclude, which is the set macro
          ;; lookup already consults, and which is what (:refer-clojure :exclude
          ;; [/]) would have said by hand. cljs.analyzer does exactly this at the
          ;; same point (analyzer.cljc:2087).
          ;;
          ;; Not in cljs.core, which would exclude every name it defines from
          ;; itself. Nothing to undo either: clear-ns-declaration! drops ::excludes
          ;; when an ns form is re-analysed, and re-analysing the file re-runs the
          ;; defs that put them back.
          _         (when (and (not= 'cljs.core env/*current-ns*)
                               (env/core-name? cenv sym))
                      (env/add-excludes! cenv env/*current-ns* #{sym}))]
      ;; WHERE IT WAS WRITTEN, which is a position and the file the position is in.
      ;; The position comes off the form, because the reader read it; the file
      ;; comes from *source-file*, because nothing in the form says it. Both are
      ;; merged rather than assoc'd over a redefinition, and a def in a file
      ;; therefore MOVES a var that a REPL had defined before it, which is what
      ;; somebody jumping to the definition wants: the last place it was written.
      (alter-meta! v merge
                   (cond-> (select-keys m [:line :column :end-line :end-column])
                     *source-file* (assoc :file *source-file*)
                     doc (assoc :doc doc)
                     (meta sym) (merge (meta sym))))
      (let [init (when init?
                   (name-defd-fn cenv sym (analyze cenv (not-tail env) init-form)))]
        ;; ^boolean ON A defn IS A RETURN TAG. (defn ^boolean nil? [x] ...) is how
        ;; cljs/core.cljs writes 86 of its predicates, and what it says is not that
        ;; the var holds a boolean - it holds a function - but that CALLING it
        ;; yields one. So it is recorded apart from :tag, under the name
        ;; cljs.analyzer keeps it under, and parse-invoke reads it there
        ;; (fn-ast->tag, analyzer.cljc:1612). Without this, ^boolean would be
        ;; honoured only where a program tests a var directly, which is ten call
        ;; sites in cljs.core against two thousand that test a predicate's result.
        (when (and (= :fn (:op init)) (:tag (meta sym)))
          (alter-meta! v assoc :ret-tag (:tag (meta sym))))
        ;; AND A REDEFINITION REPLACES THE TAGS, for the reason below: merged, a
        ;; ^boolean dropped from the source would stay on the var, and every if
        ;; compiled against it after would skip truth_ for a value that may be
        ;; nil. Only a def with an init - a declare says nothing new.
        (when init?
          (when-not (:tag (meta sym))
            (alter-meta! v dissoc :tag))
          (when-not (and (= :fn (:op init)) (:tag (meta sym)))
            (alter-meta! v dissoc :ret-tag)))
        ;; A REDEFINITION REPLACES THE SHAPE, IT DOES NOT ADD TO IT. The metadata
        ;; above is merged, which is right for a doc string and wrong for :top-fn:
        ;; redefining a two-arity foo as a one-argument one would leave the old
        ;; entry behind, and every later call site would dispatch to an arity that
        ;; the new definition no longer sets. Only a def WITH AN INIT clears it -
        ;; (declare foo) after a (defn foo ...) is not a new shape, it is a
        ;; forward declaration of the one already there. §5.33.
        (when (and init? (not (:top-fn (meta sym))))
          (alter-meta! v dissoc :top-fn))
        (cond-> {:op :def :form form :env env
               :name qname
               :doc doc
               :var {:op :var :name qname :ns env/*current-ns* :form sym :env env}
               :children [:var]}
        init? (assoc :init init
                     :children [:var :init])
        ;; ^{:test (fn [] ...)} IS COMPILED, and this is the only piece of def
        ;; metadata that is. cljs.test's deftest is (def ^{:test body} name ...),
        ;; and cljs.test/test-var runs (.-cljs$lang$test v) - so the form in the
        ;; metadata has to become a function in the OUTPUT, not just an entry in
        ;; the symbol table. cljs.compiler emits the same property from the same
        ;; key (compiler.cljc:900), under the same *load-tests* switch.
        (and *load-tests* (:test (meta sym)))
        (as-> node (assoc node
                          :test (analyze cenv (not-tail env) (:test (meta sym)))
                          :children (conj (:children node) :test))))))))

(defn- parse-invoke [cenv env form]
  (let [env  (not-tail env)
        fnode (analyze cenv env (first form))]
    (cond-> {:op :invoke :form form :env env
             :fn fnode
             :args (mapv #(analyze cenv env %) (rest form))
             :children [:fn :args]}
      ;; the callee's RETURN tag, which is the invoke's tag - see parse-def. The
      ;; only tag this compiler propagates, and it goes one place: emit-if.
      (:ret-tag fnode) (assoc :tag (:ret-tag fnode)))))

(def ^:private property-symbol?
  "(. o -x) reads a property; (. o x) calls a method. The leading minus is the
  only thing that tells them apart."
  #(boolean (and (symbol? %) (.startsWith (name %) "-"))))

(defn- parse-dot
  "(. target member args...), the form all host interop reduces to - the reader
  sugar .foo / Foo. is rewritten into it by clojure.cljs.macroexpand/host-sugar.

  Follows cljs.analyzer/build-dot-form. Four shapes:

      (. o -x)        property read     -> :host-field
      (. o m)         method call, none -> :host-call
      (. o m 1 2)     method call       -> :host-call
      (. o (m 1 2))   method call       -> :host-call

  Note the second: with no arguments and no minus this is o.m(), not o.m. That is
  where ClojureScript parts company with Clojure on the JVM, where (. o m) reads a
  field. JavaScript has no reflection to disambiguate on, so the syntax has to."
  [cenv env form]
  (let [[_ target member & args] form
        env (not-tail env)]
    (when (nil? target)
      (throw (ex-info "Bad dot form: no target" {:form form})))
    (let [tgt    (analyze cenv env target)
          member! (fn [sym what]
                    ;; (. o -) leaves nothing after the minus, and (. o ()) has no
                    ;; method at all; either emits `o.` - a syntax error
                    (when-not (and (simple-symbol? sym) (seq (name sym)))
                      (throw (ex-info (str "Bad dot form: " what " is missing")
                                      {:form form})))
                    sym)
          call (fn [method args]
                 {:op :host-call :form form :env env
                  :target tgt :method method
                  :args (mapv #(analyze cenv env %) args)
                  :children [:target :args]})]
      (cond
        (property-symbol? member)
        (do (when (seq args)
              (throw (ex-info (str "Cannot provide arguments " (pr-str args)
                                   " on property access " member)
                              {:form form})))
            {:op :host-field :form form :env env
             :target tgt :field (member! (symbol (subs (name member) 1)) "a field name")
             :children [:target]})

        (symbol? member) (call (member! member "a method name") args)

        (seq? member)
        (do (when (seq args)
              (throw (ex-info (str "Cannot provide arguments " (pr-str args)
                                   " after the method list " (pr-str member))
                              {:form form})))
            (call (member! (first member) "a method name") (rest member)))

        :else
        (throw (ex-info (str "Bad dot form: " (pr-str form)) {:form form}))))))

(defn- parse-new
  "(new Ctor args...), and so (Ctor. args...) after host-sugar."
  [cenv env form]
  (let [[_ ctor & args] form
        env (not-tail env)]
    (when (nil? ctor)
      (throw (ex-info "new requires a constructor" {:form form})))
    {:op :new :form form :env env
     :class (analyze cenv env ctor)
     :args (mapv #(analyze cenv env %) args)
     :children [:class :args]}))

(defn- parse-throw
  "(throw e). Control never leaves, which the emitter records as :terminal? - the
  same mark recur carries, and the reason a throw in expression position needs no
  function wrapper here."
  [cenv env form]
  (when (not= 2 (count form))
    (throw (ex-info "throw expects exactly one argument" {:form form})))
  {:op :throw :form form :env env
   :exception (analyze cenv (not-tail env) (second form))
   :children [:exception]})

(def ^:private compiler-flag-vars
  "The three cljs.core vars that name a COMPILER setting rather than a value, and
  whose (set! <flag> true|false) ClojureScript answers at compile time and does not
  emit (cljs.analyzer 1.12.145:2712-2775). §5.37.

  They are ordinary defs in core.cljs so that reading one is not an error; the
  reading is the only thing the runtime does with them."
  '#{cljs.core/*unchecked-if* cljs.core/*unchecked-arrays* cljs.core/*warn-on-infer*})

(defn- parse-set!
  "(set! target val), where target is a var or a property.

  Follows cljs.analyzer, which refuses only two things: a local (JavaScript would
  happily assign one, but a Clojure local is immutable) and a constant. Assigning a
  var in the current namespace is allowed - it is a plain assignment to the
  module-level name.

  (set! o -prop val) is the three-place sugar for (set! (. o -prop) val)."
  [cenv env form]
  (when-not (<= 3 (count form) 4)
    (throw (ex-info "set! expects (set! target val) or (set! target -prop val)"
                    {:form form})))
  (let [[_ target val alt] form
        [target val] (if (= 4 (count form)) [(list '. target val) alt] [target val])
        env    (not-tail env)
        ;; asked of the SYMBOL, before analysis turns a field into the property
        ;; access it stands for - by then it is an ordinary set!-able target and
        ;; nothing would be left to refuse.
        fld    (when (symbol? target) (get-in env [:locals target]))
        _      (when (and fld (= :field (:local fld)) (not (:mutable? fld)))
                 (analysis-error form
                                 (str "Cannot set! the field " target
                                      " - a deftype field is immutable unless it is"
                                      " declared ^:mutable.")))
        tnode  (analyze cenv env target)]
    ;; :goog-var is here because a goog var IS a property access: goog/global
    ;; emits goog$ns.global, and $ns("goog") is the goog object itself once
    ;; base.js has run (§5.5). core.cljs sets it, under js/COMPILED, to whichever
    ;; of window/self/global the target has.
    (when-not (#{:var :js-var :goog-var :host-field} (:op tnode))
      (throw (ex-info (str "Cannot set! " (pr-str target)
                           (case (:op tnode)
                             :local " - a local is immutable"
                             ;; NOT an oversight and not ours to relax: an ES
                             ;; module's exports are read-only bindings in the
                             ;; importer, so the assignment would be a TypeError
                             ;; in the host rather than a rule of this compiler's.
                             (:js-module :js-module-var)
                             (str " - a JavaScript module's exports are read-only"
                                  " bindings where it is imported")
                             " - a set! target must be a var or a property access"))
                      {:form form})))
    (if (and (= :var (:op tnode))
             (contains? compiler-flag-vars (:name tnode))
             (or (true? val) (false? val)))
      ;; A COMPILER FLAG IS NOT A RUNTIME VARIABLE. Setting one is answered here
      ;; and nothing is emitted, which is what ClojureScript does outside the REPL
      ;; (cljs.analyzer 1.12.145:2769 returns {:op :no-op}) and why their own
      ;; array_access_test asserts that cljs.core/*unchecked-arrays* is still
      ;; false after a file has set it.
      ;;
      ;; The form keeps the VALUE a set! has - its right-hand side, which the
      ;; guard has already restricted to a boolean literal - so it analyses to
      ;; that constant. No new node type: a constant is already stable and
      ;; effect-free, so the emitter drops it in statement position, which is
      ;; every position one of these appears in.
      (analyze cenv env val)
      (do
        ;; ASSIGNING A VAR THROWS AWAY WHAT WE KNEW ABOUT ITS SHAPE. (set! f (fn ...))
        ;; replaces the function, and an ordinary fn has no arity properties on it at
        ;; all - so a later (f 1 2) must go back through the function itself. The same
        ;; rule parse-def applies to a redefinition, applied to the other way a var's
        ;; value changes. NOT for a property: (set! (. f -cljs$core$IFn$_invoke$arity$2)
        ;; ...) is how core.cljc BUILDS the shape, and that target is a :host-field.
        ;; §5.33.
        (when (= :var (:op tnode))
          (some-> ^Namespace (env/find-cljs-ns cenv (:ns tnode))
                  (.findInternedVar (symbol (name (:name tnode))))
                  (alter-meta! dissoc :top-fn)))
        {:op :set! :form form :env env
         :target tnode
         :val (analyze cenv env val)
         :children [:target :val]}))))

(defn- catch-clause? [f] (and (seq? f) (= 'catch (first f))))
(defn- finally-clause? [f] (and (seq? f) (= 'finally (first f))))

(defn- split-try
  "A try form as {:body :catches :default :finally}, with the grammar enforced:
  body first, then catch clauses, then at most one finally.

  (catch :default e ...) is separated out because it is not a type test - it
  catches everything, which is also why it has to come last: anything after it
  would be dead."
  [form]
  (let [[body more]    (split-with (complement (some-fn catch-clause? finally-clause?))
                                   (rest form))
        [catches more] (split-with catch-clause? more)
        [fins more]    (split-with finally-clause? more)]
    (when (seq more)
      (analysis-error form "In a try, catch clauses come after the body and finally comes last"))
    (when (< 1 (count fins))
      (analysis-error form "A try can have only one finally"))
    (doseq [c catches]
      (when (< (count c) 3)
        (analysis-error c "A catch clause is (catch type name body...)"))
      (when-not (simple-symbol? (nth c 2))
        (analysis-error c (str "A catch binding must be an unqualified symbol, got "
                               (pr-str (nth c 2))))))
    (let [defaults (filterv #(= :default (second %)) catches)]
      (when (< 1 (count defaults))
        (analysis-error form "A try can have only one (catch :default ...)"))
      (when (and (seq defaults) (not= (last catches) (first defaults)))
        (analysis-error form "(catch :default ...) catches everything, so it must come last"))
      {:body    body
       :catches (filterv #(not= :default (second %)) catches)
       :default (first defaults)
       :finally (first fins)})))

(defn- catch-chain
  "Every catch clause as ONE form over one binding, which is all JavaScript offers:
  a single catch parameter holding whatever was thrown.

  A typed clause becomes an instanceof test, :default becomes the else, and with no
  :default the else rethrows - so an unmatched exception keeps travelling instead of
  being swallowed. cljs.analyzer desugars the same way, into cond and instance?;
  this uses if and js* because there is no core library to call yet."
  [e catches default]
  (reduce (fn [else [_ type nm & body]]
            (list 'if (list 'js* "(~{} instanceof ~{})" e type)
                  (list* 'let* [nm e] body)
                  else))
          (if default
            (let [[_ _ nm & body] default] (list* 'let* [nm e] body))
            (list 'throw e))
          (reverse catches)))

(defn- parse-try
  "(try body* (catch type name body*)* (finally body*)?)

  The catch clauses are desugared here rather than emitted as a chain, so that the
  emitter owns only the try/catch/finally frame and everything else - the branch
  values, the terminal arms, the destination - comes from if, let* and throw, which
  already have it."
  [cenv env form]
  (let [{:keys [body catches default finally]} (split-try form)
        ;; RECUR MAY NOT CROSS A TRY: JavaScript's continue cannot leave the block,
        ;; and a finally would have to run on the way out of a jump that has no way
        ;; to run it. A nil frame in front is how the barrier is spelled - a loop*
        ;; written INSIDE the try conses its own frame on top, so recurring to it
        ;; still works.
        env'   (assoc env :tail? false
                      :recur-frames (cons nil (:recur-frames env)))
        caught (when (or (seq catches) default)
                 ;; a temp-name, not a local name: this holds the raw exception and
                 ;; is not a binding anyone wrote. The name shapes are disjoint
                 ;; (clojure.cljs.names), so it cannot collide with a local however
                 ;; one is spelled, and it is allocated from the same counter, so
                 ;; two compiles of one file still agree.
                 {:op :binding :name (gensym "e") :js-name (names/temp-name)
                  :local :catch :form form :env env :children []})]
    {:op :try :form form :env env
     :body    (parse-do cenv env' (cons 'do body))
     :binding caught
     :catch   (when caught
                (analyze cenv (assoc-in env' [:locals (:name caught)] caught)
                         (catch-chain (:name caught) catches default)))
     :finally (when finally (parse-do cenv env' (cons 'do (rest finally))))
     :children (cond-> [:body]
                 caught  (conj :binding :catch)
                 finally (conj :finally))}))

(defn- field-bindings
  "The fields of a deftype*, as bindings that play two roles at once.

  :js-name is a CONSTRUCTOR PARAMETER, an ordinary local, because that is what the
  emitted function takes. :field is the PROPERTY it is stored in, spelled the
  host's way by names/field-name, because (.-x p) from another namespace is an
  ordinary property access and the host has the last word on how one is spelled.

  host-name is lossy where munge is not, so foo-bar and foo_bar are one property.
  Two fields differing only there are refused here rather than allowed to become
  one silently - the second would overwrite the first, which is exactly the bug
  clojure.cljs.names exists to have fixed for vars."
  [env fields]
  (let [bs (mapv (fn [sym]
                   (when-not (simple-symbol? sym)
                     (throw (ex-info (str "Bad field name: " (pr-str sym))
                                     {:field sym})))
                   {:op :binding :name sym :js-name (names/local-name sym)
                    :field (names/field-name sym)
                    :mutable? (boolean (or (:mutable (meta sym))
                                           (:unsynchronized-mutable (meta sym))
                                           (:volatile-mutable (meta sym))))
                    :local :field :form sym :env env :children []})
                 fields)]
    (doseq [[js group] (group-by :field bs)
            :when (> (count group) 1)]
      (throw (ex-info (str "Fields " (clojure.string/join " and "
                                                          (map (comp pr-str :name) group))
                           " are one field: both spell the property " js
                           ". A field is read from outside as (.-" js " x), so it"
                           " is spelled the host's way, and that spelling maps a"
                           " hyphen and an underscore to the same character.")
                      {:fields (mapv :name group)})))
    bs))

(def ^:private record-fields
  "The three fields defrecord* adds to whatever the user wrote. The names are not
  ours to choose: cljs.core's defrecord macro reads them back as (.-__meta r), and
  vendoring that macro at M5 is the point of getting the special form right now.

  __hash IS MUTABLE and the other two are not, which is cljs.analyzer's list
  verbatim (analyzer.cljc:3636). A record caches its own hash: -hash expands
  through core.cljc's caching-hash, which reads the field, computes on nil, and
  set!s the answer back - so the one field the macro writes to is the one field
  declared writable here."
  '[__meta __extmap ^:mutable __hash])

(defn- parse-deftype
  "(deftype* Name [fields] self body) and (defrecord* Name [fields] self body).

  A def whose init is a constructor, plus a body that runs straight after it. The
  var is interned before the body is analysed, because the body is what installs
  the protocol implementations and it names the type to reach its prototype.

  SELF IS THE THIRD ARGUMENT, and cljs.analyzer has no equivalent. A field is
  reachable by its bare name inside a method, and a method is an ordinary function
  in the body - so something has to say WHICH object the bare name reads from.
  ClojureScript answers with JavaScript's `this`, hard-coding the local name self__
  in cljs.compiler/munge and threading it in with a this-as around every method
  body. That answer does not survive here: our fn* emits a plain function
  expression, so a nested fn inside a method would rebind `this`, and the arity
  dispatch of a multi-arity fn* reads `arguments`, which arrow functions do not
  have - so we cannot buy lexical `this` by emitting arrows instead.

  Naming the binding is both simpler and stronger. The macro writes each method as
  (fn* [self ...] ...) and passes the same symbol here; a field then analyses as
  (. self -x), an ordinary property access on an ordinary local, which closes over
  correctly into a nested fn, is shadowed correctly by an inner binding of the same
  name, and needs nothing from the emitter at all. A mutable field is the same
  access, and set! on a property already works.

  A method that wants JavaScript's `this` after all - an Object method, which the
  host itself calls - binds it with (let* [self (js* \"this\")] ...) in the macro.
  Both kinds of method reach their fields the same way."
  [record?]
  (let [what (if record? "defrecord*" "deftype*")]
    (fn [cenv env form]
      (let [[_ tsym fields self body] form]
        (when-not (simple-symbol? tsym)
          (analysis-error form (str "First argument to " what
                                    " must be a simple symbol, got: " (pr-str tsym))))
        (names/check-own-name! tsym "a type name")
        (when-not (vector? fields)
          (analysis-error form (str what " needs a vector of fields")))
        (when-not (simple-symbol? self)
          (analysis-error form (str what " needs a symbol to name the object its"
                                    " methods are called on, got: " (pr-str self))))
        (when (> (count form) 5)
          (analysis-error form (str "Too many arguments to " what)))
        (when (some #(= self %) fields)
          (analysis-error form
                          (str "A field cannot be named " self
                               ": that is the name this " what " gives the object"
                               " its methods are called on, and a field reads"
                               " through it.")))
        (let [qname (symbol (str env/*current-ns*) (str tsym))
              ^Namespace ns (env/cljs-ns cenv)
              ^Var v  (.intern ns tsym)
              bs     (field-bindings env (into (vec fields)
                                               (when record? record-fields)))
              env'   (-> (not-tail env)
                         (dissoc :top-level?)
                         (update :locals into
                                 (map (fn [b] [(:name b) (assoc b :self self)]))
                                 bs))]
          ;; :file beside the position, for the same reason parse-def records it: a
          ;; type is a definition somebody asks to be taken to.
          ;;
          ;; THE POSITION IS THE NAME'S, and the form's only if the name has none.
          ;; deftype* is written by a macro and carries no metadata of its own -
          ;; cljs.core's deftype builds the form out of `do` and syntax-quote,
          ;; neither of which copies &form's - while the type symbol inside it is
          ;; the one the reader read, vary-meta'd rather than rebuilt. Taking the
          ;; form's first would have given every type a file and line 1, which
          ;; reads like a position and is not one.
          (alter-meta! v merge
                       (select-keys (if (seq (meta tsym)) (meta tsym) (meta form))
                                    [:line :column :end-line :end-column])
                       (when *source-file* {:file *source-file*})
                       {:type true :record record?
                        :fields (mapv :name bs)})
          (cond-> {:op :deftype :form form :env env
                   :name qname
                   :record? record?
                   :fields bs
                   :var {:op :var :name qname :ns env/*current-ns*
                         :form tsym :env env}
                   :children [:var :fields]}
            body (assoc :body (analyze cenv env' body)
                        :children [:var :fields :body])))))))

(defn- parse-quote
  "(quote x), for anything at all.

  Nothing here has to walk x, and that is the point of a quote: a quoted
  collection is a CONSTANT, not a literal - none of its elements evaluates - so
  the whole structure travels as one :const node and the emitter builds it in one
  expression (see clojure.cljs.emitter/const-js). The collection literals below
  are the other half of the same story, and the half that needs children.

  A quoted symbol still emits the placeholder a keyword does: cljs.core/Symbol
  and cljs.core/Keyword are real types now, but a program cannot allocate one
  until cljs.core RUNS, and it does not yet (doc/cljs-compiler.md §5.7)."
  [cenv env form]
  (when (not= 2 (count form))
    (throw (ex-info "Wrong number of args to quote" {:form form})))
  {:op :quote :form form :env env :literal? true
   :expr (assoc (const-node env (second form)) :literal? true)
   :children [:expr]})

(defn- var-meta-form
  "The metadata map `(var foo)` carries at RUNTIME, as a form to be analysed.

  cljs.analyzer builds the same map (analyzer.cljc:1663) and the shape is its own,
  not something we get to choose: cljs.core/meta on a Var reads this map, and
  cljs.test reaches into it for :test and :line to find and order the tests in a
  namespace. Every value is quoted, because these are compile-time facts being
  shipped as data - :name is the SIMPLE name, and :ns the namespace symbol.

  :test is the exception and is not a constant: it reads the property `def` set on
  the var's value, so that a var redefined without a test loses it."
  [^Var v qname]
  (let [m (meta v)]
    (merge
     ;; user metadata first, so a :doc or :arglists the def wrote wins over
     ;; nothing and the keys below win over a user :name
     (zipmap (keys m) (map #(list 'quote %) (vals m)))
     {:ns       (list 'quote (symbol (namespace qname)))
      :name     (list 'quote (symbol (name qname)))
      :doc      (:doc m)
      :file     (list 'quote (:file m))
      :line     (list 'quote (:line m))
      :column   (list 'quote (:column m))
      :test     (list 'when qname (list '. qname '-cljs$lang$test))
      :arglists (list 'quote (let [a (:arglists m)]
                               (if (= 'quote (first a)) (second a) a)))})))

(defn- parse-var
  "(var foo) - the Var OBJECT, not the value in it.

  Three pieces, and cljs.compiler puts them together as
  `new cljs.core.Var(function(){return foo;}, 'ns/foo, {...})`
  (compiler.cljc:504): a thunk that reads the var, so the Var stays live across a
  redefinition rather than closing over a value; the qualified symbol; and the
  metadata map above. All three are analysed here as ordinary nodes, so the
  emitter needs no knowledge of any of them - which is the same bargain the
  collection literals struck (§5.7).

  IT COULD NOT LAND BEFORE M5. cljs.core/Var is a type core.cljs defines, the
  symbol is an allocation of cljs.core/Symbol (§5.10), and the metadata map is a
  cljs.core map (§5.7) - so `var` is a CONSEQUENCE of the core library rather than
  a prerequisite for it, which is what §4.1 predicted and §5.6 checked.

  :locals is dropped before the symbol is resolved, and cljs.analyzer drops it in
  the same place for the same reason: in (let [x 1] (var x)) the var meant is the
  one x names as a VAR, and a local of that name is not it."
  [cenv env form]
  (when (not= 2 (count form))
    (analysis-error form "Wrong number of args to var"))
  (let [sym (second form)]
    (when-not (symbol? sym)
      (analysis-error form (str "Argument to var must be a symbol, got: " (pr-str sym))))
    (let [env' (dissoc env :locals)
          vnode (analyze cenv env' sym)]
      (when-not (= :var (:op vnode))
        (analysis-error form (str "Argument to var must name a var, and " sym
                                  " is " (name (:op vnode)))))
      (let [qname (:name vnode)
            ^Var v (env/resolve-var cenv sym)]
        {:op :the-var :form form :env env
         :var  vnode
         :sym  (analyze cenv env' (list 'quote qname))
         :meta (analyze cenv env' (var-meta-form v qname))
         :children [:var :sym :meta]}))))

(defn- parse-letfn
  "(letfn* [f (fn* ...) g (fn* ...)] body...) - like let*, except every binding is
  in scope in every init, so the functions can call each other.

  A deliberate departure from cljs.analyzer, which binds each name to its OUTER
  meaning while analysing that name's own init (analyzer.cljc:2432, the :shadow
  reduce). A self-call inside f therefore resolves to a var there rather than to f,
  and emits a namespace reference - so (letfn [(f [] (f))] ...) does not recur.
  Clojure's letfn is self-recursive, and emitting a var reference for a local name
  is a silent wrong answer, so ours is in scope in its own init. Mutual recursion
  is analysed identically by both."
  [cenv env form]
  (let [[_ bindings & body] form]
    (when-not (and (vector? bindings) (even? (count bindings)))
      (throw (ex-info "letfn* requires a vector of an even number of forms"
                      {:form form})))
    (let [pairs (partition 2 bindings)
          nodes (mapv (fn [[sym _]] (binding-node env sym :letfn)) pairs)
          env'  (update env :locals into (map (juxt :name identity)) nodes)
          nodes (mapv (fn [node [_ init]]
                        (assoc node :init (analyze cenv (not-tail env') init)
                               :children [:init]))
                      nodes pairs)]
      {:op :letfn :form form :env env
       :bindings nodes
       :body (parse-do cenv env' (cons 'do body))
       :children [:bindings :body]})))

(defn- case-test-node [cenv env form t]
  (let [n (analyze cenv env t)]
    (when-not (and (= :const (:op n)) ((some-fn number? string? char?) (:val n)))
      (throw (ex-info (str "case* tests must be numbers, strings or characters, got "
                           (pr-str t))
                      {:form form})))
    {:op :case-test :form (:form n) :env env :test n :children [:test]}))

(defn- case-label
  "What `t` is as a JAVASCRIPT case label, for the distinctness check below.

  Two Clojure constants can be one label, and then the second branch is
  unreachable rather than ambiguous. Two ways that happens: 1 and 1.0 are one
  JavaScript number, and \\a and \"a\" are one JavaScript string, because a
  ClojureScript character IS a one-character string (§5.7)."
  [t]
  (cond (number? t) (double t)
        (char? t)   (str t)
        :else       t))

(defn- parse-case
  "(case* sym tests thens default), where tests are grouped in vectors: one group
  per branch, since several constants can share a branch.

  The `case` macro binds a local and hands the symbol over, which is why the test
  is a symbol rather than an expression. Numbers, strings and characters, which is
  cljs.analyzer's list too (analyzer.cljc:1884) - a character is a one-character
  string in ClojureScript, so it is a string label like any other.

  A branch is a tail position, so recur may appear there - only the test may not."
  [cenv env form]
  (let [[_ sym tests thens default] form
        env' (not-tail env)]
    (when-not (symbol? sym)
      (throw (ex-info "case* must switch on a symbol" {:form form})))
    (when-not (and (vector? tests) (every? vector? tests))
      (throw (ex-info "case* tests must be grouped in vectors" {:form form})))
    (when-not (every? seq tests)
      (throw (ex-info "a case* branch needs at least one test" {:form form})))
    (when-not (= (count tests) (count thens))
      (throw (ex-info "case* needs one branch per group of tests" {:form form})))
    ;; JavaScript takes the first matching label, so a repeated constant would
    ;; make a later branch unreachable rather than ambiguous. Clojure's case
    ;; refuses duplicate tests; so does this. cljs.analyzer does not - it accepts
    ;; even [[1] [1]] - so there is no model to copy here and the check is ours.
    ;;
    ;; Distinct in CLOJURESCRIPT, which is what case-label answers: 1 and 1.0 are
    ;; two Clojure constants and one JavaScript number, and \a and "a" are two
    ;; Clojure constants and one JavaScript string. Either way the second `case`
    ;; label is the same as the first and its branch is unreachable. Comparing
    ;; with = alone let exactly that through.
    (let [all (map case-label (apply concat tests))]
      (when-not (or (empty? all) (apply distinct? all))
        (throw (ex-info "case* tests must be distinct" {:form form}))))
    {:op :case :form form :env env
     :test (analyze cenv env' sym)
     :nodes (mapv (fn [group then]
                    {:op :case-node :env env
                     :tests (mapv #(case-test-node cenv env' form %) group)
                     :then (let [n (analyze cenv env then)]
                             {:op :case-then :form (:form n) :env env
                              :then n :children [:then]})
                     :children [:tests :then]})
                  tests thens)
     :default (analyze cenv env default)
     :children [:test :nodes :default]}))

(defn- libspec
  "One entry of a :require / :use / :require-macros list, as [target opts].

  The target is a SYMBOL for a namespace and a STRING for a JavaScript module -
  [\"react\" :as React] - which is the one place those two worlds are told apart,
  and the reason they can be: a namespace name is a symbol everywhere else in
  Clojure, so a string in that position can only mean the other thing. It is
  ClojureScript's own spelling and shadow-cljs's, so a file written for either
  reads here unchanged."
  [kind spec]
  (cond
    (symbol? spec) [spec {}]
    (string? spec) [spec {}]

    (and (vector? spec) (or (symbol? (first spec)) (string? (first spec)))
         (even? (count (rest spec))))
    [(first spec) (apply hash-map (rest spec))]

    :else
    (analysis-error
     spec
     (str "Bad " kind " spec: " (pr-str spec)
          ". Write a namespace name, or [namespace :as alias :refer [...]],"
          " or [\"module\" :as alias] for a JavaScript module."
          ;; the shape of the mistake, named: a prefix list is what someone
          ;; reaching for Clojure's ns writes, and ClojureScript has never had them
          (when (and (vector? spec) (some coll? (rest spec)))
            " ClojureScript has no prefix lists - write each namespace in full.")))))

(defn- alias-only?
  "Is this libspec's ONLY option :as-alias?

  The whole of what :as-alias means. `[made.up.lib :as-alias lib]` registers an
  alias and requires NOTHING: the namespace need not exist, is not compiled, and
  gets no import - the alias is there so that ::lib/foo and `lib/foo have a name
  to expand to. Clojure 1.11 added it for exactly that, and ClojureScript 1.11
  followed.

  A spec that asks for anything ELSE beside it is an ordinary require whose alias
  happens to be spelled :as-alias, because the other thing it asked for - a
  :refer, an :as - is a use of the namespace and cannot be served without it.
  Clojure's rule, in Clojure's words: a load occurs unless the libspec has only
  :as-alias.

  Asked in two places that must agree - ns-form-deps, so a driver does not go
  looking for made/up/lib.cljs, and plan-require, so nothing is added to this
  namespace's requires - which is why it is a predicate here rather than a
  condition written twice."
  [opts]
  (= #{:as-alias} (set (keys opts))))

(defn- check-opts!
  [kind target opts allowed]
  (doseq [k (keys opts)]
    (when-not (contains? allowed k)
      (analysis-error opts
                      (str "Unsupported option " k " in " kind " of " target
                           ". Handled here: "
                           (clojure.string/join ", " (sort allowed)) "."))))
  opts)

(defn- add-alias!
  [cenv this-ns target as]
  (when as
    (when-not (simple-symbol? as)
      (analysis-error as (str ":as must be a simple symbol, got " (pr-str as))))
    ;; An alias is a Clojure-side name only - what reaches JavaScript is
    ;; names/ns-alias of the TARGET - so it needs no JavaScript spelling and gets
    ;; no check for one. Namespace.addAlias refuses a second, different target for
    ;; a name already aliased, which is the check that matters.
    (.addAlias ^Namespace (env/cljs-ns cenv this-ns) as
               ^Namespace (env/cljs-ns cenv target))))

(defn- check-alias!
  [as]
  (when (and as (not (simple-symbol? as)))
    (analysis-error as (str ":as must be a simple symbol, got " (pr-str as))))
  as)

(defn- macro-self-ns?
  "Whether `target` said its macros live in the JVM namespace of its own name.

  A .cljc that is both a runtime namespace and a macro namespace says so by
  requiring itself for macros, which cljs.test does, and which is the whole of the
  condition cljs.analyzer calls macro-autoload-ns?.

  CLJS.CORE IS ONE WITHOUT SAYING SO, and it is the only one. Its ns form does not
  require itself for macros - cljs/core.cljs asks for five goog namespaces and
  nothing else - because it does not have to: every namespace gets cljs.core's
  macros through :core-macros, which is the macro half of the implicit require
  (doc/cljs-compiler.md §5.12). That is the same fact this predicate asks about,
  arrived at through the mechanism rather than through the ns form, so the answer
  is yes. (:require [cljs.core :refer [await]]) is what needs it - `await` is a
  macro at core.cljc:1036 and nothing at all in core.cljs."
  [cenv target]
  (or (= 'cljs.core target)
      (contains? (env/declared-macro-requires cenv target) target)))

(defn- split-refers!
  "The names a :refer asks for, split into the VARS of `target` and the MACROS of
  the JVM namespace beside it - and an error for a name that is neither. Returns
  [vars macros].

  A :REFER MAY NAME A MACRO, which is why this splits rather than checks. `is` and
  `deftest` are macros in cljs/test.cljc and nothing at all in cljs/test.cljs, and
  ClojureScript's own tests write (:require [cljs.test :refer [deftest is]]) with
  no :refer-macros anywhere - three of their test namespaces would not compile
  without it. cljs.analyzer reaches the same answer by a longer route: it lets the
  refer through, discovers the missing var afterwards, and moves the name from
  :uses to :use-macros (check-use-macros-inferring-missing).

  ONLY WHERE THE TARGET SAID SO, which is macro-self-ns?. Without that condition a
  JVM namespace that merely happens to be loaded under the same name would answer
  for a ClojureScript one, and a typo in a :refer would resolve to something the
  program never asked for.

  Asking creates the target namespace if it is absent, which is inert: an empty
  namespace nothing requires is unreachable, and requiring is what would make it
  reachable."
  [cenv kind target syms also]
  (when-not (or (nil? syms)
                (and (sequential? syms) (every? simple-symbol? syms)))
    (analysis-error syms (str kind " of " target
                              " takes a sequence of simple symbols, got "
                              (pr-str syms))))
  ;; `also` is the sources of a :rename, checked HERE and validated by
  ;; check-renames! rather than by the line above - the message there is about
  ;; :rename and this one is about :refer, and a bad :rename must not be reported
  ;; as a bad :refer.
  (let [syms (into (vec syms) (remove (set syms)) also)
        ^Namespace from (env/cljs-ns cenv target)
        ^Namespace jns  (when (macro-self-ns? cenv target) (find-ns target))]
    (reduce
     (fn [[vars macros] sym]
       (let [mv (when jns (.findInternedVar jns sym))]
         (cond
           (.findInternedVar from sym)   [(conj vars sym) macros]
           (and mv (.isMacro ^Var mv))   [vars (conj macros sym)]
           :else
           (analysis-error
            sym
            (str "Cannot refer " sym " from " target ": no such var there"
                 (if jns
                   (str ", and no such macro in " target " either.")
                   (str ". " target " does not keep its macros in a JVM namespace"
                        " of its own name, so a :refer there names a var and only"
                        " a var - write :refer-macros for a macro."))
                 " Requiring a namespace does not compile it yet (M3 owns source"
                 " resolution), so a namespace referred out of has to have been"
                 " analysed already.")))))
     [[] []]
     syms)))

(defn ns-form-deps
  "The ClojureScript namespaces an ns form requires, in the order written.

  What a compilation driver needs before it can analyse the form: the requires have
  to be compiled first, and finding out which they are cannot wait for parse-ns,
  which is what needs them compiled. Only the runtime side - :require-macros names
  a JVM namespace, which the classpath resolves and which nothing here compiles.

  Shares libspec with parse-ns rather than re-reading the grammar, so a spec shape
  one accepts is a spec shape the other sees.

  goog is NOT in here, and :import is not read at all. A Closure namespace has no
  .cljs to find and nothing to compile - it is written out whole by
  clojure.cljs.goog, before anything is compiled - so a driver that saw one would
  go looking for goog/object.cljs on the source path and fail. It still reaches the
  emitted module's imports, because those come from env/requires rather than from
  here."
  [form]
  (when (and (seq? form) (= 'ns (first form)))
    (vec (distinct (for [ref  (rest form)
                         :when (and (sequential? ref)
                                    (#{:require :use} (first ref)))
                         spec (rest ref)
                         :let [[target opts] (libspec (first ref) spec)]
                         ;; :as-alias alone is NOT a dependency - see alias-only?.
                         ;; cljs/ns_test/foo.cljs writes [made.up.lib :as-alias lib]
                         ;; and there is no made/up/lib.cljs anywhere, which is the
                         ;; point of the test.
                         ;; A STRING IS NOT IN HERE EITHER, and for goog's reason
                         ;; one world over: a JavaScript module has no .cljs to
                         ;; find, is not compiled, and is fetched from npm/ rather
                         ;; than emitted. It reaches the module's imports through
                         ;; env/js-requires, as goog reaches them through
                         ;; env/requires.
                         :when (not (or (string? target)
                                        (goog/goog-ns? target)
                                        (alias-only? opts)))]
                     target)))))

(defn closure-ns?
  "Is `target` a CLOSURE namespace here - one whose implementation is a JavaScript
  file the compiler converts, rather than a ClojureScript file it compiles?

  Two kinds. A `goog.` name, which is syntactic and reserved; and a Closure-style
  JavaScript file sitting on the classpath at the name's own path -
  com.cognitect.transit out of transit-js's jar, shadow.loader out of shadow-cljs's.
  After this line the two are one thing: both are converted by clojure.cljs.goog,
  both register their provide into $CLJS.namespaces, and a var in either is a
  property of the object $ns hands back.

  A NAMESPACE THAT HAS BEEN DECLARED IS NOT ONE, whatever sits on the classpath
  beside it. That is what gives a .cljs precedence over a .js of the same name
  without anyone having to rule on the ambiguity: by the time an ns form is
  analysed, a compilation driver has already compiled everything it requires
  (driver/ensure!), so a namespace with a source has an ns form behind it and
  answers false here. env/declared? is that question and is asked FIRST, before the
  classpath is touched - which is also what keeps this cheap enough to ask about
  every require and every qualified symbol's prefix.

  Public because clojure.cljs.driver asks it of a namespace it could not find a
  source for, and the two must agree."
  [cenv target]
  (or (goog/goog-ns? target)
      (and (not (env/declared? cenv target)) (goog/js-ns? target))))

(defn js-module-ns?
  "Is `target` - a bare SYMBOL in a require - the name of a JavaScript module
  rather than of a ClojureScript namespace?

  shadow-cljs's spelling. A project written against it says

      (:require [react :as React] [react :refer [useRef]] [clipboard-polyfill])

  where upstream says [\"react\" :as React], and both are read here for the reason
  the three options of a string require are shadow's three: a project moving between
  the two compilers should not have to rewrite its ns forms. See
  doc/cljs-compiler.md 5.53.

  Three questions, cheapest first, and each is doing something.

  COULD IT BE A SPECIFIER AT ALL - output/symbol-specifier, which is syntactic and
  answers no for anything with a dot in it. That is what makes this free to ask
  about every require in every ns form, and it is also what keeps `Could not locate
  nosco/colours.cljs` as the answer for a namespace that is missing rather than for
  a package that is not.

  HAS IT BEEN DECLARED - a one-segment name may perfectly well be a ClojureScript
  namespace, and a source wins. env/declared? is the same question closure-ns? asks
  and answers by the same arrangement: by the time an ns form is analysed, a
  compilation driver has compiled everything it requires (driver/ensure!), so a
  namespace with a source has an ns form behind it.

  IS IT A CLOSURE FILE - because that is the other way to be a namespace with no
  .cljs, and a file that is actually on the classpath beats a package that may or
  may not be in somebody's node_modules.

  Public because clojure.cljs.driver and clojure.cljs.repl ask it too, and the
  three must agree."
  [cenv target]
  (and (symbol? target)
       (some? (output/symbol-specifier target))
       (not (env/declared? cenv target))
       (not (goog/closure-ns? target))))

(defn- check-goog-require!
  "A (:require [goog.object :as gobject]) entry, checked. A classpath Closure file -
  (:require [com.cognitect.transit :as t]) - passes through here too, and the rules
  are the same rules: it is JavaScript either way.

  Two things are refused rather than passed through. A Closure name we do not
  have, because the alternative is a module import for a file that is not there and
  a 404 at load; and the macro options, because there is no JVM namespace called
  goog.object.

  :REFER IS NOT ONE OF THEM ANY MORE, and what changed is not the fact it was
  refused over. A Closure var is still not a Var, and a Namespace still has nowhere
  to put one - that was true and stays true. What it stopped being is a reason,
  because this compiler now refers names that are not Vars all the time: a
  (:require [\"react\" :refer [useState]]) is exactly a bare name standing for a
  JavaScript property, and env/js-refers is where it lives precisely because a
  Namespace could not hold it (5.51). Once that map exists the goog side has no
  argument left of its own, and the refusal was costing a real program the whole of
  lambdaisland.deep-diff2 for one #?(:cljs [goog.string :refer [format]]).

  So a referred name is checked here the way the QUALIFIED spelling would be
  checked where it was written, and for the same reasons - the ns form is where the
  name was asked for, so the ns form is where a mistake should surface. Returns
  {name qualified-name}, which is what the resolver needs and all it needs; see
  env/goog-refers."
  [spec target refers renames macros]
  (when-not (goog/provided? target)
    (analysis-error
     spec
     (if goog/*closure-library*
       (str "No such Closure namespace: " target
            ". The Closure Library on the classpath does not provide it.")
       (str "No such Closure namespace: " target ". This fork ships a SUBSET of the"
            " Closure Library - " (clojure.string/join ", " (sort (keys (goog/index))))
            ". To get the rest: " (goog/get-real-closure)))))
  (when macros
    (analysis-error
     spec
     (str target " is a Closure namespace, so :include-macros / :refer-macros have"
          " nothing to reach - those name a JVM namespace of the same name.")))
  ;; A RENAME IS A REFER UNDER ANOTHER NAME, the same as everywhere else - so the
  ;; two are one list here, keyed by what THIS namespace will call each one, and a
  ;; renamed name is not also referred under its own. Until now :rename was in the
  ;; option set a Closure require accepts and was read by nothing, which is the
  ;; quiet half of the same gap: (:require [goog.string :rename {format fmt}])
  ;; compiled and gave you nothing.
  (let [named   (concat (map (fn [r] [r r]) (remove (set (keys renames)) refers))
                        (map (fn [[from to]] [to from]) renames))
        refers  (into {} (map (fn [[here there]]
                                [here (symbol (str target) (str there))]))
                      named)]
    (doseq [[_ there] refers]
      ;; The provide branch of analyze-qualified-symbol answers first, and a
      ;; provide needs no further checking - goog.string.format is a file the
      ;; output tree will hold. Everything else is a property of a namespace
      ;; object, unchecked exactly as gobject/get is, EXCEPT in the three
      ;; namespaces this fork reduced, where we do have the list and a missing
      ;; name is missing because we removed it (goog/reduced-vars).
      ;;
      ;; Asked HERE as well as at the use, because a refer names a var in the ns
      ;; form and a mistake there should not wait for the first call. Both places
      ;; ask the same function and get the same sentence.
      ;; the DOTTED spelling for the provide question and the slashed one for the
      ;; var: a provide is one name, and goog.string.format is not goog.string's
      ;; `format` (5.18). analyze-qualified-symbol splits the same two readings
      ;; the same way, and this is that line said once earlier.
      (when-not (goog/provided? (symbol (str target "." (name there))))
        (goog/check-var! (str target) (name there))))
    refers))

(defn clj-ns->cljs-ns
  "clojure.foo -> cljs.foo. Any other name unchanged.

  ClojureScript's function of the same name (analyzer.cljc:3264). Public because
  the driver asks the same question of a source path that this namespace asks of
  the namespaces it has analysed - see aliased-clj-ns."
  [sym]
  (let [s (str sym)]
    (if (or (= "clojure" s) (clojure.string/starts-with? s "clojure."))
      (symbol (str "cljs" (subs s (count "clojure"))))
      sym)))

(defn aliased-clj-ns
  "The cljs.* namespace `target` stands for, or nil if it stands for itself.

  (:require [clojure.test :refer [deftest is]]) is how three of ClojureScript's
  own test namespaces open, and there is no clojure/test.cljs anywhere - not here
  and not in ClojureScript. THE clojure.* NAME IS AN ALIAS FOR THE cljs.* ONE
  wherever the first does not exist and the second does, so that a namespace which
  differs from Clojure's only in where it lives can be reached by the name a reader
  of Clojure would reach for. clojure.string and clojure.set are the other half of
  that rule and are NOT aliased: both exist under their own names, and the rule
  fires only where nothing does.

  Whether it exists is asked of what has been ANALYSED, not of the source path,
  and that is the whole of the difference from ClojureScript. Theirs is
  aliasable-clj-ns?, which stats the classpath, because parse-ns is the only place
  that decides. Here the decision is already made twice over: a driver has to find
  a file for every dependency before this runs, so by the time a spec is planned
  the question `is there a clojure.test?` has an answer that cost nothing - and the
  driver, which does hold the source paths, answers the same question the same way
  for itself (driver/ensure!). Neither half has to reach into the other's evidence.

  declared? rather than existence: add-require! creates a namespace on being named,
  so existence would say only that somebody mentioned the name.

  PUBLIC BECAUSE A REPL'S require ASKS IT TOO, and asks it for a third reason.
  The two above are about NAMES - what a spec means, and what a driver goes
  looking for. clojure.cljs.repl/do-require asks about a FILE: having compiled
  what was typed, it has to tell the runtime which module to fetch, and
  ns/clojure/math.js is not where cljs/math.cljs was written. Reading the rule off
  `declared?` a second time in repl.clj would be the same three conditions in
  another file, and the one that drifted would be the one nobody re-read."
  [cenv target]
  (let [alt (clj-ns->cljs-ns target)]
    (when (and (not= alt target)
               (not (env/declared? cenv target))
               (env/declared? cenv alt))
      alt)))

(defn- check-renames!
  "The :rename map of a :require or :use, checked. {from to}, where `from` is a
  name in the TARGET and `to` is what this namespace calls it.

  A rename is a refer under another name, and the name it replaces is NOT also
  referred: (:require [cljs.core :refer [await] :rename {await aw}]) gives this
  namespace `aw` and not `await`. cljs.analyzer computes the same set, as
  referred-without-renamed - a rename whose source stayed referred would put two
  names on one var and make :exclude-by-renaming impossible.

  The source does not have to appear in :refer at all; naming it in :rename is
  enough to ask for it. That is ClojureScript's reading and it is the useful one -
  :refer [x] :rename {x y} and :rename {x y} mean the same thing, so neither
  spelling is a trap."
  [rename]
  (when-not (or (nil? rename)
                (and (map? rename)
                     (every? simple-symbol? (keys rename))
                     (every? simple-symbol? (vals rename))))
    (analysis-error rename (str ":rename takes a map of simple symbols, got "
                                (pr-str rename))))
  (when (not= (count rename) (count (set (vals rename))))
    (analysis-error rename (str ":rename gives one name to two vars: "
                                (pr-str rename))))
  (or rename {}))

(def ^:private js-export-re
  "One JavaScript identifier - the shape an export name has to have once spelled
  the host's way. js-path-re below is the same thing with dots allowed, and the
  difference is the point: an export is a single property of a module object."
  #"^[A-Za-z_$][A-Za-z0-9_$]*$")

(defn- check-js-export!
  "`sym` is a name a string require asks to be given, so it has to be a simple
  symbol AND to spell a property a JavaScript module could export.

  Unchecked beyond that, and it cannot be otherwise: a JavaScript file is never
  analysed here, so which names it exports is not a question this compiler can
  ask. Exactly the position a goog var is in (goog-var-node), and the same answer -
  a name that is not there surfaces when it runs."
  [spec sym what]
  (when-not (simple-symbol? sym)
    (analysis-error spec (str what " takes a simple symbol, got " (pr-str sym))))
  (when-not (re-matches js-export-re (names/host-name (name sym)))
    (analysis-error spec (str "Cannot draw " sym " out of a JavaScript module: it"
                              " spells " (names/host-name (name sym))
                              ", which is not a name there.")))
  sym)

(defn- split-js-specifier
  "\"date-fns/sub$default\" -> [\"date-fns/sub\" \"default\"], and \"react\" ->
  [\"react\" nil]. `spec` is the whole libspec, so that a bad one is reported
  against what was written.

  THE $ NAMES A PATH INTO THE MODULE, and nothing after it is part of any file
  name: a $ specifier is ONE import of the module half, and the path is a property
  read off the object that import bound. \"date-fns/sub$default\" and
  \"date-fns/sub\" in the same ns form are one import between them.

  SPLIT HERE AND NOWHERE ELSE, which is what the sugar costs. The plan this
  function feeds carries the two halves apart, so clojure.cljs.env, the emitter,
  the output layout, the driver and the missing-package report each go on seeing a
  module and only a module - one specifier, one file, one binding, as before. A $
  reaching clojure.cljs.output/js->path is a bug, and is refused there as one.

  AT THE FIRST $, which is shadow-cljs's rule (shadow.build.js-support splits with
  a limit of 2) rather than ClojureScript's, whose lib&sublib regex is greedy and
  takes the LAST. The two agree on every specifier with one $ in it and disagree
  on a$b$c; the first $ is the one that can be the delimiter, because $ is legal
  in a JavaScript property name and not in a package name. See doc/cljs-npm.md §4.1.

  Beyond the split this is the check js->path is for the other half: what follows
  the $ has to be a dotted path of names JavaScript could have, because that is
  what it is emitted as."
  [spec specifier]
  (if-not (and (string? specifier) (clojure.string/includes? specifier "$"))
    [specifier nil]
    (let [[module path] (clojure.string/split specifier #"\$" 2)]
      (when (clojure.string/blank? module)
        (analysis-error spec (str "Bad JavaScript module specifier: "
                                  (pr-str specifier) " - a $ names something"
                                  " inside a module, and there is no module"
                                  " before it.")))
      (when (clojure.string/blank? path)
        (analysis-error spec (str "Bad JavaScript module specifier: "
                                  (pr-str specifier) " - a $ names something"
                                  " inside a module, and there is nothing after"
                                  " it. Drop the $ to require the module.")))
      ;; NOT MUNGED, where a :refer of the symbol some-fn is: a specifier is a
      ;; string, and a string in an ns form is spelled the host's way from end to
      ;; end - which is why it can hold a /, an @ and a . without any of them
      ;; meaning what they mean in a symbol.
      (doseq [segment (clojure.string/split path #"\." -1)]
        (when-not (re-matches js-export-re segment)
          (analysis-error spec (str "Cannot read " (pr-str path) " out of "
                                    (pr-str module) ": " (pr-str segment)
                                    " is not a name in JavaScript, and what"
                                    " follows a $ is spelled the way JavaScript"
                                    " spells it."))))
      [module path])))

(defn- js-export-path
  "Where `export` sits relative to the module object: \"useState\" on its own, and
  \"default.useState\" when the specifier's $ path put something between them.

  One function because every option goes through it - :refer, :default and the
  export half of :rename all name something inside whatever the specifier named,
  and the specifier is free to have named a property rather than the module."
  [path export]
  (if path (str path "." export) export))

(defn- plan-js-require
  "One (:require [\"react\" :as React :refer [useState] :default React]) entry,
  checked and turned into what applying it needs. Changes nothing.

  Three options, and they are shadow-cljs's three because a project moving between
  the two compilers should not have to rewrite its ns forms:

    :as       names the module, so React/createElement is a property of it
    :refer    names exports, so useState is a bare name in this namespace
    :default  names the export called `default`, which is what a CommonJS package
              bundled to ESM puts its single value on

  AND A FOURTH THING THAT IS NOT AN OPTION: a $ in the specifier, which names a
  property path into the module and which the three options above then apply to.
  [\"date-fns/sub$default\" :as sub] binds sub to the default export, and is
  shadow-cljs's spelling of what [\"date-fns/sub\" :default sub] says with an
  option. Both are accepted, because a project moving between the two compilers
  should not have to rewrite its ns forms - which is the same reason the three
  options are shadow's three. split-js-specifier is the whole of it.

  :rename renames a :refer, as it does for a namespace - a refer under another
  name, and the name it replaces is not also referred (check-renames!). The map is
  built here rather than by that function because there is no var to check.

  WHAT IS REFUSED, each because it means nothing rather than because it is
  unsupported. :use, which needs :only and whose whole point is referring vars.
  :as-alias, which registers a Clojure-side name for a namespace that need not
  exist - a module is not a namespace and has no ::keyword to expand. And the
  macro options, which name a JVM namespace: there is no react.clj.

  A SPECIFIER IS CHECKED BY THE THING THAT TURNS IT INTO A FILE, which is
  clojure.cljs.output/js->path - called here for its preconditions, the way
  parse-ns calls names/ns-alias for its own, and called on the MODULE half
  because that is the half that becomes a file. A mistake in it is then reported
  against the ns form that holds it rather than at emission."
  [kind spec]
  ;; `written` is the specifier as the ns form spells it, which is what an error
  ;; about the SPEC should echo; `specifier` below is its module half, which is
  ;; what everything downstream is told.
  (let [[written opts] (libspec kind spec)]
    (when (= kind :use)
      (analysis-error spec (str "Cannot :use " (pr-str written)
                                ": a JavaScript module has no vars to refer."
                                " Write :require with :refer.")))
    ;; BEFORE check-opts!, which would refuse it as merely unsupported: it is one
    ;; of the two options a namespace has and a module cannot, so it gets the
    ;; sentence that says which.
    (when (contains? opts :as-alias)
      (analysis-error spec (str "Cannot :as-alias " (pr-str written)
                                ": :as-alias names a namespace that need not"
                                " exist, and a JavaScript module is not a"
                                " namespace. Write :as.")))
    (check-opts! kind written opts #{:as :refer :default :rename})
    (check-alias! (:as opts))
    (let [[specifier path] (split-js-specifier spec written)
          refer  (:refer opts)
          rename (or (:rename opts) {})]
      (when-not (or (nil? refer) (and (sequential? refer) (every? symbol? refer)))
        (analysis-error spec (str ":refer takes a vector of symbols, got "
                                  (pr-str refer))))
      (when-not (and (map? rename) (every? simple-symbol? (mapcat identity rename)))
        (analysis-error spec (str ":rename takes a map of simple symbols, got "
                                  (pr-str (:rename opts)))))
      (doseq [[from _] rename]
        (when-not (some #{from} refer)
          (analysis-error spec (str ":rename names " from ", which is not in"
                                    " :refer " (pr-str (vec refer)) "."))))
      (output/js->path specifier)
      (when-let [d (:default opts)] (check-js-export! spec d :default))
      (run! #(check-js-export! spec % :refer) refer)
      {:specifier specifier
       ;; the $ half, kept beside the module rather than folded into it: what an
       ;; alias names is the module when this is nil and a property of it when it
       ;; is not, and that is the only thing downstream has to know about the sugar
       :path path
       :as (:as opts)
       ;; {name export}, where the export is what JavaScript calls it and the name
       ;; is what this namespace calls it. A rename moves the key and leaves the
       ;; export where it was, which is the whole of what renaming means.
       :refers (into (if-let [d (:default opts)]
                       {d (js-export-path path "default")} {})
                     (map (fn [sym] [(get rename sym sym)
                                     (js-export-path path (name sym))]))
                     refer)})))

(defn- plan-ns-require
  "One (:require ...) or (:use ...) entry naming a NAMESPACE, checked and turned
  into what applying it needs. Changes nothing.

  :as and :refer are the ClojureScript side; :include-macros and :refer-macros
  reach the JVM namespace of the same name, which is how a .cljs file gets at the
  macros defined beside it.

  AND SO, WITHOUT BEING ASKED, DOES A REQUIRE OF A NAMESPACE THAT KEEPS ITS MACROS
  THERE. (:require [cljs.test :as t :refer [deftest]]) reaches cljs/test.cljc for
  both the alias and the refer, because cljs/test.cljs says that is where its
  macros are (macro-self-ns?). ClojureScript does the same in two halves -
  desugar-ns-specs writes the implied :require-macros, and
  check-use-macros-inferring-missing moves the refers into it - and it is one
  feature: a .cljc namespace is one namespace to whoever requires it, whichever
  side of it a name lives on. See doc/cljs-compiler.md 5.17.

  A clojure.* TARGET MAY STAND FOR A cljs.* ONE (aliased-clj-ns), and then the
  name it was written under becomes a second alias for it, so that clojure.test
  and cljs.test both resolve and so does an unqualified refer out of either. See
  doc/cljs-compiler.md 5.20."
  [cenv kind spec]
  (let [[written opts]  (libspec kind spec)
        use?            (= kind :use)
        stands-for      (aliased-clj-ns cenv written)
        target          (or stands-for written)]
    (check-opts! kind target opts
                 (if use?
                   #{:only :rename}
                   #{:as :as-alias :refer :refer-macros :include-macros :rename}))
    (when (and use? (not (contains? opts :only)))
      (analysis-error spec (str ":use of " target " needs :only [...]"
                                " - write :require with :refer instead.")))
    (check-alias! (:as opts))
    (check-alias! (:as-alias opts))
    (let [asked (if use? (:only opts) (:refer opts))]
      (cond
        ;; :as-alias ALONE plans an alias and nothing else - no require, no
        ;; refers, no macro namespace loaded, and the target not checked for
        ;; existence, because it is allowed not to exist. See alias-only?.
        ;;
        ;; `written` rather than `target`: aliased-clj-ns asks whether a cljs.*
        ;; twin was COMPILED, and a namespace that need not exist has none.
        (alias-only? opts)
        {:target written :as (:as-alias opts) :alias-only true}

        ;; A CLOSURE NAMESPACE - goog's tree, or a .js on the classpath at the
        ;; name's own path. Nothing here is compiled, nothing is interned, and
        ;; there are no vars to refer: what the require buys is the alias and the
        ;; import, which apply-ns-require! records the same way it records one for
        ;; a namespace we compiled. See closure-ns? for why a .cljs wins.
        (closure-ns? cenv target)
        (let [macros (when (or (:include-macros opts) (:refer-macros opts))
                       {:target target :as (:as opts) :refers (:refer-macros opts)})]
          ;; :refers rather than :goog-refers would be the shorter spelling and the
          ;; wrong one: apply-ns-require! reads :refers as names to look up in the
          ;; TARGET'S Namespace and intern here, and a Closure namespace has no
          ;; Namespace and no interned anything. The two are different enough to
          ;; deserve different keys - one is a Var mapping, the other is a note
          ;; that a bare name stands for a qualified one.
          {:target target :as (:as opts) :macros macros
           :goog-refers (check-goog-require! spec target asked
                                             (check-renames! (:rename opts)) macros)})

        ;; A RENAMED NAME IS CHECKED LIKE ANY OTHER REFERRED NAME - same split
        ;; into vars and macros, same message when it is neither - and then taken
        ;; back out of the refers, because a rename replaces the name rather than
        ;; adding to it. See check-renames!.
        :else
        (let [renamed (check-renames! (:rename opts))
              ren?    (set (keys renamed))
              [refers inferred] (split-refers! cenv (if use? :only :refer) target
                                               asked (keys renamed))
              rename-of (fn [syms] (into {} (for [s syms :when (ren? s)]
                                              [(get renamed s) s])))
              v-ren   (rename-of refers)
              m-ren   (rename-of inferred)
              refers  (into [] (remove ren?) refers)
              inferred (into [] (remove ren?) inferred)
              self?   (macro-self-ns? cenv target)
              m-refs  (into (vec (:refer-macros opts)) inferred)
              macros  (when (or self? (:include-macros opts) (:refer-macros opts))
                        {:target target :as (:as opts) :refers m-refs
                         :renames m-ren})]
          (when macros
            (env/macro-ns target (into (vec (:refers macros)) (vals m-ren))))
          {:target target :as (:as opts) :also-as (when stands-for written)
           :refers refers :renames v-ren :macros macros})))))

(defn- plan-require
  "One (:require ...) or (:use ...) entry, whichever kind it is.

  A STRING SPEC IS A JAVASCRIPT MODULE and shares nothing with the other but the
  ns form it was written in - no namespace, no alias on a Namespace, no vars to
  refer, no macro side. Told apart here rather than by a branch in each step, so
  that every rule in plan-ns-require can go on being about namespaces.

  AND SO IS A BARE SYMBOL THAT NAMES ONE, which is shadow-cljs's spelling and is
  told apart by js-module-ns? rather than by its shape. It is REWRITTEN into the
  string spelling and handed to the same function, so there is one kind of module
  require from here on and every rule about one goes on being about all of them.
  What the rewrite costs is that an error names the module as \"react\" where the
  ns form said react, and what it buys is that no rule below had to learn a second
  shape.

  THE SYMBOL IS ITSELF A NAME FOR THE MODULE, which is the one thing the two
  spellings do not share. (:require [clipboard-polyfill]) is a whole require in
  nosco-gamma and clipboard-polyfill/write is how it is used - so the symbol
  qualifies names the way a namespace's own name always does, whether or not an
  :as was asked for. When :as was, both work, and :also-as is how the second one
  is carried - the very word and the very mechanism a namespace require already
  uses for the name it was WRITTEN under (see apply-ns-require!)."
  [cenv kind spec]
  (let [target (if (vector? spec) (first spec) spec)]
    (cond
      (string? target) (plan-js-require kind spec)

      (js-module-ns? cenv target)
      (let [specifier (output/symbol-specifier target)
            rest-of   (rest (if (vector? spec) spec [spec]))]
        ;; ALWAYS, even when :as asked for the symbol itself. Guarding that case
        ;; was written here and taken out again: the two names are recorded into a
        ;; map under the same key, so the second write is the first one over again
        ;; and no test could tell the difference. An invariant nothing can observe
        ;; is not one worth a branch.
        (assoc (plan-js-require kind (into [specifier] rest-of))
               :also-as target))

      :else (plan-ns-require cenv kind spec))))

(defn- plan-import
  "One (:import ...) entry: [goog.string StringBuffer], or the class written out as
  goog.string.StringBuffer.

  An :import is a require plus an alias. The require is of the CLASS - Closure
  provides goog.string.StringBuffer as a name in its own right, and base.js
  registers it - and the alias maps the bare name to it, which is what makes
  (StringBuffer.) work. That is exactly what Closure's :import means, and it is
  the one ns reference cljs.core needs that :require cannot express.

  Returns one entry per class, so the two spellings plan the same way."
  [spec]
  (let [entries (cond
                  ;; goog.string.StringBuffer - the class written out, which is what
                  ;; cljs.core writes and what ClojureScript's ns form takes
                  ;; (parse-import-spec). The LAST dot splits the namespace from the
                  ;; class, as it does for a name in code (§5.3).
                  (and (simple-symbol? spec)
                       (clojure.string/includes? (str spec) "."))
                  (let [t (str spec)
                        i (.lastIndexOf t ".")]
                    [[(symbol (subs t 0 i)) (symbol (subs t (inc i)))]])

                  ;; a bare name says which class and not where to find it
                  (simple-symbol? spec)
                  (analysis-error spec
                                  (str "Bad :import spec: " (pr-str spec)
                                       ". An imported class needs a namespace -"
                                       " write goog.string.StringBuffer, or"
                                       " [goog.string StringBuffer]."))

                  ;; goog.string/StringBuffer. A REFERENCE may be spelled with a
                  ;; slash and mean the same class (§5.18); an :import SPEC may not.
                  ;; The ns form is a declaration rather than an expression, and
                  ;; ClojureScript refuses this - "Only lib.ns.Ctor or [lib.ns Ctor*]
                  ;; spec supported in :import" - so taking it would be a spelling
                  ;; that compiles here and nowhere else.
                  (symbol? spec)
                  (analysis-error spec
                                  (str "Bad :import spec: " (pr-str spec)
                                       ". An :import spec is written with a dot,"
                                       " not a slash - write "
                                       (namespace spec) "." (name spec) ", or ["
                                       (namespace spec) " " (name spec) "]."))

                  (and (sequential? spec) (symbol? (first spec)) (next spec))
                  (for [c (rest spec)]
                    (if (simple-symbol? c)
                      [(first spec) c]
                      (analysis-error spec (str "Bad :import spec: " (pr-str spec)
                                                ". " (pr-str c) " is not a class"
                                                " name."))))

                  :else
                  (analysis-error spec
                                  (str "Bad :import spec: " (pr-str spec)
                                       ". Write [goog.string StringBuffer] or"
                                       " goog.string.StringBuffer.")))]
    (for [[ns-part class-sym] entries]
      (let [target (symbol (str ns-part "." class-sym))]
        (when-not (goog/goog-ns? target)
          (analysis-error spec
                          (str "Cannot :import " target
                               ": :import names a CLOSURE class, and this compiler"
                               " has no other kind. Use js/Foo for a JavaScript"
                               " global, and :require for a ClojureScript"
                               " namespace.")))
        (when-not (goog/known? target)
          (analysis-error spec
                          (str "No such Closure class: " target
                               ". This fork ships a subset of the Closure Library,"
                               " and that name is not in it.")))
        {:target target :as class-sym}))))

(defn- invert-renames
  "A :rename map as WRITTEN, {from to}, turned into the {to from} that .refer and
  env/require-macros! take - the same name pair with the two halves apart, so that
  applying a rename is the same call as applying a refer.

  Both directions are in use and neither is arbitrary: the ns form reads `call
  their `from` my `to``, and applying it reads `my `to` is their `from``."
  [renamed]
  (into {} (map (fn [[from to]] [to from])) renamed))

(defn- plan-require-macros
  "One (:require-macros ...) or (:use-macros ...) entry. The target is a real JVM
  namespace, and nothing about it enters the ClojureScript world.

  :rename is the macro-side twin of :require's, and it means what it means there
  (check-renames!): a rename is a refer under another name, and the name it
  replaces is not also referred. cljs/ns_test.cljs writes
  (:require-macros [clojure.core :refer [when when-let]
                                 :rename {when always, when-let always-let}])
  and then checks that `always` expands - so both halves of that spec have to
  reach env/require-macros! together."
  [cenv kind spec]
  (let [[target opts] (libspec kind spec)
        use?          (= kind :use-macros)]
    (check-opts! kind target opts (if use? #{:only :rename} #{:as :refer :rename}))
    (when (and use? (not (contains? opts :only)))
      (analysis-error spec (str ":use-macros of " target " needs :only [...]")))
    (let [renamed (check-renames! (:rename opts))
          asked   (if use? (:only opts) (:refer opts))
          refers  (into [] (remove (set (keys renamed))) asked)
          renames (invert-renames renamed)]
      (check-alias! (:as opts))
      (env/macro-ns target (into refers (vals renames)))
      {:target target :as (:as opts) :refers refers :renames renames})))

(defn- plan-refer-clojure
  "(:refer-clojure :exclude [+ for] :rename {mapv core-mapv}) - the names this
  namespace does NOT take from cljs.core, and the ones it takes under another
  name. Returns {:excludes #{...} :renames {to from}}.

  A :RENAME EXCLUDES ITS SOURCE. cljs.analyzer says so in one line -
  parse-ns-excludes adds (keys renames) to the excludes - and cljs/ns_test.cljs
  checks it: (exists? mapv) is false in a namespace that renamed mapv to
  core-mapv, while (exists? core-mapv) is true. It is the reading :require :rename
  already has here (check-renames!), and that is the point: a rename gives the var
  one name, not two.

  There is no :require of cljs.core to hang this off. Every namespace has its
  names already, through the refer half of the implicit require (5.12), and that
  half is a RULE in env/resolve-var rather than a mapping - so a rename cannot be
  expressed by changing what the require asked for. It is applied as the one
  explicit refer of a cljs.core var this compiler writes; see refer-core-renames!."
  [args]
  (when-not (even? (count args))
    (analysis-error args ":refer-clojure takes keyword/value pairs"))
  (let [opts    (apply hash-map args)
        _       (check-opts! :refer-clojure "the ns form" opts #{:exclude :rename})
        renamed (check-renames! (:rename opts))]
    (when-not (every? simple-symbol? (:exclude opts))
      (analysis-error opts ":refer-clojure :exclude takes simple symbols"))
    {:excludes (into (set (:exclude opts)) (keys renamed))
     :renames  (invert-renames renamed)}))

(defn- plan-refer-global
  "(:refer-global :only [Object String] :rename {Foo Bar}) - the names this
  namespace may write BARE and mean a JavaScript global. Returns a map from the
  name written to the js/ name it stands for.

  There is nothing to require. `js` is a symbol prefix here rather than a
  namespace (doc/cljs-compiler.md 7), so Object refers to js/Object the way a
  :refer refers a var - one name mapped to another, and no module, no import and
  no namespace object anywhere. cljs.analyzer's parse-global-refer-spec builds
  literally that: {:use {Object js, String js}}, an entry in the namespace's uses
  whose namespace is the symbol js.

  The point of writing it is that a bare name would otherwise be an ERROR - this
  compiler refuses a symbol that is neither a local nor a var - so it is the ns
  form's way of saying `Object here is the host's`. That makes it useful to us
  exactly as it is to them, and there is nothing to adapt."
  [args]
  (when-not (even? (count args))
    (analysis-error args ":refer-global takes keyword/value pairs"))
  (let [opts (apply hash-map args)
        {:keys [only rename]} opts]
    (check-opts! :refer-global "the ns form" opts #{:only :rename})
    (when-not (and (vector? only) (seq only) (every? simple-symbol? only))
      (analysis-error opts (str ":refer-global :only takes a non-empty vector of"
                                " simple symbols, got " (pr-str only))))
    (when-not (or (nil? rename)
                  (and (map? rename)
                       (every? simple-symbol? (mapcat identity rename))))
      (analysis-error opts (str ":refer-global :rename takes a map of simple"
                                " symbols, got " (pr-str rename))))
    ;; a renamed name has to be one of the names being referred, or the rename
    ;; renames nothing and the mistake is silent
    (doseq [[from _] rename]
      (when-not (some #{from} only)
        (analysis-error opts (str ":refer-global :rename names " from
                                  ", which is not in :only " (pr-str only) "."))))
    (into {}
          (map (fn [sym]
                 [(get rename sym sym) (symbol "js" (str sym))]))
          only)))

(defn- refer-core-renames!
  "(:refer-clojure :rename {mapv core-mapv}) applied: core-mapv is cljs.core/mapv
  in `this-ns`, and mapv is nothing here at all (plan-refer-clojure excluded it).

  THE ONLY EXPLICIT REFER OF A CLJS.CORE VAR THIS COMPILER WRITES. Every other
  core name arrives through the rule in env/resolve-var - ask cljs.core last -
  which is the refer half of the implicit require (doc/cljs-compiler.md 5.12) and
  which can only answer under the var's OWN name. A rename asks for a different
  name, so it needs a real mapping, and this is where it is made.

  Applied AFTER the requires, so that a namespace that both requires something and
  renames a core var gets the same answer whichever order the ns form listed them
  in - and after add-excludes!, whose set this one's sources are already in."
  [cenv this-ns renames]
  (when (seq renames)
    (let [^Namespace core (env/cljs-ns cenv 'cljs.core)
          ^Namespace here (env/cljs-ns cenv this-ns)]
      (doseq [[to from] renames]
        (if-let [v (.findInternedVar core from)]
          (.refer here to v)
          (analysis-error renames
                          (str ":refer-clojure :rename names cljs.core/" from
                               ", which does not exist.")))))))

(defn- apply-js-require!
  "A string require applied: the specifier recorded, the alias recorded, and the
  referred names recorded. No namespace is created, nothing is interned and no
  Namespace alias is added - there is nothing on the other end to point at.

  ONE NAME CANNOT MEAN TWO THINGS. A Namespace refuses a second, different target
  for an alias it already has, and that check cannot see these, so the two
  directions are asked here and in apply-require!. Without them
  (:require [\"react\" :as r] [app.r :as r]) would take whichever branch the
  resolver asks first, silently."
  [cenv this-ns {:keys [specifier path as also-as refers]}]
  (env/add-js-require! cenv this-ns specifier)
  ;; `as` is the alias that was asked for; `also-as` is the SYMBOL the require was
  ;; written under when the spec was shadow's spelling, so that
  ;; (:require [clipboard-polyfill]) leaves clipboard-polyfill/write resolving -
  ;; the same second name, and the same word for it, that a namespace require
  ;; carries for a rewritten target (apply-ns-require!).
  (doseq [as (remove nil? [as also-as])]
    (when (.lookupAlias ^Namespace (env/cljs-ns cenv this-ns) as)
      (analysis-error as (str as " already names a namespace in " this-ns
                              " - a JavaScript module needs an alias of its own.")))
    (env/add-js-alias! cenv this-ns as specifier path))
  (env/add-js-refers! cenv this-ns
                      (into {} (map (fn [[sym export]] [sym [specifier export]]))
                            refers)))

(defn- apply-ns-require!
  [cenv this-ns {:keys [target as also-as refers renames goog-refers macros
                        alias-only]}]
  ;; :as-alias alone: the alias below and nothing else. NOT add-require!, which is
  ;; what puts a namespace in the module's imports and the prologue - and there is
  ;; no module to import, because the namespace was never compiled and need not
  ;; exist. env/cljs-ns creates the empty Namespace the alias points at, which is
  ;; all ::foo/bar and `foo/bar need to expand.
  (when-not alias-only
    (env/add-require! cenv this-ns target))
  ;; `as` is the alias that was asked for; `also-as` is the name the require was
  ;; WRITTEN under when that is not the target's own (aliased-clj-ns), so that
  ;; clojure.test/deftest resolves in a namespace that required clojure.test.
  ;; ClojureScript writes the same second alias, as an extra spec its rewriter
  ;; adds beside the first (process-rewrite-form).
  (doseq [a (remove nil? [as also-as])]
    ;; An alias is a Clojure-side name only - what reaches JavaScript is
    ;; names/ns-alias of the TARGET - so it needs no JavaScript spelling and gets
    ;; no check for one. Namespace.addAlias refuses a second, different target for
    ;; a name already aliased, which is the check that matters.
    ;;
    ;; It cannot see a JavaScript module's alias, which lives on the namespace's
    ;; metadata rather than in the alias table, so that half is asked here - the
    ;; other direction of the check apply-js-require! makes.
    (when (contains? (env/js-aliases cenv this-ns) a)
      (analysis-error a (str a " already names a JavaScript module in " this-ns
                             " - a namespace needs an alias of its own.")))
    (.addAlias ^Namespace (env/cljs-ns cenv this-ns) a
               ^Namespace (env/cljs-ns cenv target)))
  ;; (:require [goog.string :refer [format]]) - a bare name drawn out of a Closure
  ;; namespace. Beside the Var refers below rather than among them: what is
  ;; recorded is which QUALIFIED name the bare one stands for, and nothing is
  ;; interned, because there is no Var on the other end to intern. The counterpart
  ;; of apply-js-require!'s env/add-js-refers!, one world over.
  (when (seq goog-refers)
    (env/add-goog-refers! cenv this-ns goog-refers))
  (let [^Namespace from (env/cljs-ns cenv target)
        ^Namespace here (env/cljs-ns cenv this-ns)]
    (doseq [sym refers]
      (.refer here sym (.findInternedVar from sym)))
    ;; a :rename is a refer under another name, so it is the same call with the
    ;; two names apart
    (doseq [[to from-sym] renames]
      (.refer here to (.findInternedVar from from-sym))))
  (when macros
    (env/require-macros! cenv this-ns (:target macros)
                         :as (:as macros) :refer (:refers macros)
                         :rename (:renames macros))))

(defn- apply-require!
  "One planned require applied, whichever kind it is. A plan carrying a
  :specifier came from a string spec and names a JavaScript module; every other
  one names a ClojureScript namespace.

  One function rather than two lists in the plan, because both of its callers -
  parse-ns and require-libs! - apply what they planned in the order it was
  WRITTEN, and an ns form is free to interleave the two kinds."
  [cenv this-ns plan]
  (if (:specifier plan)
    (apply-js-require! cenv this-ns plan)
    (apply-ns-require! cenv this-ns plan)))

(defn- parse-ns
  "The ns form: the only place a namespace's requires, aliases and refers are
  established.

  Its work is done during ANALYSIS, on cenv, and that is what makes the top-level
  check below worth having rather than pedantry: inside a function body the
  aliases would be established while the file compiles and the JavaScript would
  run later, so the two would disagree about when the namespace changed. The check
  catches the shape that makes the mistake - (defn f [] (ns ...)) - rather than
  every possible one; (if p (ns a) (ns b)) still gets through, and is nobody's
  intent.

  EVERY REFERENCE IS CHECKED BEFORE ANY IS APPLIED, and the cursor moves last. A
  form that throws therefore leaves the namespace as it was rather than half
  requiring something, and leaves the REPL in the namespace it was in rather than
  in a half-built one. Without that a mistyped :refer cost the whole session: the
  require was recorded before the refer was checked, so every later script asked
  the runtime to fetch a namespace that was never going to exist. What a failed
  form does leave behind is inert - the namespaces it named exist, empty, and any
  JVM macro namespace it named is loaded.

  :import names a CLOSURE class and nothing else - there is no other kind here -
  and is a require of that class plus an alias from its bare name, which is what
  (:import [goog.string StringBuffer]) means in cljs.core.

  Not here: :rename and :as-alias, refused by name rather than ignored; the implicit
  self-require of a same-named macro namespace, which needs the source resolution
  M3's second half brings; and the emission of static imports for a module on
  disk, which needs the same. A required namespace that has not been analysed yet
  is created empty rather than compiled - see env/add-require!."
  [cenv env form]
  (when-not (:top-level? env)
    (analysis-error form
                    (str "ns must appear at the top level: it is an analysis-time"
                         " effect, so inside a function body it would move the"
                         " compiler's namespace while the code moved nothing.")))
  (let [[_ nsym & more] form]
    (when-not (and (symbol? nsym) (nil? (namespace nsym)))
      (analysis-error form (str "A namespace name must be an unqualified symbol, got "
                                (pr-str nsym))))
    ;; for its preconditions: ns-alias is what an emitted reference spells, so a
    ;; name that cannot spell one is refused here rather than at emission
    (names/ns-alias nsym)
    (let [[doc more]   (if (string? (first more)) [(first more) (rest more)] [nil more])
          [attrs more] (if (map? (first more)) [(first more) (rest more)] [nil more])
          plan (reduce
                (fn [plan ref]
                  (when-not (and (sequential? ref) (keyword? (first ref)))
                    (analysis-error ref (str "Bad ns reference: " (pr-str ref)
                                             ". Expected (:require ...) or similar.")))
                  (let [specs (rest ref)]
                    (case (first ref)
                      :require
                      (update plan :requires into
                              (map #(plan-require cenv :require %)) specs)
                      :use
                      (update plan :requires into
                              (map #(plan-require cenv :use %)) specs)
                      :require-macros
                      (update plan :macro-requires into
                              (map #(plan-require-macros cenv :require-macros %)) specs)
                      :use-macros
                      (update plan :macro-requires into
                              (map #(plan-require-macros cenv :use-macros %)) specs)
                      :refer-clojure
                      (let [{:keys [excludes renames]} (plan-refer-clojure specs)]
                        (-> plan
                            (update :excludes into excludes)
                            (update :core-renames merge renames)))
                      :refer-global
                      (update plan :global-refers merge (plan-refer-global specs))
                      :import
                      (update plan :imports into
                              (mapcat #(plan-import %)) specs)
                      (analysis-error ref
                                      (str "Unknown ns reference " (first ref)
                                           ". Handled: :require, :require-macros,"
                                           " :use, :use-macros, :refer-clojure,"
                                           " :refer-global, :import.")))))
                {:requires [] :imports [] :macro-requires [] :excludes #{}
                 :core-renames {} :global-refers {}}
                more)]
      ;; the plan is complete, so applying it starts here - and starts by undoing
      ;; the last ns form for this namespace, because a declaration replaces
      ;; rather than accumulates
      (env/clear-ns-declaration! cenv nsym)
      (run! #(apply-require! cenv nsym %) (:requires plan))
      ;; an :import is a require plus an alias, so it applies as one - and is
      ;; recorded as an import besides, which is the one thing the alias does not
      ;; say and the one thing ns-imports asks
      (run! #(apply-require! cenv nsym %) (:imports plan))
      (env/add-imports! cenv nsym
                        (into {} (map (juxt :as :target)) (:imports plan)))
      (doseq [{:keys [target as refers renames]} (:macro-requires plan)]
        (env/require-macros! cenv nsym target :as as :refer refers :rename renames))
      (env/add-excludes! cenv nsym (:excludes plan))
      (refer-core-renames! cenv nsym (:core-renames plan))
      (env/refer-globals! cenv nsym (:global-refers plan))
      (env/declare-ns! cenv nsym)
      (when (or doc attrs)
        (alter-meta! (env/cljs-ns cenv nsym) merge attrs (when doc {:doc doc})))
      (env/set-current-ns! nsym)
      {:op :ns :form form :env env :name nsym :doc doc
       :requires (vec (sort (env/requires cenv nsym)))
       :children []})))

(defn require-libs!
  "Apply `specs` as (:require ...) entries of the CURRENT namespace, ADDING to what
  it already requires rather than replacing it.

  That is the whole difference between this and an ns form, and it is why the REPL
  cannot simply build one: (require 'foo) means also foo, where (ns app.core ...)
  means exactly this list. Everything else is shared - the same planning, the same
  check-before-apply, so a spec that cannot be applied applies none of itself.

  The namespaces named have to have been analysed already, because :refer is
  checked against what they define; the REPL compiles them first."
  [cenv specs]
  (let [nsym  env/*current-ns*
        plans (mapv #(plan-require cenv :require %) specs)]
    (run! #(apply-require! cenv nsym %) plans)
    (mapv :target plans)))

(defn- parse-try-clause
  "What (catch ...) or (finally ...) means OUTSIDE a try, which is either a local
  being called or a mistake. See the note in `parsers`."
  [op]
  (fn [cenv env form]
    (if (contains? (:locals env) op)
      (parse-invoke cenv env form)
      (analysis-error form (str op " is only valid inside a try")))))

(def ^:private parsers
  {'if parse-if, 'do parse-do, 'let* parse-let, 'js* parse-js, 'fn* parse-fn,
   'def parse-def, 'loop* parse-loop, 'recur parse-recur,
   '. parse-dot, 'new parse-new,
   'throw parse-throw, 'set! parse-set!, 'quote parse-quote, 'var parse-var,
   'letfn* parse-letfn, 'case* parse-case, 'ns parse-ns, 'try parse-try,
   'deftype* (parse-deftype false), 'defrecord* (parse-deftype true)
   ;; NOT SPECIAL FORMS, and in here anyway. Neither Clojure nor ClojureScript
   ;; treats them as one - cljs.analyzer's `specials` set has neither, and both
   ;; are recognised positionally by try's parser and nowhere else - so a LOCAL
   ;; MAY SHADOW EITHER, which core_test.cljs:1496 does on purpose:
   ;;
   ;;     (is (= 1 (let [catch identity] (catch 1))))
   ;;
   ;; They are here because the alternative message is worse. Someone who gets the
   ;; shape of a try wrong writes (catch ...) in the open, and "the symbol catch is
   ;; neither a local nor a var" sends them looking for a var they never meant to
   ;; name. So each says what is actually wrong, and checks first that the name is
   ;; not simply in scope - which is the whole of what being in the table costs.
   'catch   (parse-try-clause 'catch)
   'finally (parse-try-clause 'finally)})

;; --- entry ------------------------------------------------------------------

(defn- unsupported [form what]
  (throw (ex-info (str "Not implemented yet: " what
                       ". This analyzer handles " (pr-str (sort (keys parsers)))
                       ", function application, locals and literals.")
                  {:form form})))

(defn- local-node [env sym b]
  (cond-> {:op :local :name sym :js-name (:js-name b) :local (:local b)
           :form sym :env env :children []}
    ;; ^boolean on a binding form, read off the binding it refers to
    (:tag b) (assoc :tag (:tag b))))

(def ^:private js-path-re
  "A dotted path of JavaScript identifiers - the shape a js/ name has to have once
  spelled. js/-Infinity needs no exception here: host-name has already made it
  _Infinity, and only the emitter restores the minus."
  #"^[A-Za-z_$][A-Za-z0-9_$]*(\.[A-Za-z_$][A-Za-z0-9_$]*)*$")

(defn- check-js-name!
  "A js/ name reaches JavaScript spelled the host's way and otherwise untouched,
  so it has to already BE a name there.

  Without this js/foo-bar emitted the text foo-bar, which JavaScript reads as a
  subtraction of two globals rather than a reference to one: a ReferenceError when
  they do not exist, and silently wrong arithmetic when they do. ClojureScript
  munges instead, turning js/foo-bar into foo_bar, which we do too - this catches
  what survives even that."
  [sym]
  (let [js (names/host-name (name sym))]
    (when-not (re-matches js-path-re js)
      (throw (ex-info (str "Cannot use " sym " as a JavaScript global: it spells "
                           js ", which is not a name there.")
                      {:sym sym})))))

(defn- js-var-node
  "A reference to a JavaScript global, spelled `sym` and written `form` in source.

  The two differ for Math/floor, which means js/Math.floor but was not written
  that way - see analyze-qualified-symbol."
  [env sym form]
  (check-js-name! sym)
  {:op :js-var :name sym :ns 'js :form form :env env :children []})

(def ^:private published-global-root
  "The one ClojureScript namespace root this compiler publishes as a JavaScript
  global. runtime.js sets globalThis.cljs, and nothing else - see 5.60 for the
  measurement that says one is the right number."
  "cljs")

(defn- cljs-namespace-behind
  "The ClojureScript namespace a js/ name is reaching for, or nil.

  js/app.core.foo under a compiled app.core is somebody assuming the layout every
  OTHER ClojureScript compiler emits, where a namespace is an object at a global
  path. Here it is not one, so the name is undefined at load and the message says
  `app is not defined` - true, unhelpful, and a long way from the assumption that
  caused it. This is what lets the warning name the assumption instead.

  The LONGEST prefix that names a namespace, which is analyze-dotted-symbol's rule
  and dotted-var-sym's, so the three cannot drift apart.

  `cljs` is excluded because it is the one root runtime.js does publish, and a
  warning about a name that works would be noise."
  [cenv sym]
  (let [segs (clojure.string/split (str (name sym)) #"\.")]
    (when-not (= published-global-root (first segs))
      (some (fn [n]
              (let [p (symbol (clojure.string/join "." (take n segs)))]
                (when (or (= 'cljs.core p) (some? (env/find-cljs-ns cenv p))) p)))
            (range (count segs) 0 -1)))))

(defn- analyze-js-symbol
  "js/foo - a JavaScript global.

  `js` is deliberately NOT a namespace in the ClojureScript NamespaceWorld: no
  Namespace is created and nothing is interned, so `js` can never collide with a
  real ClojureScript namespace, which is the property the world exists to protect.
  It is a symbol prefix the analyzer recognises, and nothing else.

  The name keeps its dots. js/console.log is one :js-var, not a field access -
  cljs.analyzer agrees (desugar-dotted-expr rewrites dotted :var and :local names,
  and skips :js-var).

  A local of the same name wins, as it does in ClojureScript: js/x inside
  (fn* [x] ...) is the parameter. Surprising, but it is the established reading,
  and cljs.analyzer warns rather than erroring.

  JS/GOOG IS OURS RATHER THAN THE HOST'S, and it is the one name this rule
  excepts. `goog` here is the vendored Closure subset (doc/cljs-compiler.md 5.5),
  and base.js deliberately does not publish it on globalThis - that is the whole
  of our isolation from a Closure the user's project happens to bundle - so
  js/goog read as a global would be a ReferenceError at load, pointing at code
  that did nothing wrong.

  So a `goog` or `goog.` name is analysed as the Closure name it spells:
  js/goog is $ns(\"goog\"), js/goog.string.urlDecode is goog.string/urlDecode, and
  each records its own require the way any written-out Closure name does
  (require-goog!). Nothing else about js/ changes.

  IN CLOJURESCRIPT THE TWO ARE THE SAME OBJECT ANYWAY - goog IS a global there,
  so js/goog and goog coincide by accident of layout - which is why their tests
  write it both ways within one form: cljs/ns_test.cljs asks
  (.isArrayLike js/goog x), (goog/isArrayLike x) and (goog-alias/isArrayLike x)
  and expects one answer, and cljs/invoke_test.cljs writes
  (js/goog.string.urlDecode \"bar\"). Here they coincide by rule instead. The
  divergence bought is one sentence - js/ names the host's globals, except goog,
  which is not the host's - and the alternative was to put `goog` on globalThis
  and lose the isolation for it."
  [cenv env sym]
  (let [bare (symbol (name sym))]
    (cond
      (contains? (:locals env) bare) (local-node env bare (get-in env [:locals bare]))
      ;; the bare symbol, analysed: everything that decides what a Closure name
      ;; means - a provide is a value, a shorter prefix plus a var, the require it
      ;; records, the subset it has to be in - is decided there and stays decided
      ;; in one place
      (goog/goog-ns? bare) (analyze cenv env (with-meta bare (meta sym)))
      :else (do (when-let [nsym (cljs-namespace-behind cenv bare)]
                  (warning :js-name-is-a-namespace env {:sym sym :ns-sym nsym}))
                (js-var-node env sym sym)))))

(defn- goog-var-node
  "gobject/get - a var in a goog namespace.

  There is no Var to find. goog is JavaScript: goog/object.js was never analysed
  by anything, and a JavaScript object's properties cannot be enumerated at compile
  time - so a goog name is UNCHECKED, exactly as js/foo is, and a typo surfaces
  when it runs.

  With one exception, and it is the reason check-var! exists. Three namespaces in
  the subset are REDUCTIONS we wrote - goog.string has four functions where the
  real one has seventy-one - so for those we do have the list, and a name that is
  missing is missing because WE removed it. Leaving that to the runtime would put
  `goog$string$ns.format is not a function` in the user's lap, pointing at their
  code. See clojure.cljs.goog/reduced-vars."
  [env sym form ns-name]
  (goog/check-var! (str ns-name) (name sym))
  (check-js-name! (symbol (name sym)))
  {:op :goog-var :form form :env env :children []
   :name (symbol (str ns-name) (name sym))
   :ns ns-name})

(defn- goog-ns-node
  "goog.math.Long, as a value - the class itself rather than a var in it.

  A Closure provide is a name in a nested object, so goog.math.Long is both a
  module and a value, and base.js registers it under its own name as well as under
  its container's. $ns(\"goog.math.Long\") is therefore the constructor, which is
  what (instance? goog.math.Long x) needs.

  Usually written as a simple symbol with dots in it. Not always: slash and dot
  are the same name here, so goog.string/StringBuffer is this node too - see
  analyze-qualified-symbol, which is where a macro's expansion arrives."
  ([env sym] (goog-ns-node env sym sym))
  ;; `form` is what the source said, which is not always `sym`: the provide is one
  ;; name and the two spellings of it are not.
  ([env sym form]
   {:op :goog-ns :form form :env env :children [] :name sym}))

(defn- js-module-node
  "React, where the ns form said (:require [\"react\" :as React]) - the module
  object itself, which is what `import * as` bound.

  The counterpart of goog-ns-node one world over, and it exists for the same
  reason: a module is a VALUE as well as a place to read names out of, and a
  program passing one along - to a framework, to console.log - has written
  something that means exactly that."
  [env specifier form]
  {:op :js-module :form form :env env :children [] :specifier specifier})

(defn- js-module-var-node
  "React/createElement, or a bare useState the ns form :referred - an export of a
  JavaScript module.

  UNCHECKED, like a goog var and for a stronger version of its reason. A goog file
  at least sits on the classpath and could in principle be read; the file behind a
  specifier is built by a bundler out of node_modules and need not exist yet when
  this compiles. What is checked is that the name can be spelled at all.

  `export` is a String and not a symbol: it is JavaScript's name for the thing,
  which is why :rename can change what this namespace calls it without changing
  this.

  It may be a DOTTED PATH rather than one name, and only because a specifier may
  ask for one: [\"date-fns/sub$default\" :refer [x]] reads default.x off the
  module. check-js-name! takes a path already - it is the shape js/a.b.c has -
  and so does the emitter, which spells each segment the host's way and joins
  them with the dots they were written with."
  [env specifier export form]
  (check-js-name! (symbol export))
  {:op :js-module-var :form form :env env :children []
   :specifier specifier :export export})

(def ^:private removed-core-vars
  "Names upstream cljs.core has that this fork's core.cljs does not, and why.

  core.cljs carried a block of \"Bootstrap helpers\" - find-ns-obj and the family
  around it - which finds a namespace by munging its name, splitting on dots and
  walking those segments as properties of goog.global. That is the addressing
  scheme cljs-repl.md §3.1 replaced: a namespace here is an object in a registry,
  reached by $ns(\"app.core\"), so the walk found nothing for every namespace that
  exists. Measured before they went - (find-ns 'cljs.user) answered nil, and
  (ns-name (find-ns 'cljs.user)) was a TypeError on that nil.

  MOST OF THAT BLOCK IS BACK (§5.48), because the registry can answer what
  goog.global could not: find-ns-obj reads it, and find-ns, create-ns and the
  Namespace type are upstream's own code working over a lookup that is now right.
  What is still here is what the registry does not make right.

  ns-interns* is the interesting one of those. Nothing is wrong with its idea - a
  namespace object's properties ARE its vars here - but it names them by putting
  the property through cljs.core/demunge, which decodes cljs.compiler's spelling,
  and a var is spelled by clojure.cljs.names/munge: cljs.core/*e is the property
  $STAR$e here and _STAR_e there. So it would answer, and be wrong for every name
  with a character in it. ns-interns asks the compiler instead, which knows.

  They are gone from the file (core-test declares every removed line), so a
  program naming one gets the error a missing name already gets. This map only
  adds the REASON to it, which is the difference between \"there is no such var\"
  and \"there is no such var, and here is what replaced it\".

  WHAT IS NOT HERE MARKS THE EDGE OF THE RULE. cljs.core/ns-name stayed even while
  find-ns was gone: given a Namespace it answers correctly, it was merely
  unreachable, and the vendored cljs/repl.cljs calls it in print-doc on a namespace
  its caller supplies - a file that compiles today and would have stopped.
  cljs.core/*eval* went with eval, which is self-hosting's entry point and nothing
  else's. The rule is: remove what answers WRONGLY, keep what is merely
  unreachable - and restore what the registry made answerable."
  '{find-macros-ns "macros live in JVM namespaces here - there is no $macros half"
    NS_CACHE       "the cache in front of the goog.global walk find-ns-obj replaced"
    ns-interns*    "it demunges cljs.compiler's spelling; ns-interns asks the compiler"
    eval           "self-hosted ClojureScript's entry point; there is no eval here"
    *eval*         "self-hosted ClojureScript's entry point; there is no eval here"})

(defn- removed-note
  "The reason `sym` names one of removed-core-vars, as a sentence to append to the
  error a missing name already raises - or nil. Opens with a period, because it
  is appended to a sentence.

  Unqualified or qualified to cljs.core, because those are the two spellings that
  could have meant the removed one. A namespace of your own may define any of
  these names and the note never fires: the name resolved, so nothing raised."
  [sym]
  (let [ns' (namespace sym)]
    (when (or (nil? ns') (= "cljs.core" ns'))
      (when-let [why (get removed-core-vars (symbol (name sym)))]
        (str ". cljs.core/" (name sym) " was removed from this fork's core.cljs: "
             why ".")))))

(defn- var-node [env ^Var v form]
  ;; :tag is the var's OWN metadata, which is where ^boolean lands - (def ^boolean
  ;; x ...) and cljs.core's 86 predicates. Carried rather than inferred: this
  ;; compiler has no infer-tag, so a tag reaches a node only where a program wrote
  ;; one, and the emitter reads it in exactly one place (emit-if). §5.32.
  (cond-> {:op :var :form form :env env
           :name (symbol (str (.getName (.ns v))) (str (.sym v)))
           :ns (.getName (.ns v))}
    (:tag (meta v))     (assoc :tag (:tag (meta v)))
    (:ret-tag (meta v)) (assoc :ret-tag (:ret-tag (meta v)))
    ;; :top-fn is the SHAPE of the function the var holds - which arities exist,
    ;; and whether one of them is variadic. Written by cljs.core's defn (core.cljc:
    ;; multi-arity-fn, variadic-fn) onto the def's name, so it is already on the
    ;; var by the time a call site asks; carried here so emit-invoke can dispatch
    ;; straight to an arity rather than through the dispatch function (§5.33).
    (:top-fn (meta v))  (assoc :top-fn (:top-fn (meta v)))))

(defn- unchecked-var-node
  "A var reference nobody checked, because `sym` carries ::no-resolve and the
  caller has therefore said it knows what the name means.

  cljs.analyzer's metadata key and cljs.analyzer's purpose for it: a macro that
  writes a reference to a var it can see from where it was DEFINED, expanding
  somewhere the var is not yet visible. cljs/core.cljc's str macro is the case
  that made us honour it - cljs.core/str_ is defined three thousand lines below
  the first use of it in core.cljs, and ClojureScript gets away with the forward
  reference only because its own str writes the global path as raw text, which
  nothing resolves and so nothing finds missing (doc/cljs-compiler.md §5.9).

  Narrow on purpose: this is the missing-VAR case in a namespace that resolved.
  An unknown namespace is a different question and is not silenced by it."
  [env sym form ns-name]
  {:op :var :form form :env env
   :name (symbol (str ns-name) (name sym))
   :ns ns-name})

(def ^:private implicit-nses
  "Prefixes whose not being a namespace is unsurprising, and so not worth a
  warning. Math/floor is one; every JavaScript global is a candidate.

  cljs.analyzer keeps the same list (analyzer.cljc:820) and it is the ONLY thing
  its list does - resolution does not consult it. Theirs is
  #{goog goog.object goog.string goog.array Math String}; this is that set minus
  the goog names, which is a difference in the target and not an oversight. There
  goog.object is a property of a global once base.js has run, so naming it without
  a require works and is merely untidy; here a goog namespace reaches the module
  through an IMPORT computed from the requires, so naming one without requiring it
  produces code that cannot run. That case stays an error below."
  '#{Math String})

(defn- require-goog!
  "Record that the current namespace requires the Closure namespace `target`, and
  hand `target` back.

  A FULLY-QUALIFIED CLOSURE NAME IS ITS OWN REQUIRE, which is why this is called
  where such a name was written rather than where one was declared. What a require
  buys is a SHORT name - an alias, so that gobj/get means something, or an :import,
  so that a bare StringBuffer does. A name written out in full carries its own
  referent, and there is nothing left for the ns form to tell a reader who can
  already see it.

  It is still RECORDED, because the require is what a module's imports and a
  script's prologue are computed from: without this line $ns(\"goog.string\") hands
  back an empty object at run time. That was always the reason the ns form was
  demanded here - and it is a reason to write the require down, not a reason to
  refuse the name. The `goog` prefix has been doing exactly this since it was made
  implicit; this is that branch, widened to the rest of the tree.

  THE CASE THAT SETTLES IT IS A MACRO. cljs.core/with-out-str expands to
  (goog.string/StringBuffer.) and lands in whichever namespace called it. That
  namespace cannot know to require goog.string, and making it say so would publish
  an implementation detail of a cljs.core macro as part of its contract - every
  caller of with-out-str, printing-test and cljs.spec.alpha among them, made to
  name a Closure namespace it never mentions. ClojureScript's core.cljc writes the
  same expansion and never has to notice, because a goog name there is a global
  path that resolution falls through to (see analyze-qualified-symbol).

  Strictness is untouched where it says something. An alias with no require still
  resolves to nothing, a goog name outside our subset is still refused by
  goog/known?, and a ClojureScript namespace still has to be required - that one
  is not a global path here and never becomes one."
  [cenv target]
  (env/add-require! cenv env/*current-ns* target)
  target)

(defn- qualified-method-kind
  "The kind of QUALIFIED METHOD `sym` names, or nil if it is not one.

  Clojure 1.12's syntax, which ClojureScript 1.12 adopted: String/.toUpperCase is
  the instance method toUpperCase of String, and Object/new is Object's
  constructor. Both name a HOST member as a value, which is what they add over
  (.toUpperCase s) and (new Object) - those are calls and cannot be passed to map.

  Only the two spellings. String/fromCharCode is a static method and needs nothing
  new: it is already a name in an object, and analyze-qualified-symbol's last
  branch has read it as one since §.8."
  [sym]
  (let [nm (name sym)]
    (cond (= "new" nm) :new
          (clojure.string/starts-with? nm ".") :method)))

(defn- qualified-method-node
  "String/.toUpperCase or Object/new - a host member as a value.

  ONE READING IN EVERY POSITION, which is worth stating because it is not what a
  reader who knows (.toUpperCase s) expects: (String/.toUpperCase s) is NOT
  rewritten to a host call. It builds the same closure the value position builds
  and calls it. Stock ClojureScript does exactly this - the oracle emits

    (function (x, ...args) { return Reflect.apply(String.prototype.toUpperCase, x, args) }).call(null,s)

  for (String/.toUpperCase s) - and the uniformity is the point: one node, one
  meaning, no position-dependent semantics for a form whose whole purpose is to
  survive being passed around.

  The CLASS is analysed as an ordinary value, so everything that can name a type
  names one here: a :refer-global name, a goog provide (which records its own
  require - see require-goog!), a local, a var. That is where the fork is stricter
  than ClojureScript, and deliberately: there an unresolved Object warns and emits
  `Object` anyway, here a bare host name has to be said with :refer-global, so the
  message below hands back the line to write."
  [cenv env sym form kind]
  (let [cls (with-meta (symbol (namespace sym)) (meta sym))]
    {:op :qualified-method :form form :env env :kind kind
     :method (when (= :method kind) (symbol (subs (name sym) 1)))
     :class (try
              (analyze cenv (not-tail env) cls)
              (catch clojure.lang.ExceptionInfo e
                ;; only when the failure IS the class name; anything else that
                ;; went wrong under there is its own error and keeps its message
                (if (= cls (:form (ex-data e)))
                  (analysis-error
                   form (str form " names a member of " cls ", and " cls
                             " is not a type here: " (.getMessage e)
                             (when (simple-symbol? cls)
                               (str " If it is meant to be the JavaScript global,"
                                    " say so - (:refer-global :only [" cls "]))."))))
                  (throw e))))
     :children [:class]}))

(defn- analyze-qualified-symbol
  "foo/bar, where foo is not js.

  Usually a var in another namespace. findInternedVar, not getMapping: what
  another namespace REFERS is not reachable through its name, only what it
  defines. Clojure resolves a qualified symbol the same way (Compiler.resolveIn),
  and so does cljs.analyzer, which consults that namespace's :defs.

  A GOOG PREFIX RESOLVES WHETHER OR NOT IT WAS REQUIRED, and the require is
  recorded as the name is read - require-goog! has the argument. Two readings of
  such a name, in this order:

    goog.string/StringBuffer is the CLASS Closure provides under that name. A
    provide is one name, and slash and dot are two spellings of it, so this is
    asked before the name is taken apart. Asked of the RESOLVED prefix, so an
    alias reaches it too: gstring/StringBuffer is the same class.

    otherwise goog.object/get is a var in goog.object. Unchecked, like js/foo -
    except in the three namespaces the subset REDUCES, where goog-var-node has
    the list and check-var! uses it.

  When `foo` is not a namespace at all the symbol names a JAVASCRIPT GLOBAL:
  Math/floor is Math.floor. That is what ClojureScript does with every prefix it
  cannot resolve - not through externs, which this branch never consults, but by
  spelling the symbol out and letting the host answer for it. A prefix outside
  implicit-nses gets a warning first, exactly as there.

  The node is a :js-var, where cljs.analyzer makes it a :var whose :ns is `Math`.
  Both emit Math.floor, and ours is the same statement in our model rather than a
  divergence: a ClojureScript var IS a global path, so :var/Math already read as
  `the global Math, property floor`, while a var of ours is a property of a
  namespace object reached through $ns (doc/cljs-compiler.md §5.2). Math has no
  namespace object and never will."
  ([cenv env sym] (analyze-qualified-symbol cenv env sym sym))
  ;; `form` is what the source actually said, which is not always `sym`:
  ;; analyze-dotted-symbol below rewrites cljs.core.Var to cljs.core/Var to get
  ;; here, and every node and message should still name what was written.
  ([cenv env sym form]
  (let [nsym  (symbol (namespace sym))
        ^Namespace target (env/resolve-ns cenv nsym)
        ;; the goog name this prefix stands for, through an alias or as itself
        gns   (if (some? target)
                (let [n (.getName target)] (when (closure-ns? cenv n) n))
                (when (closure-ns? cenv nsym) nsym))
        prov  (when gns
                (let [p (symbol (str gns "." (name sym)))]
                  (when (goog/provided? p) p)))
        ;; String/.toUpperCase, Object/new - a host member as a value. Asked when
        ;; the prefix is not a ClojureScript NAMESPACE, which is how cljs.analyzer
        ;; asks it (analyzer.cljc:4143): my.ns/.foo in a namespace that requires
        ;; my.ns is still a var called .foo and not a method.
        ;;
        ;; A GOOG PREFIX COUNTS AS NOT ONE, and the reason is that the two readings
        ;; cannot both be live there. A goog var named `new` or `.append` is
        ;; unreachable - check-js-name! refuses the second outright and the first
        ;; is a reserved word - so for a goog prefix the method reading is the only
        ;; one that can produce code, and goog.string.StringBuffer/.append means
        ;; what it looks like. It has to be said explicitly because require-goog!
        ;; makes a provide resolvable the moment it is named, so the SECOND
        ;; occurrence in a file would otherwise take a different branch from the
        ;; first.
        ;;
        ;; Asked BEFORE the goog branches, so the class is analysed as an ordinary
        ;; value - which is also how goog.math.Long/new records its own require.
        mkind (when (or (nil? target) (some? gns)) (qualified-method-kind sym))]
    (cond
      mkind (qualified-method-node cenv env sym form mkind)

      prov (goog-ns-node env (require-goog! cenv prov) form)

      (and gns (goog/provided? gns))
      (goog-var-node env sym form (require-goog! cenv gns))

      ;; a name in the goog tree that this fork does not ship. Not a JavaScript
      ;; global to fall through to: the whole `goog.` prefix is reserved, so the
      ;; answer is that we do not have it rather than that we do not know it.
      gns
      (analysis-error form
                      (str "No such namespace: " gns
                           (if goog/*closure-library*
                             (str ". The Closure Library on the classpath does not"
                                  " provide it.")
                             (str ". This fork ships a subset of the Closure Library,"
                                  " and that name is not in it. To get it: "
                                  (goog/get-real-closure)))))

      ;; React/createElement - an export of a JavaScript module this namespace
      ;; required under that name. Asked after the goog branches, which cannot
      ;; overlap with it (a goog name has a dot in it and an alias does not), and
      ;; before every reading below, because an alias is a DECLARATION: a name the
      ;; ns form said stands for a module is that module, whatever else the
      ;; session happens to hold under it.
      (contains? (env/js-aliases cenv env/*current-ns*) nsym)
      ;; [specifier path], the path being the $ sugar: sub/foo where the ns form
      ;; said ["date-fns/sub$default" :as sub] is the property foo of the property
      ;; default, and the only difference it makes is what the export path starts
      ;; from.
      (let [[specifier path] (get (env/js-aliases cenv env/*current-ns*) nsym)
            nm        (name sym)
            dot       (.indexOf nm ".")]
        (if (pos? dot)
          ;; React/Children.map - the export Children, property map. The rewriting
          ;; the namespace branch below does, for the same reason: a dot in the
          ;; NAME half splits a value from its properties, and an export named
          ;; `Children.map` is not a thing JavaScript can have.
          (analyze cenv env
                   (reduce (fn [t p] (list '. t (symbol (str "-" p))))
                           (with-meta (symbol (str nsym) (subs nm 0 dot))
                             (meta sym))
                           (rest (clojure.string/split nm #"\."))))
          (js-module-var-node env specifier (js-export-path path nm) form)))

      ;; PersistentVector/EMPTY - the namespace part names a VAR rather than a
      ;; namespace, so the whole symbol is that value and a property of it. Asked
      ;; after `target`, so a real namespace or alias of the same name wins.
      ;;
      ;; cljs.analyzer asks it in the same order and asks it FIRST among the things
      ;; a qualified symbol can be (resolve-var: not an alias, no dot in the
      ;; namespace part, and the namespace part resolves as a var - then read the
      ;; whole thing as the dotted symbol). Their reading of a dotted symbol is
      ;; ours (analyze-dotted-symbol's first rule), so this arrives at the same
      ;; place by building the property access directly instead - which also keeps
      ;; the two from handing the same name back and forth, since the dotted
      ;; spelling splits at its last dot and returns here.
      ;;
      ;; What needs it is a TYPE used as a container of statics: cljs/core_test.cljs
      ;; writes (= [] PersistentVector/EMPTY), and ClojureScript gets it for nothing
      ;; because a var there IS a global path, so cljs.core.PersistentVector.EMPTY
      ;; is already the right JavaScript. Here a var is a property of a namespace
      ;; object (5.2), so the property access has to be built.
      (and (nil? target)
           (or (contains? (:locals env) nsym)
               (some? (env/resolve-var cenv nsym))))
      (analyze cenv env
               (reduce (fn [t p] (list '. t (symbol (str "-" p))))
                       (with-meta nsym (meta sym))
                       (clojure.string/split (name sym) #"\.")))

      (some? target)
      (let [tname (.getName target)
            nm    (name sym)
            dot   (.indexOf nm ".")]
        (cond
          ;; cljs.core/PersistentQueue.EMPTY - the VAR PersistentQueue, property
          ;; EMPTY. A dot in the NAME half is property access, because a
          ;; ClojureScript var name cannot hold one: the first dot splits a value
          ;; from its properties, which is analyze-dotted-symbol's first reading
          ;; applied one level in.
          ;;
          ;; ClojureScript gets this for nothing - the symbol munges to the global
          ;; path cljs.core.PersistentQueue.EMPTY and the property access is the
          ;; same dots - and it is written that way in cljs/reader.cljs:101, so a
          ;; compiler whose vars are properties of a namespace object (§5.2) has
          ;; to say it. Rewritten to the form rather than built as a node, so the
          ;; var goes through ordinary resolution and everything else about it -
          ;; the missing-var message, ::no-resolve - keeps working.
          (pos? dot)
          (analyze cenv env
                   (reduce (fn [t p] (list '. t (symbol (str "-" p))))
                           (with-meta (symbol (str tname) (subs nm 0 dot))
                             (meta sym))
                           (rest (clojure.string/split nm #"\."))))

          (.findInternedVar target (symbol nm))
          (var-node env (.findInternedVar target (symbol nm)) form)

          (::no-resolve (meta sym)) (unchecked-var-node env sym form tname)

          ;; the namespace is there and the var is not, which is a different
          ;; question from the one below and still an error: we can SEE the
          ;; namespace, so we know the name is missing rather than merely
          ;; unknown to us.
          :else (analysis-error form (str "No such var: " form (removed-note form)))))

      ;; A FULLY-QUALIFIED NAME OF A COMPILED NAMESPACE IS ITS OWN REQUIRE, which
      ;; is require-goog!'s rule (doc/cljs-compiler.md 5.18) reaching the other
      ;; half of the world - and it is here rather than there because the reason
      ;; 5.18 gave for stopping at goog has been answered since.
      ;;
      ;; That reason was that a goog name is registered on one global object by
      ;; base.js and can be reached by writing it out, while a var of ours is a
      ;; property of a namespace object NOBODY BOUND until the require puts it in
      ;; the module's imports - so resolving one without a require would compile
      ;; and then fail to run. It would. But recording the require is what binds
      ;; it, and driver/module-text reads env/requires AFTER the whole body is
      ;; analysed, so a require added while resolving a name reaches that module's
      ;; imports and its prologue like any other. Nothing is left unbound.
      ;;
      ;; WHAT NEEDS IT IS A MACRO, and the same macro argument require-goog! makes:
      ;; cljs/pprint.cljc expands to clojure.string/split-lines and lands in
      ;; whichever namespace called cl-format, and clojure.test.check.clojure-test's
      ;; defspec expands to clojure.test.check/quick-check. Neither caller can know
      ;; to require those, and making them say so would publish an implementation
      ;; detail of somebody else's macro as part of their own ns form.
      ;;
      ;; DECLARED, not merely named, and that is the whole of the remaining
      ;; strictness. env/declared? is true only of a namespace whose ns form has
      ;; been analysed here - which in a driver run means it was compiled and its
      ;; module written, so there is a file for the import to reach. A typo still
      ;; names nothing and still gets the message below; a namespace nobody
      ;; compiled still gets it, and correctly, because the driver needs it in the
      ;; ns form UP FRONT to compile it at all.
      (env/declared? cenv nsym)
      (do (env/add-require! cenv env/*current-ns* nsym)
          ;; one level: the require is recorded, so resolve-ns finds it now and
          ;; the ordinary var branch above does the rest - including saying `No
          ;; such var` if the name is wrong
          (analyze-qualified-symbol cenv env sym form))

      ;; a ClojureScript namespace that EXISTS in the world - something named it -
      ;; but that nothing compiled. cljs.core by name comes here too: the compiler
      ;; itself emits references to it (see the emitter's nameable-namespaces), so
      ;; it cannot be a global whatever a given environment happens to hold.
      (or (= 'cljs.core nsym) (some? (env/find-cljs-ns cenv nsym)))
      (analysis-error form
                      (str "No such namespace: " nsym
                           ". " env/*current-ns* " neither is it nor requires"
                           " it - add it to the ns form."))

      ;; (:refer-global :only [Promise]) then Promise/resolve. The bare name is a
      ;; refer (see analyze-symbol), and this is the same refer used as a PREFIX -
      ;; still one name standing for a JavaScript global, with a property read off
      ;; it. It resolves the same way as the fallthrough below and differs in one
      ;; thing: the namespace SAID this name is the host's, so there is nothing to
      ;; warn about, and a :rename is honoured - Bar/baz is js/Foo.baz when the ns
      ;; form renamed Foo to Bar.
      ;;
      ;; cljs/async_await_test.cljs is the case: (:refer-global :only [Date Promise])
      ;; and then (Promise/resolve 0) thirteen times, each of which would otherwise
      ;; be an undeclared-ns warning against a declaration sitting six lines above.
      (contains? (env/global-refers cenv env/*current-ns*) nsym)
      (let [g (get (env/global-refers cenv env/*current-ns*) nsym)]
        (js-var-node env (symbol "js" (str (name g) "." (name sym))) form))

      ;; nothing anywhere knows this prefix, so it is a JavaScript global
      :else
      (do (when-not (contains? implicit-nses nsym)
            (warning :undeclared-ns env {:ns-sym nsym :sym form}))
          (js-var-node env (symbol "js" (str nsym "." (name sym))) form))))))

(defn- analyze-dotted-symbol
  "cljs.core.Var - a simple symbol with dots in it, which is a name in ONE piece
  where the reader would have given us two had it been written cljs.core/Var.

  cljs.analyzer's rule, and this follows it (analyzer.cljc:1313). Two readings, in
  this order:

    the FIRST dot splits a value from its properties, when the head names one.
    (.-x p) is how a property is normally written, but p.x is legal too, and a
    local wins over any namespace of the same name - so this is asked first.

    otherwise a NAMESPACE splits from a name, and cljs.core.Var is cljs.core/Var.
    UNCHECKED, which is not our choice but theirs and is load bearing: core.cljs
    writes (instance? cljs.core.Var v) at line 1162 and defines Var at 1186.
    Rewriting to the qualified symbol is how it is done rather than a shortcut -
    everything analyze-qualified-symbol decides about a prefix (a goog namespace
    needs its require, cljs.core is never a global, an unknown prefix is one and
    warns) is decided the same way here, because it is the same question.

    WHICH dot is the split is the LONGEST PREFIX THAT NAMES A NAMESPACE, not the
    last dot. cljs.core.PersistentQueue.EMPTY is the var PersistentQueue in
    cljs.core and then its EMPTY property, and splitting at the last dot made it a
    var called EMPTY in a namespace called cljs.core.PersistentQueue - which is
    nothing, so it fell through to a JavaScript global and the emitted
    cljs.core.PersistentQueue.EMPTY was a ReferenceError at load. Their tests
    write it four times. ClojureScript needs no such rule because there the
    fallthrough IS the right answer: a var is a global path, so the name it could
    not resolve happens to be the name it wanted.

    Falling back to the last dot when nothing resolves keeps Foo.Bar.baz a
    JavaScript global, which is what §5.8 says it is.

  What ClojureScript emits for the second reading is the global path cljs.core.Var
  and what we emit is cljs$core$ns.Var, for the reason §5.2 gives everywhere else."
  [cenv env sym]
  (let [s    (str sym)
        head (symbol (subs s 0 (.indexOf s ".")))]
    ;; env/resolve-var rather than getMapping, and it is the same argument
    ;; env/resolve-var's own docstring makes: a core name is REFERRED without
    ;; being mapped (doc/cljs-compiler.md 5.12), so getMapping answers no for
    ;; PersistentVector and the whole name fell through to a JavaScript global -
    ;; PersistentVector.EMPTY, a ReferenceError at load. cljs.analyzer resolves the
    ;; prefix with a full resolve-var here too (its dotted-symbol? branch).
    (if (or (contains? (:locals env) head)
            (some? (env/resolve-var cenv head)))
      (analyze cenv env
               (reduce (fn [target prop] (list '. target (symbol (str "-" prop))))
                       head
                       (rest (clojure.string/split s #"\."))))
      (let [segs (clojure.string/split s #"\.")
            i    (or (first (for [k (range (dec (count segs)) 0 -1)
                                  :let [p (clojure.string/join "." (take k segs))]
                                  :when (some? (env/resolve-ns cenv (symbol p)))]
                              (count p)))
                     (.lastIndexOf s "."))]
        (analyze-qualified-symbol
         cenv env
         (with-meta (symbol (subs s 0 i) (subs s (inc i)))
           (assoc (meta sym) ::no-resolve true))
         sym)))))

(defn- analyze-symbol [cenv env sym]
  (if-let [b (get-in env [:locals sym])]
    (if (= :field (:local b))
      ;; a deftype field is not a local at all - it is a property of the object the
      ;; method was called on, and the bare name is sugar for reading it. Rewritten
      ;; to the form rather than built as a node, so that the object's own name goes
      ;; through ordinary local resolution: shadowing, closing over it from a nested
      ;; fn and set! on a mutable field all then work with no code of their own.
      ;;
      ;; The rewritten form remembers which field it reads and where its name was
      ;; written, so clojure.cljs.analysis can count it as a use of the field.
      ;; Under keys of their own rather than :line, for macroexpand/host-sugar's
      ;; reason: a :line here would be a position source maps read.
      (analyze cenv env
               (cond-> (list '. (:self b) (symbol (str "-" (:name b))))
                 (:line (meta sym))
                 (with-meta {::field-of (:js-name b)
                             :clojure.cljs.macroexpand/written
                             (select-keys (meta sym) [:line :column :end-line :end-column])})))
      (local-node env sym b))
    (if (namespace sym)
      (if (= "js" (namespace sym))
        (analyze-js-symbol cenv env sym)
        (analyze-qualified-symbol cenv env sym))
      ;; env/resolve-var, not getMapping: a referred var resolves, and so does a
      ;; cljs.core one, which is the refer half of the implicit require
      ;; (doc/cljs-compiler.md §5.12) - the half that makes an unqualified `reduce`
      ;; mean something.
      ;;
      ;; ASKED THERE RATHER THAN HERE because a macro asks the same question and
      ;; has to get the same answer; env/resolve-var's docstring has the argument,
      ;; and the fourteen cljs.core protocols defrecord extends in its expansion
      ;; are what happens when the two disagree.
      (let [^Namespace here (env/cljs-ns cenv)
            ^Var v (env/resolve-var cenv sym)
            ;; (:require ["react" :refer [useState]]) - a bare name drawn out of a
            ;; JavaScript module. {name [specifier export]}, or nil.
            js-ref (get (env/js-refers cenv env/*current-ns*) sym)
            ;; (:require [goog.string :refer [format]]) - a bare name drawn out of
            ;; a Closure namespace. The QUALIFIED symbol it stands for, or nil.
            gg-ref (get (env/goog-refers cenv env/*current-ns*) sym)
            ;; is `v` a mapping of THIS namespace - a def, or a :refer of a var -
            ;; rather than the cljs.core one resolve-var falls back to? That is the
            ;; whole of the ordering question below, and asking it costs one lookup
            ;; in the only case that can be in doubt.
            mine?  (fn [] (instance? Var (.getMapping here sym)))]
        (cond
          ;; A JS REFER IS A REFER, so it sits exactly where a cljs one does: below
          ;; anything this namespace defines or refers itself, and ABOVE the
          ;; implicit refer of cljs.core (doc/cljs-compiler.md §5.12). Without the
          ;; second half, (:require ["react-dom" :refer [render]]) would resolve to
          ;; nothing at all today and to cljs.core/render the day core grew one,
          ;; which is a name silently changing meaning under a program.
          (and (some? v) (or (and (nil? js-ref) (nil? gg-ref)) (mine?)))
          (var-node env v sym)

          (some? js-ref)
          (js-module-var-node env (first js-ref) (second js-ref) sym)

          ;; A GOOG REFER IS A REFER too, so it sits in the same slot a JS one
          ;; does and for the identical reason - below what this namespace defines
          ;; or refers itself, above the implicit refer of cljs.core. `format` is
          ;; the name that makes the second half concrete rather than hypothetical:
          ;; it is what lambdaisland.deep-diff2 refers out of goog.string, and
          ;; cljs.core has no format TODAY.
          ;;
          ;; Handed to analyze-qualified-symbol rather than turned into a node
          ;; here, which is the whole of why this branch is one line. That function
          ;; already reads a goog name both ways - goog.string/format is the
          ;; PROVIDE of that name, gobject/get is a property of a namespace object
          ;; - and already records the require, checks a reduced namespace's var
          ;; list and refuses a name we do not have. A refer decides none of that
          ;; and must not: it says only which qualified name was meant.
          ;;
          ;; `sym` is passed as the form so every message and every node names what
          ;; the source actually wrote, which is the bare name.
          (some? gg-ref) (analyze-qualified-symbol cenv env gg-ref sym)

          ;; (:refer-global :only [Object]) - a bare name this namespace said is
          ;; the host's. AFTER the var, which is what makes it a refer rather than
          ;; a shadow: a def of the same name in this namespace wins, exactly as a
          ;; def wins over a :refer of a var.
          (contains? (env/global-refers cenv env/*current-ns*) sym)
          (analyze-js-symbol
           cenv env (get (env/global-refers cenv env/*current-ns*) sym))

          ;; goog.math.Long written out in full. A simple symbol with dots, so it
          ;; arrives here rather than at analyze-qualified-symbol. Asked BEFORE the
          ;; dotted rule below, which would split it at its last dot and go looking
          ;; for a Long in goog.math - a namespace that exists and is not the one
          ;; named. A provide is one name, not a var in a shorter one.
          ;;
          ;; Writing it out is the require; see require-goog!. cljs.spec.alpha is
          ;; the case, at alpha.cljs:1463 - (instance? goog.math.Long val), in a
          ;; namespace whose ns form mentions goog.object and nothing else.
          (and (goog/goog-ns? sym) (goog/known? sym))
          (goog-ns-node env (require-goog! cenv sym))

          ;; (:import [goog.string StringBuffer]) is an alias from the bare name to
          ;; the provide, so a bare StringBuffer is that class. Aliases are looked
          ;; up AFTER vars: a def of the same name in this namespace wins, which is
          ;; the reading every other shadowing rule here has.
          ;; (:require ["react" :as React]) then React alone - the module object
          ;; itself. Beside the :import alias below, and read the same way: a name
          ;; the ns form gave to something, used as a value.
          (contains? (env/js-aliases cenv env/*current-ns*) sym)
          ;; the module itself, or - when the specifier's $ named a path into it -
          ;; what sits at that path, which is a property read and not a module
          (let [[specifier path] (get (env/js-aliases cenv env/*current-ns*) sym)]
            (if path
              (js-module-var-node env specifier path sym)
              (js-module-node env specifier sym)))

          :else
          (if-let [^Namespace aliased (.lookupAlias here sym)]
            (if (closure-ns? cenv (.getName aliased))
              (goog-ns-node env (.getName aliased))
              (analysis-error sym (str sym " is a namespace alias, not a value.")))
            ;; a.b - not a var, not a goog name, not an alias, so the dots are
            ;; structure rather than part of one name
            (if (clojure.string/includes? (str sym) ".")
              (analyze-dotted-symbol cenv env sym)
              (analysis-error sym (str "the symbol " sym
                                       " is neither a local nor a var in "
                                       env/*current-ns* (removed-note sym))))))))))

(defn- analyze-seq [cenv env form]
  ;; WHERE :line AND :column ENTER &env, and the only place they could: this is
  ;; the sole call site of macroexpand-1 in the analyzer, so it is the sole moment
  ;; at which an &env is handed to somebody else's code.
  ;;
  ;; A macro reads (:line &env) because it wants to record WHERE IT WAS CALLED -
  ;; an i18n extractor keying a translation by file and line is the case that
  ;; asked for this, and cljs.analyzer's analyze-seq (analyzer.cljc:4352) puts the
  ;; two keys there for it. (meta &form) answers the same question and is already
  ;; there, but only for a call the READER read: a macro call built by another
  ;; macro's expansion carries no metadata at all, for the reason parse-deftype
  ;; gives above - syntax-quote does not copy &form's. Hence the inheritance, and
  ;; it is what &form alone cannot do.
  ;;
  ;; THE INHERITED POSITION TRAVELS UNDER A NAMESPACED KEY AND NOT AS :line, which
  ;; is the whole difference between this and upstream's version. Upstream assocs
  ;; :line and :column onto the env it threads onward, so every node it builds ends
  ;; up carrying a position and its source maps are made of them. Here positions on
  ;; nodes belong to clojure.cljs.source-info, which walks the finished tree with
  ;; the same rule - own position, else the nearest enclosing one - and its own
  ;; docstring says why analysis does not do it: `threading them through every
  ;; analyze call' is a larger change than that pass, not a free side effect of
  ;; this one. Two sources of truth for a node's line is the failure to avoid, and
  ;; ::position is invisible to source-info's position-keys and to the emitter's
  ;; node-pos, so there is only ever one.
  ;;
  ;; :line and :column MOVE AS A GROUP, and a form has a position at all only if it
  ;; has a :line - source-info/own-position reads reader metadata the same way.
  (let [m   (meta form)
        pos (if (:line m) (select-keys m [:line :column]) (::position env))
        env (cond-> env pos (assoc ::position pos))
        form' (mx/macroexpand-1 cenv (merge env pos) form)]
    (if-not (identical? form form')
      (analyze cenv env form')
      (let [op (first form)]
        (if-let [parse (get parsers op)]
          (parse cenv env form)
          ;; anything else in head position is a function call. An unresolvable
          ;; head symbol fails in analyze-symbol, which says so precisely.
          (parse-invoke cenv env form))))))

;; --- the collection literals -------------------------------------------------
;;
;; A collection literal is not a constant, because its elements are EXPRESSIONS:
;; [a (f b)] has to evaluate two of them, in that order, before it can build
;; anything. So each gets a node of its own, with the elements as children, and
;; the emitter turns the parts into a call to whichever cljs.core constructor
;; fits - which is why these could not land before core.cljc and core.cljs did
;; (doc/cljs-compiler.md §5.7).
;;
;; QUOTED data goes the other way: 'a and '(1 2) are constants all the way down,
;; nothing in them evaluates, and one :const node carries the whole structure.
;; That is cljs.analyzer's split too, and it is the reason parse-quote can now
;; simply stop refusing collections.

(defn- wrap-meta
  "`node`, wrapped in the with-meta its form asks for.

  METADATA ON A LITERAL IS PART OF THE VALUE, and until now it was dropped: a
  program could write ^{:b :c} [1 2] and read nil back off it. The reader's own
  position keys are not part of it (reader/program-meta), which is the whole
  reason this is not simply (meta form) - every collection carries a line number.

  cljs.analyzer's analyze-wrap-meta (analyzer.cljc:4460) and the same node: the
  metadata is a MAP LITERAL, analyzed like any other, so a value in it is an
  expression and gets evaluated. It sits outside the collection rather than inside
  it because that is the order Clojure evaluates in - the collection first, then
  the metadata that goes on it.

  Applied to fn* as well, which is what cljs.analyzer does - a function is a
  value, and (meta ^:foo (fn [])) is a program reading its own metadata back. The
  marks this compiler reads itself, ^:async and the fn's own name, are on the HEAD
  symbol rather than on the form, so wrapping the form cannot turn one of them
  into a runtime with-meta call. Collections, quoted data and functions are what a
  program reads meta off - see the emitter's const-js for the quoted half."
  [cenv env form node]
  (if-let [m (reader/program-meta form)]
    {:op :with-meta :form form :env env
     :expr node
     :meta (analyze cenv (not-tail env) m)
     :children [:expr :meta]}
    node))

(defn- analyze-vector [cenv env form]
  (wrap-meta
   cenv env form
   {:op :vector :form form :env env
    :items (mapv #(analyze cenv env %) form)
    :children [:items]}))

(defn- analyze-map [cenv env form]
  ;; keys and vals are read off the SAME map object, so the two vectors line up
  ;; positionally however the map orders itself. Written order survives for the
  ;; array maps a literal usually is, which is the order Clojure evaluates in.
  (wrap-meta
   cenv env form
   {:op :map :form form :env env
    :keys (mapv #(analyze cenv env %) (keys form))
    :vals (mapv #(analyze cenv env %) (vals form))
    :children [:keys :vals]}))

(defn- analyze-set [cenv env form]
  (wrap-meta
   cenv env form
   {:op :set :form form :env env
    :items (mapv #(analyze cenv env %) form)
    :children [:items]}))

(defn- analyze-js-value
  "#js [1 2] and #js {:a x}, which the reader wrapped rather than built.

  An object's KEYS are not analyzed and never could be: they are JavaScript
  property names, spelled the host's way like every other property (§5.3), so
  #js {:a 1} and #js {\"a\" 1} are the same object. Only the values are code."
  [cenv env form]
  (let [v (.-val ^JSValue form)]
    (if (map? v)
      {:op :js-object :form form :env env
       :keys (vec (keys v))
       :vals (mapv #(analyze cenv env %) (vals v))
       :children [:vals]}
      {:op :js-array :form form :env env
       :items (mapv #(analyze cenv env %) v)
       :children [:items]})))

(defn analyze
  "AST for `form` in `env`. Macroexpands first, so callers hand in source."
  [cenv env form]
  (cond
    (seq? form)    (if (seq form)
                     (analyze-seq cenv env form)
                     ;; () is the empty list, and it is a VALUE rather than a
                     ;; call: cljs.core.List.EMPTY, which emit-const builds like
                     ;; any other constant seq. Left as the literal text `()` it
                     ;; was a syntax error that took the module with it.
                     (const-node env form))
    (symbol? form) (analyze-symbol cenv env form)
    (number? form)
    ;; JavaScript has one number type, so 10N and 1.5M simply become doubles, as
    ;; cljs.compiler makes them. A Ratio is the one number with no reading at all
    ;; there, and ClojureScript refuses it in the same words.
    (if (ratio? form)
      (unsupported form (str "the ratio " (pr-str form)
                             " - clojure.lang.Ratio is not a valid ClojureScript"
                             " constant"))
      (const-node env form))

    ;; BEFORE the map test, and it no longer HAS to be - kept because the reason
    ;; it had to be is a trap worth not re-laying. JSValue was a defrecord here
    ;; once, and a record is a map, so #js {:a 1} reaching the map test first was
    ;; analyzed as a Clojure map literal of one entry whose key was :val.
    ;; ClojureScript's own JSValue is a deftype and is not a map, which is also
    ;; why upstream can afford to test it last (analyzer.cljc, -item-to-ssa in
    ;; core.async) - and why this compiler now shares the type rather than
    ;; declaring a second one (doc/cljs-compiler.md 5.68).
    (instance? JSValue form) (analyze-js-value cenv env form)

    (vector? form) (analyze-vector cenv env form)
    (map? form)    (analyze-map cenv env form)
    (set? form)    (analyze-set cenv env form)

    (or (nil? form) (string? form) (boolean? form) (keyword? form)
        ;; a character is a one-character string in ClojureScript, and a regex is
        ;; a JavaScript regex literal - neither needs cljs.core, and both were
        ;; only ever refused because nothing looked at them
        (char? form) (instance? java.util.regex.Pattern form)
        ;; #uuid, which is CLOJURE'S tagged literal - the reader builds it from
        ;; default-data-readers with no help from us, so what was missing was only
        ;; somewhere for the value to go - and #inst, which is Clojure's tag read
        ;; ClojureScript'S WAY: an Instant rather than a Date, because a Date is
        ;; Julian before 1582 and a JavaScript Date is not (clojure.cljs.reader's
        ;; cljs-data-readers has the argument). The emitter spells both.
        ;;
        ;; #queue needs no case here at all - reader/read-queue hands back a form
        ;; rather than a value.
        (instance? java.time.Instant form) (instance? java.util.UUID form))
    (const-node env form)

    ;; A JVM VAR, WHICH IS NOT A CLOJURESCRIPT VALUE AND COULD NOT BE: a var here
    ;; is a property of a namespace object (§5.2), and clojure.lang.Var is the
    ;; other world's object entirely. Nothing a reader produces is one either -
    ;; #'foo reads as (var foo), which parse-var handles and which is a different
    ;; form. So one arrives from exactly one place: a macro that returned it.
    ;;
    ;; AND A MACRO RETURNS ONE BY ACCIDENT. `def` evaluates to the var it
    ;; interned, so a macro whose body ends in a def hands that var back as its
    ;; expansion, having meant only the interning. sci.impl.cljs does it:
    ;; (require-cljs-analyzer-api) exists to require cljs.analyzer.api and intern
    ;; two JVM vars WHILE EXPANDING, and its last form is a def, so what it
    ;; expands to is #'sci.impl.cljs/cljs-find-ns.
    ;;
    ;; It is therefore a constant with no spelling, and cljs.analyzer makes
    ;; exactly that of it: analyze-form's :else branch, :op :const, and
    ;; emit-constant* has no method for a Var. That survives because of WHERE such
    ;; a form sits. The macro was called for its effect, at the top level, where
    ;; the value is discarded - and a discarded constant is never spelled at all.
    ;; Upstream drops it in emit* :const, which skips a :statement context before
    ;; it reaches emit-constant*; ours has no context to read, so emitter/unspellable
    ;; carries the refusal into the expression channel and lets it be dropped
    ;; unread. The two agree in both positions: nothing as a statement, and a
    ;; refusal anywhere the value is actually wanted.
    (instance? clojure.lang.Var form) (const-node env form)

    :else (unsupported form (str "a " (.getSimpleName (class form)) " literal"))))

(defn analyze-top
  "Analyze one top-level form. Establishes a name scope if the caller has not -
  but a caller compiling several forms into one JavaScript scope must wrap them
  together in one clojure.cljs.names/with-name-scope."
  [cenv env form]
  (binding [*cljs-ns* env/*current-ns*]
    (names/with-name-scope* #(analyze cenv (assoc env :top-level? true) form))))

;; --- the surface cljs.core's macros reach for --------------------------------
;;
;; Six names, and they exist because the VENDORED cljs/core.cljc calls them
;; (doc/cljs-compiler.md §4.4 and M5). They are not a compatibility layer bolted
;; on: resolving a symbol and reporting a warning are things any front end does,
;; and cljs.analyzer's spelling of them is as good as one we would invent - which
;; is borne out by `warning`, whose first caller inside the compiler proper is
;; analyze-qualified-symbol (doc/cljs-compiler.md §5.8) rather than core.cljc.
;;
;; What is adapted rather than mirrored is the ENVIRONMENT argument. cljs.analyzer
;; threads its compile state through cljs.env/*compiler*, so its resolve-var reads
;; `env` for :ns and the dynamic var for the rest; ours lives in a CompileEnv that
;; a macro reaches through clojure.cljs.env/*cenv* (see its docstring for why that
;; one dynamic var is not a slip). So `env` is accepted and ignored here, and the
;; namespace resolution happens in is the one being compiled - which is what every
;; call site means by it.

(def ^:dynamic *cljs-warnings*
  "Which warnings are on. cljs.analyzer's map has 30-odd keys and a handler chain;
  this is the same map with every key defaulting to true and one handler, and it
  is here so that a `(:undeclared ana/*cljs-warnings*)` in core.cljc reads as it
  was written. Rebind to a map of false to silence a form."
  {})

(defn warning
  "Report a compile-time warning of `type` about `info`.

  cljs.analyzer formats each type into a sentence through a multimethod and sends
  it to a handler chain. Until there is something to hand warnings to, this prints
  the type and the data - which is strictly more information than a formatted
  message, and is the shape a real handler would receive anyway."
  [type env info]
  (when (get *cljs-warnings* type true)
    (binding [*out* *err*]
      (println (str "WARNING: " (name type) " " (pr-str info)
                    " in " env/*current-ns*)))))

(defn confirm-var-exists-throw
  "The `confirm` argument that makes an unresolvable symbol an error rather than a
  warning. cljs.analyzer returns a function of [env prefix suffix]; the shape is
  kept so a call site reads unchanged."
  []
  (fn [env prefix suffix]
    (throw (ex-info (str "No such var: " prefix "/" suffix)
                    {:ns prefix :sym suffix}))))

(defn confirm-var-exist-warning
  "The `confirm` argument that warns instead."
  [env prefix suffix]
  (warning :undeclared-var env {:prefix prefix :suffix suffix}))

(defn resolve-var
  "What `sym` names in the namespace being compiled, as a map - or nil.

  A MACRO's view of the symbol table. clojure.cljs.env/resolve-var answers with the
  Var itself; cljs.core's macros want :name (the qualified symbol), :ns, and
  whatever the def's metadata carried - :protocol-symbol, :protocol-info, :const,
  :deprecated - so the Var's metadata is merged under those two keys.

  `env` is accepted and ignored: see the section note above. `confirm` is called
  when nothing resolves, exactly as cljs.analyzer calls it."
  ([env sym] (resolve-var env sym nil))
  ([env sym confirm]
   (let [cenv (or env/*cenv*
                  (throw (ex-info (str "No compile environment - " sym " can only"
                                       " be resolved while a ClojureScript form is"
                                       " being macroexpanded.")
                                  {:sym sym})))]
     (or (when-let [^Var v (env/resolve-var cenv sym)]
           (assoc (meta v)
                  :name (symbol (str (.getName (.ns v))) (str (.sym v)))
                  :ns   (.getName (.ns v))))
         ;; NOTHING RESOLVED, and the answer is still a name. cljs.analyzer's
         ;; resolve* does the same, and it is not a lapse: a macro asks this
         ;; question about a name it is about to DEFINE as often as about one that
         ;; already exists. (defonce x 1) expands to (when-not (exists? x) ...)
         ;; and extend-type resolves Object before it notices that Object is not a
         ;; protocol - both of which need a qualified name for a var that is not
         ;; there. Being wrong about existence is the analyzer's business, and it
         ;; refuses the symbol itself when the expansion is analysed; `confirm` is
         ;; how a caller that does care asks to be told first.
         (let [ns (if-let [n (namespace sym)]
                    (symbol (if (= "clojure.core" n) "cljs.core" n))
                    env/*current-ns*)]
           (when confirm (confirm env ns (symbol (name sym))))
           {:name (symbol (str ns) (name sym)) :ns ns})))))

(defn resolve-existing-var
  "The var `sym` names, warning and answering nil when there is none.

  Unlike resolve-var, which synthesises: a caller reaching for this one is asking
  about a var that should already exist, and wants to know when it does not."
  [env sym]
  (when (some-> env/*cenv* (env/resolve-var sym))
    (resolve-var env sym)))
