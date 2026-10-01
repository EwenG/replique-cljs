// The pre-cljs.core prelude: everything emitted code needs that is not itself
// emitted. See doc/cljs-repl.md §3.1.
//
// It is reachable two ways, because its two callers cannot use the same one:
//
//   - a compiled module imports it, like any other dependency;
//   - a REPL form is evaluated as a *script*, and a script may not contain an
//     import declaration at all, so it reaches these functions through
//     globalThis.$CLJS instead.
//
// The registry therefore lives on globalThis rather than in this module's scope.
// That is also what makes reload work: a second instance of this module - the
// same file re-imported under a cache-busting query string - finds the
// namespaces that are already there instead of starting an empty world.

export const $CLJS = (globalThis.$CLJS ??= {
  namespaces: new Map(),
  loaded: new Set(),
  fetched: new Set(),
});

// The namespace object a var is a property of. Idempotent, so a reloaded module
// gets back the same object every existing reference already holds, which is what
// makes redefinition and reload land where the old definitions were.
export function ns(name) {
  let m = $CLJS.namespaces, o = m.get(name);
  if (o === undefined) { o = {}; m.set(name, o); }
  return o;
}

// ClojureScript truthiness is not JavaScript's: 0 and "" are true, and only nil
// and false are false.
export function truth_(x) { return x !== null && x !== undefined && x !== false; }

// Closure's COMPILED flag, which emitted ClojureScript reads as a BARE identifier
// (core.cljs guards a block with js/COMPILED). Closure's base.js declares it with
// `var COMPILED = false` at the top level of a script, which is a global; our goog
// subset is ES modules, where the same line would be module-scoped and invisible -
// so it is set here instead, and set on globalThis because that is the only scope a
// bare identifier in another module can reach.
//
// FALSE UNCONDITIONALLY, not ??=. Every other Closure default in goog/base.js uses
// ??= so that a real Closure already on the page wins; this one must not, because
// it is not a preference but a fact about the code we emit - nothing here is ever
// put through the Closure compiler, so a `true` from somebody else's bundle would
// send our code down a branch written for a build that did not happen. Overwriting
// theirs is the safer half of the trade: advanced compilation inlines COMPILED and
// drops the variable, so a compiled bundle is not reading this at run time.
globalThis.COMPILED = false;

// The `cljs` object a goog.provide build publishes as a global. Nothing WE emit
// reads it - a var here is a property of a namespace object (doc/cljs-compiler.md
// 5.2) and a module reaches those through $ns - but code we did not write does:
// cljs-bean asks for (.. js/cljs -core -PersistentArrayMap -EMPTY), wanting the
// empty map's identity rather than a value, and 339 of nosco-gamma's 684 modules
// stop there.
//
// A VIEW AND NOT A COPY. `core` is the object ns() hands every module, so a read
// finds the real type - and cljs-bean's two set!s of PersistentArrayMap.EMPTY land
// on the real one too. A synthesised object would get the read right and the
// writes silently wrong, which is the worse half of that trade.
//
// ONE ROOT, because one is what was measured. Across every ClojureScript source on
// a 414-namespace application's classpath, exactly one library reaches for a global
// like this, and the only thing it asks of it is `core`.
//
// UNCONDITIONAL, as COMPILED above is, and with a sharper edge. If another
// ClojureScript bundle shares the page then globalThis.cljs is ITS namespace tree,
// and deferring would send our cljs-bean at its PersistentArrayMap - a different
// type of the same name, and every wrong answer silent. Two runtimes on one page is
// broken either way; being broken in our own favour is the half we can reason about.
//
// AND IT IS THE EXCEPTION RATHER THAN THE RULE. js/goog is deliberately NOT
// published here - analyzer/analyze-js-symbol resolves it instead, to keep our
// Closure subset isolated from a Closure the user's project bundles. This goes the
// other way because nothing can resolve `js/cljs` at compile time: what cljs-bean
// reads off it are three host property accesses, not a name this compiler ever sees
// whole. See doc/cljs-compiler.md 5.60.
globalThis.cljs = { core: ns("cljs.core") };

$CLJS.ns = ns;
$CLJS.truth_ = truth_;

// --- names ------------------------------------------------------------------
//
// clojure.cljs.names/code-map, STATED A SECOND TIME, for urlFor's reason one
// section down: a name computed HERE has nothing to ask the JVM. names_test holds
// the two to each other over the same alphabet that proves munge injective, which
// is the only thing keeping them from drifting apart.
//
// WHAT NEEDS IT is a var looked up by a name that is a string at run time rather
// than a symbol at compile time - lazy loading, where the thing to fetch is named
// by `"the.ns/the-var"` and the module holding it is not loaded yet, so there was
// no compile-time reference to munge. `$CLJS.ns(ns)[munge(v)]` is then the whole
// of the lookup, because a var IS a property of its namespace object (def-name in
// clojure.cljs.emitter, doc/cljs-repl.md §3.1).
//
// NOT cljs.core/munge, which is the same idea and a DIFFERENT map: it delimits
// its codes with _ and appends $ to JavaScript reserved words, where ours delimits
// with $ and reserves nothing. nosco-gamma's file->wb-promise is file_$GT$wb_promise
// here and file__GT_wb_promise there - a property that does not exist. The two are
// not interchangeable and the name they disagree about is an ordinary one.
const CODE_MAP = {
  // the three that make it injective: - is the common case, and the other two
  // escape the characters the output would otherwise be ambiguous about
  "-": "_", "_": "$US$", "$": "$DL$",
  ":": "$COLON$", "+": "$PLUS$", ">": "$GT$", "<": "$LT$", "=": "$EQ$",
  "~": "$TILDE$", "!": "$BANG$", "@": "$CIRCA$", "#": "$SHARP$",
  "'": "$SINGLEQUOTE$", '"': "$DOUBLEQUOTE$", "%": "$PERCENT$", "^": "$CARET$",
  "&": "$AMPERSAND$", "*": "$STAR$", "|": "$BAR$", "{": "$LBRACE$",
  "}": "$RBRACE$", "[": "$LBRACK$", "]": "$RBRACK$", "/": "$SLASH$",
  "\\": "$BSLASH$", "?": "$QMARK$",
};

// A plain object is safe to index with an unknown character because every key on
// Object.prototype is more than one character long, and a key here never is.
export function munge(name) {
  let out = "";
  for (const c of name) out += CODE_MAP[c] ?? c;
  return out;
}

$CLJS.munge = munge;

// --- the protocol calling convention ----------------------------------------
//
// doc/cljs-compiler.md §5.4. An implementation lives on the object, under a
// property name computed from the protocol and the method alone
// (clojure.cljs.names/protocol-method-name), and a call site spells that name for
// itself - so nothing here is consulted on the fast path. These three are the slow
// path: what to do for a value that has no such property, which is every native
// JavaScript value, because null has no prototype to install one on and String's
// belongs to the host.

// The key a native extension is filed under. goog.typeOf, minus goog: the names
// are ClojureScript's, because (extend-type string ...) and (extend-type array
// ...) are what people write. null and undefined share one key, as they share one
// nil.
export function typeOf(x) {
  if (x === null || x === undefined) return "null";
  const t = typeof x;
  if (t !== "object") return t;           // string number boolean function bigint symbol
  return Array.isArray(x) ? "array" : "object";
}

// The implementation of one protocol method for a native value, or a throw naming
// what was missing. Returns the function rather than calling it, so the call site
// keeps its own argument list and this needs no arity of its own.
export function nativeImpl(method, x, name) {
  const f = method[typeOf(x)] ?? method["_"];
  if (f === undefined || f === null) {
    throw new Error("No implementation of method " + name + " found for "
                    + typeOf(x) + ": " + print(x));
  }
  return f;
}

// Does a native value satisfy a protocol? Every extension marks the protocol
// object as well as the method, so this asks one question instead of one per
// method.
export function nativeSatisfies(protocol, x) {
  return protocol[typeOf(x)] === true || protocol["_"] === true;
}

$CLJS.typeOf = typeOf;
$CLJS.nativeImpl = nativeImpl;
$CLJS.nativeSatisfies = nativeSatisfies;

// --- loading ----------------------------------------------------------------
//
// doc/cljs-repl.md §7.2: dependencies are the client's problem. The JVM never
// models what this runtime holds, so what it ships is idempotent and this decides
// for itself whether anything has to be fetched.

// The output layout, stated a second time - see clojure.cljs.output, which states
// it in Clojure and whose test runs the two against each other. It has to be
// stated here because require computes a URL from a name with nothing to ask the
// JVM. Relative, so it resolves against this file's own URL: from a filesystem
// under node and from an HTTP origin in a browser, with no difference in the text.
export function urlFor(name) {
  // goog is not a ClojureScript namespace and does not live under ns/. The rule
  // inside its tree is the same one - dots to slashes - which is exactly why the
  // Closure subset is written out at names derived from its provides rather than
  // at Closure's own layout: goog.asserts is asserts/asserts.js upstream, and no
  // rule connects those, so a require would have needed a manifest to look in.
  // See clojure.cljs.goog/ns->path, and §7.3 for why a manifest is not available.
  if (name === "goog" || name.startsWith("goog.")) {
    return "./goog-subset/" + name.replace(/\./g, "/") + ".js";
  }
  return "./ns/" + name.replace(/\./g, "/") + ".js";
}

// The same rule for a JavaScript module a string require named, and the second
// statement of clojure.cljs.output/js->path - stated here for urlFor's reason, and
// kept in step with the JVM half by the same test. The specifier IS the path: what
// npm calls react is npm/react.js here, and react-dom/client is a file two levels
// down. Nothing is escaped, because a specifier is already a path made of names -
// output/js->path refuses one that is not.
export function urlForJs(specifier) {
  return "./npm/" + specifier + ".js";
}

// What a MODULE spells as `import * as react$js from "../../npm/react.js"`, for a
// script, which may contain no import declaration. It returns the module namespace
// object, which is what the import statement binds - so the two bind the same name
// to the same thing and the body between them is identical (doc/cljs-repl.md §4).
//
// No bookkeeping of its own, unlike require_ below. A namespace can be redefined at
// a REPL and must not be fetched back over the top; an npm module is built by a
// bundler and is never redefined from here, so the module system's own cache - one
// evaluation per URL - is the whole of what is needed.
function requireJs_(specifier) {
  return import(urlForJs(specifier));
}

// TWO FACTS, TWO SETS, and telling them apart is what keeps a reload from
// undoing itself:
//
//   loaded   this namespace's definitions are live here. Set by a body, whether
//            that body arrived as a module or as a script the REPL shipped.
//   fetched  this namespace's FILE has been through the module system at least
//            once, so the module system will never evaluate it again - it returns
//            the cached module instead.
//
// The second one exists because an import statement consults the module system's
// own registry and not `loaded`. A namespace whose definitions arrived as a
// shipped body is live but unfetched, and the next cold-loaded module that
// imports it would evaluate the file straight over the top, silently reverting
// whatever the REPL had redefined since.
//
// Nothing here marks `fetched`: a MODULE marks itself, in the line the compiler
// emits at the top of it. That is the only complete rule, because a module body
// runs if and only if the module system evaluated the file - and it reaches that
// point by a static import inside another module just as often as by this
// function, which would never see it.
function fetch_(name) {
  return import(urlFor(name));
}

// Checked BEFORE the import, not after. A namespace redefined at the REPL and not
// yet written to disk would otherwise be silently reverted to its on-disk version
// by the next require that reached it.
function require_(name) {
  return $CLJS.loaded.has(name) ? null : fetch_(name);
}

$CLJS.urlFor = urlFor;
$CLJS.urlForJs = urlForJs;
$CLJS.fetch = fetch_;
$CLJS.require = require_;
$CLJS.requireJs = requireJs_;

// --- printing ---------------------------------------------------------------
//
// doc/cljs-repl.md §8: a value is printed in the RUNTIME and travels as a string.
// Until cljs.core is LOADED HERE there is no pr-str, so this prints JavaScript
// values as JavaScript values rather than pretending otherwise.
//
// That hand-off landed with M5 and is prStr below: anything cljs.core owns is
// printed by cljs.core/pr-str, and everything else keeps the JavaScript printing
// here - a JavaScript object is still a JavaScript object. What remains below is
// the fallback, and the two places it is deliberately more precise than pr-str:
// undefined is not nil, and -0 is not 0.

const MAX_DEPTH = 8;

function printNumber(n) {
  if (Number.isNaN(n)) return "##NaN";
  if (n === Infinity) return "##Inf";
  if (n === -Infinity) return "##-Inf";
  // -0 prints as 0 through String, and the difference is one a compiler cares
  // about: it is what distinguishes (/ -1 ##Inf) from 0.
  return Object.is(n, -0) ? "-0" : String(n);
}

// `seen` is the cycle guard and `depth` the size guard. Both are needed: a cycle
// never terminates, and a deep-but-finite object would print a page of noise
// where the REPL wants a line.
function printAt(x, depth, seen) {
  if (x === null) return "nil";
  // NOT folded into nil, though ClojureScript treats both as false. undefined
  // arrives from a JavaScript function that returned nothing, and while this
  // compiler is being written that is more often a bug than a value.
  if (x === undefined) return "undefined";
  switch (typeof x) {
    case "boolean":  return String(x);
    case "number":   return printNumber(x);
    case "bigint":   return String(x) + "N";
    case "string":   return JSON.stringify(x);
    case "symbol":   return String(x);
    case "function": return "#object[Function " + (x.name || "anonymous") + "]";
  }
  if (seen.has(x)) return "#object[circular]";
  if (depth >= MAX_DEPTH) return Array.isArray(x) ? "#js [...]" : "#js {...}";
  if (x instanceof Error) return "#object[" + x.name + " " + x.message + "]";
  seen.add(x);
  try {
    if (Array.isArray(x))
      return "#js [" + x.map((v) => printAt(v, depth + 1, seen)).join(" ") + "]";
    const proto = Object.getPrototypeOf(x);
    if (proto !== Object.prototype && proto !== null)
      return "#object[" + ((x.constructor && x.constructor.name) || "Object") + "]";
    return "#js {" + Object.keys(x).map(
      (k) => JSON.stringify(k) + " " + printAt(x[k], depth + 1, seen)).join(", ") + "}";
  } finally {
    seen.delete(x);
  }
}

// cljs.core's printer, once there is one. A ClojureScript value knows how to print
// itself and nothing here could do it as well - a vector is [1 2 3] and not
// #object[PersistentVector].
//
// Looked up per call rather than cached, because a REPL loads cljs.core AFTER this
// module is evaluated and may reload it later; the cost is one property read.
// Nothing is imported: this module is the prelude and cljs.core is above it.
function prStr(x) {
  const core = $CLJS.namespaces.get("cljs.core"), f = core && core.pr_str;
  return f && f.cljs$core$IFn$_invoke$arity$variadic
    ? f.cljs$core$IFn$_invoke$arity$variadic(core.list.call(null, x))
    : null;
}

export function print(x) {
  // A getter can throw, and a REPL that dies while printing an answer it already
  // has is worse than one that says it could not print it.
  try {
    // cljs.core FIRST and JavaScript second, rather than the other way round: what
    // a ClojureScript program returns is usually a ClojureScript value, and the
    // fallback below is what the host's own values still need.
    //
    // Only objects are offered, which is the whole of the rule. Every value
    // cljs.core owns is one - a keyword, a vector, a map - while a number, a string
    // and a boolean are the host's, and for those the two printers agree anyway
    // except where this one is deliberately more precise (undefined is not nil,
    // and -0 is not 0). An array stays #js [...] here because a JavaScript array is
    // not a ClojureScript value either; a plain object does go to pr-str, and comes
    // back as #js {:a 1}, which is ClojureScript's own spelling of one.
    if (x !== null && typeof x === "object" && !Array.isArray(x)) {
      try { const s = prStr(x); if (s !== null && s !== undefined) return s; }
      catch (_) { /* not a value cljs.core knows; print it as JavaScript */ }
    }
    return printAt(x, 0, new Set());
  }
  catch (e) { return "#object[unprintable " + String(e && e.message) + "]"; }
}

// --- evaluating -------------------------------------------------------------

// Indirect, so the script runs in GLOBAL scope rather than this module's: a REPL
// form must not be able to see the runtime's own bindings, and it may not contain
// an import, which is why it is a script in the first place (§3.1).
const $eval = eval;

// The result as EDN, not as an object, so the wire format is decided once here
// rather than once per transport - node's socket and the browser's long-poll ship
// the same string. JSON.stringify of a string is a valid EDN string literal: the
// escapes EDN knows are a superset of the ones it emits, minus \/, which V8 does
// not produce. It never emits a raw newline either, which is what lets a result be
// one line.
function resultEdn(status, value, stacktrace) {
  return "{:status :" + status + " :value " + JSON.stringify(value) +
    (stacktrace ? " :stacktrace " + JSON.stringify(stacktrace) : "") +
    paramsEdn() + "}";
}

// The printing the value went through, as cljs.core's vars hold it AFTER the
// script ran - so a form that set! one of them is answered with what it set,
// rather than with what was in force before it.
//
// HERE AND NOT IN THE FORM, for rememberError's reason turned around: the printer
// is this module's, and the values it printed under are properties of cljs.core's
// namespace object, read the way pr_str is above - munged by hand, looked up per
// call, and nothing at all where cljs.core is not loaded yet, which is no printing
// to describe. A REPL keeps them so that a page that reloads, and starts again
// with cljs.core's defaults, can be given back the ones the developer chose.
//
// Only what EDN can read back: a count that is not a whole number is no count.
function paramsEdn() {
  try {
    const core = $CLJS.namespaces.get("cljs.core");
    if (!core) return "";
    const count = (x) => Number.isInteger(x) ? String(x) : "nil";
    return " :params {:print-length " + count(core.$STAR$print_length$STAR$) +
      " :print-level " + count(core.$STAR$print_level$STAR$) +
      " :print-meta " + String(truth_(core.$STAR$print_meta$STAR$)) + "}";
  } catch (_) { return ""; }
}

// cljs.core/*e, which is the one piece of REPL history the compiled form cannot
// keep for itself: a form that throws runs nothing after it, so the only place that
// can see the throw is here. Its three companions - *1, *2 and *3 - are assigned by
// the form, in ClojureScript (clojure.cljs.repl/remembering).
//
// The property name is cljs.core/*e munged ($STAR$e), spelled out for the same
// reason pr_str is above: this module is the prelude and cljs.core is above it, so
// there is nothing to import and nothing to ask. Looked up per call, because a REPL
// loads cljs.core after this module is evaluated and may reload it later.
//
// EVERY failure of a turn, not only a form's: a prologue that cannot fetch a module
// throws before the form runs at all, and that is still the error the user is
// looking at.
function rememberError(e) {
  try {
    const core = $CLJS.namespaces.get("cljs.core");
    if (core) core.$STAR$e = e;
  } catch (_) { /* no cljs.core yet, or a frozen namespace object; not worth a turn */ }
}

// One failure, as the wire spells it, and the ONE place that decides how.
//
// EXPORTED, because a turn is not the only way a program can fail. An exception
// thrown out of a setTimeout callback, a rejected promise nobody caught, an error
// in an event handler - none of them belongs to an evaluation, because the form
// that scheduled the work answered long ago. Each host transport watches for those
// and hands them here, so that an error nobody was waiting for is reported exactly
// as one that was: same message, same stack, same *e. What differs is only which
// channel carries it, and that is the transport's business rather than this one's.
export function errorEdn(e) {
  // *e holds what was THROWN, not what it printed as, so (ex-data *e) works.
  rememberError(e);
  // JavaScript lets you throw anything. String() on a thrown object gives
  // "[object Object]", which tells a REPL user nothing, so anything that is not
  // an Error goes through the printer like any other value.
  return resultEdn("error",
                   e instanceof Error ? e.name + ": " + e.message : print(e),
                   (e && e.stack) ? String(e.stack) : "");
}

// Evaluate one script and say what happened. Never throws: a REPL turn that ends
// without an answer would leave the JVM waiting on a line that is not coming.
export async function evaluate(src) {
  try {
    // await, because the unit is an async IIFE - so a throw inside it arrives here
    // as a rejection, which is why the unit itself carries no try/catch (§5).
    return resultEdn("success", print(await $eval(src)));
  } catch (e) {
    return errorEdn(e);
  }
}

$CLJS.print = print;
$CLJS.evaluate = evaluate;

// --- saying something unasked -------------------------------------------------
//
// A runtime answers what it is asked, and prints; this is the third thing it
// can do, which is tell the JVM something nobody asked for at that moment - an
// atom an editor watches was swapped. What the string means is the business of
// whoever sends it and whoever the JVM hands it to, and nothing here reads it.
//
// The transport is what knows how to reach the JVM, so it is the transport that
// installs sendNotify; until one has, or where none ever will, this says false
// and nothing is sent.
export function notify(content) {
  const send = $CLJS.sendNotify;
  if (typeof send !== "function") return false;
  try { send(content); return true; } catch (_) { return false; }
}

$CLJS.notify = notify;
