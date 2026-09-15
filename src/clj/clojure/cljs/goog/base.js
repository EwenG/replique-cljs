// The `goog` object every vendored Closure Library file mutates, and the only
// file in this tree we wrote rather than vendored.
//
// See doc/cljs-compiler.md §5.5. The Closure Library is not shipped whole - the
// transitive closure of what cljs.core requires is 42 files and 18,458 lines,
// most of it reached by goog.string and goog.Uri pulling in the safe-HTML type
// system - so this tree holds the subset cljs.core actually uses, and the rule
// for what is in it is: ship the file verbatim when its dependency chain
// terminates cheaply, write our own when it does not.
//
// A vendored file's BODY is untouched. Only its goog.require lines become ES
// imports, and only its goog.module header becomes the two lines at the bottom
// of clojure.cljs.goog/convert. Everything those bodies reach for through `goog`
// is here.
//
// Load order is carried by ES static imports, exactly as it was carried by
// goog.require under the debug loader: a file importing this one and then its
// dependencies is guaranteed to run after them.

// The registry a var is a property of, so that a goog namespace can BE a
// namespace object (doc/cljs-compiler.md §5.2) and `gobject/get` can emit
// goog$object$ns.get with no new case in the analyzer.
import { $CLJS } from "../runtime.js";

// NOT globalThis.goog, and that is the whole of our isolation from a Closure
// Library the user's project already has. A page can hold a real Closure - loaded
// by a bundler, or by Closure's own debug loader - and that one owns
// globalThis.goog. Ours lives on $CLJS, which is already global and already
// reload-idempotent, and the two never meet.
//
// Nothing needs it to be global: emitted ClojureScript never names `goog`, it
// names $ns("goog.string").isEmpty, and the only code that touches this object is
// the converted Closure files, every one of which imports it from here. $CLJS is
// on globalThis for a reason that does not apply here - a REPL form is evaluated
// as a script, and a script may not contain an import declaration.
export const goog = ($CLJS.goog ??= {});

// Closure's own defaults. DEBUG false is what makes goog.asserts.ENABLE_ASSERTS
// false, so an assert compiles to a no-op that returns its argument; TRUSTED_SITE
// true is base.js's default and is read once, by goog.string.internal.trim.
goog.DEBUG ??= false;
goog.TRUSTED_SITE ??= true;
goog.global ??= globalThis;

// goog.define is a compiler directive under Closure and a plain function here:
// there is no compilation pass to substitute a value, so a define is its default.
goog.define ??= function(name, defaultValue) { return defaultValue; };

// --- verbatim from Closure's base.js ----------------------------------------
//
// These five are the whole of what the vendored files and cljs.core reach for on
// `goog` itself. Copied rather than paraphrased: goog.typeOf in particular is a
// contract cljs.core dispatches on, and it is NOT the same function as
// runtime.js's typeOf - Closure separates null from undefined, and we do not,
// because (extend-type nil ...) is one case in ClojureScript.

goog.typeOf ??= function(value) {
  var s = typeof value;
  if (s != 'object') { return s; }
  if (!value) { return 'null'; }
  if (Array.isArray(value)) { return 'array'; }
  return s;
};

goog.isArrayLike ??= function(val) {
  var type = goog.typeOf(val);
  // We do not use goog.isObject here in order to exclude function values.
  return type == 'array' || type == 'object' && typeof val.length == 'number';
};

goog.isObject ??= function(val) {
  var type = typeof val;
  return type == 'object' && val != null || type == 'function';
};

goog.UID_PROPERTY_ ??= 'closure_uid_' + ((Math.random() * 1e9) >>> 0);
goog.uidCounter_ ??= 0;

goog.getUid ??= function(obj) {
  return Object.prototype.hasOwnProperty.call(obj, goog.UID_PROPERTY_) &&
      obj[goog.UID_PROPERTY_] ||
      (obj[goog.UID_PROPERTY_] = ++goog.uidCounter_);
};

// base.js:1447. Reached by goog.array.insertArrayAt, which is the rule this file
// opens with: everything a vendored body reaches for through `goog` is here.
goog.partial ??= function(fn, var_args) {
  var args = Array.prototype.slice.call(arguments, 1);
  return function() {
    // Clone the array (with slice()) and append additional arguments
    // to the existing arguments.
    var newArgs = args.slice();
    newArgs.push.apply(newArgs, arguments);
    return fn.apply(/** @type {?} */ (this), newArgs);
  };
};

goog.inherits ??= function(childCtor, parentCtor) {
  /** @constructor */
  function tempCtor() {}
  tempCtor.prototype = parentCtor.prototype;
  childCtor.superClass_ = parentCtor.prototype;
  childCtor.prototype = new tempCtor();
  /** @override */
  childCtor.prototype.constructor = childCtor;
  childCtor.base = function(me, methodName, var_args) {
    var args = new Array(arguments.length - 2);
    for (var i = 2; i < arguments.length; i++) { args[i - 2] = arguments[i]; }
    return parentCtor.prototype[methodName].apply(me, args);
  };
};

// --- ours -------------------------------------------------------------------

// goog.provide, kept as a call so a vendored goog.provide file's first line
// stays verbatim. Under Closure it is a directive the compiler erases and the
// debug loader turns into exactly this; here it is only ever the latter.
//
// Idempotent, and it must be: goog.string.internal and goog.string.StringBuffer
// both provide something under `goog.string`, and whichever runs second has to
// find the object the first one made rather than replace it - along with
// everything already hung on it.
goog.provide ??= function(name) {
  let o = goog;
  for (const part of name.split(".").slice(1)) { o = (o[part] ??= {}); }
  return o;
};

// The goog.module counterpart, and the one line of a converted module file that
// is ours rather than Closure's: goog.module.declareLegacyNamespace() says the
// module's exports ARE goog.<name>, and this is that assignment. Split from
// provide because a module's exports replace the object rather than extend it -
// goog.math.Long IS the Long constructor, not a namespace holding one.
goog.expose ??= function(name, exports) {
  const parts = name.split(".").slice(1);
  let o = goog;
  for (const part of parts.slice(0, -1)) { o = (o[part] ??= {}); }
  o[parts[parts.length - 1]] = exports;
  register(name);
};

// A goog name is reachable as a ClojureScript namespace object, so that
// (:require [goog.object :as gobject]) needs nothing the analyzer does not
// already do for a ClojureScript namespace: gobject/get is a var, and a var is a
// property of the object $ns returns.
//
// Registered rather than created, which is the whole trick - $CLJS.ns would
// otherwise hand out a fresh {} and the goog functions would be on an object
// nobody reads. Every emitted module's static imports run before its prologue
// calls $ns, so this always wins the race.
//
// CALLED AFTER THE BODY, never from goog.provide, and that is not a detail. A
// provide whose name ends up holding a CLASS - goog.string.StringBuffer,
// goog.math.Integer, goog.Uri - has its name REPLACED by the body:
//
//     goog.provide('goog.string.StringBuffer');   // creates an empty object
//     goog.string.StringBuffer = function(...) {} // replaces it
//
// so registering inside provide files the empty object away, and every
// (StringBuffer.) then fails with "not a constructor". The converted file calls
// goog.register on its last line instead - see clojure.cljs.goog/convert.
//
// The value registered for a DOTTED provide is its container, because that is
// what a ClojureScript namespace means: `goog.math.Long` names the var `Long` in
// the namespace `goog.math`, so the object registered under "goog.math" is the
// one holding Long. The full name is registered too, for (:require
// goog.math.Long), which asks for a module by its provide name.
function register(name) {
  const parts = name.split(".");
  let o = goog;
  for (const part of parts.slice(1)) { o = o[part]; if (o == null) return; }
  $CLJS.namespaces.set(name, o);
  if (parts.length > 1) {
    const parent = parts.slice(0, -1).join(".");
    let p = goog;
    for (const part of parts.slice(1, -1)) { p = p[part]; if (p == null) return; }
    if (!$CLJS.namespaces.has(parent)) $CLJS.namespaces.set(parent, p);
  }
}

goog.register ??= register;

// base.js provides `goog` itself. goog.js is what a require of it FETCHES - this
// is only so that importing any goog file at all leaves $ns("goog") meaning
// something.
// Single-quoted, like every other provide in this tree. base.js is never parsed -
// convert copies it verbatim and index skips it - so the quoting cannot matter to
// the rewrite. It is written this way so that it could be: a file whose header
// would be REFUSED by clojure.cljs.goog/parse is a trap for whoever next changes
// which files are parsed, and the cost of not being one is this comment.
goog.provide('goog');
register('goog');
