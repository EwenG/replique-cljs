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

// --- what the whole Closure Library reaches for ------------------------------
//
// Everything above is what the SUBSET's files and cljs.core need. A project that
// compiles against a real Closure Library (clojure.cljs.goog/*closure-library*)
// converts files nobody here chose, and their bodies call base.js functions the
// subset never did. Measured over the library's 1,604 non-test files, these are
// all of them, with how many files call each:
//
//     goog.setTestOnly 744   getCssName 570   bind 457   getMsg 378   now 82
//     exportSymbol 70   addSingletonGetter 45   getObjectByName 38   scope 18
//     defineClass 12    exportProperty 10   cloneObject 8   setCssNameMapping 7
//     createTrustedTypesPolicy 6   removeUid/hasUid 6   isDateLike 19
//
// Copied from Closure's base.js rather than paraphrased, for the reason goog.typeOf
// above is: these are contracts library code depends on. Where the original reaches
// a private helper of base.js - exportPath_, cssNameMapping_, identity_,
// instantiatedSingletons_ - the helper is inlined, because those exist to serve the
// debug loader and the compiler, neither of which is here. Each one that is not a
// straight copy says so.
//
// goog.defineClass is NOT here. It is a compiler directive with a runtime fallback
// of some size, and no file in the library calls it outside its own tests; the day
// one does, the error names it, which is better than a paraphrase nobody checked.

// A no-op: goog.DISALLOW_TEST_ONLY_CODE is a define the compiler sets, and there is
// no compilation pass here to set it.
goog.setTestOnly ??= function(opt_message) {};

// goog.module.get(name), which a file inside a goog.scope uses to reach a module it
// required - nine of the library files do it. An OBJECT rather than a function,
// because the goog.module(...) header line it would otherwise shadow is blanked by
// the rewrite and never called: see clojure.cljs.goog/convert.
//
// What it returns is what goog.expose assigned, which is what the requirer would
// have bound with const - so this and a bound require are two spellings of one
// thing, as they are under Closure.
goog.module ??= {};
goog.module.get ??= function(name) {
  let o = goog;
  for (const part of name.split(".").slice(1)) { o = o[part]; if (o == null) return null; }
  return o;
};

goog.now ??= function() { return Date.now(); };

// The native path of Closure's goog.bind, which is the one it installs on every
// engine of this century.
goog.bind ??= function(fn, selfObj, var_args) {
  return fn.call.apply(fn.bind, arguments);
};

goog.getObjectByName ??= function(name, opt_obj) {
  var parts = name.split('.');
  var cur = opt_obj || goog.global;
  for (var i = 0; i < parts.length; i++) {
    cur = cur[parts[i]];
    if (cur == null) { return null; }
  }
  return cur;
};

goog.exportProperty ??= function(object, publicName, symbol) {
  object[publicName] = symbol;
};

// exportPath_ inlined: walk the path, making the objects that are missing, and
// assign at the end. The original's overwriteImplicit bookkeeping exists for the
// compiler's benefit and decides nothing here.
goog.exportSymbol ??= function(publicPath, object, objectToExportTo) {
  var parts = publicPath.split('.');
  var cur = objectToExportTo || goog.global;
  for (var i = 0; i < parts.length - 1; i++) {
    cur = cur[parts[i]] ??= {};
  }
  cur[parts[parts.length - 1]] = object;
};

// goog.scope's only job outside the compiler is to call its function. The original
// also refuses to run inside a module loader, which is a state this has none of.
goog.scope ??= function(fn) { fn.call(goog.global); };

// instantiatedSingletons_ dropped: it is a DEBUG-only list, kept so that a test
// harness can reset every singleton, and nothing here resets one.
goog.addSingletonGetter ??= function(ctor) {
  ctor.instance_ = undefined;
  ctor.getInstance = function() {
    if (ctor.instance_) { return ctor.instance_; }
    return ctor.instance_ = new ctor;
  };
};

goog.isDateLike ??= function(val) {
  return goog.isObject(val) && typeof val.getFullYear == 'function';
};

goog.hasUid ??= function(obj) { return !!obj[goog.UID_PROPERTY_]; };

goog.removeUid ??= function(obj) {
  if (obj !== null && 'removeAttribute' in obj) {
    obj.removeAttribute(goog.UID_PROPERTY_);
  }
  try { delete obj[goog.UID_PROPERTY_]; } catch (ex) {}
};

goog.cloneObject ??= function(obj) {
  var type = goog.typeOf(obj);
  if (type == 'object' || type == 'array') {
    if (typeof obj.clone === 'function') { return obj.clone(); }
    if (typeof Map !== 'undefined' && obj instanceof Map) { return new Map(obj); }
    if (typeof Set !== 'undefined' && obj instanceof Set) { return new Set(obj); }
    var clone = type == 'array' ? [] : {};
    for (var key in obj) { clone[key] = goog.cloneObject(obj[key]); }
    return clone;
  }
  return obj;
};

goog.getMsg ??= function(str, opt_values, opt_options) {
  if (opt_options && opt_options.html) {
    str = str.replace(/</g, '&lt;');
  }
  if (opt_options && opt_options.unescapeHtmlEntities) {
    str = str.replace(/&lt;/g, '<')
             .replace(/&gt;/g, '>')
             .replace(/&apos;/g, "'")
             .replace(/&quot;/g, '"')
             .replace(/&amp;/g, '&');
  }
  if (opt_values) {
    str = str.replace(/\{\$([^}]+)}/g, function(match, key) {
      return (opt_values != null && key in opt_values) ? opt_values[key] : match;
    });
  }
  return str;
};

// The CSS renaming map, which only a build sets. Unset, getCssName is identity -
// which is what an uncompiled Closure does too.
goog.cssNameMapping_ ??= null;

goog.setCssNameMapping ??= function(mapping, opt_style) {
  goog.cssNameMapping_ = mapping;
  goog.cssNameMappingStyle_ = opt_style;
};

goog.getCssName ??= function(className, opt_modifier) {
  if (String(className).charAt(0) == '.') {
    throw new Error('className passed in goog.getCssName must not start with ".".' +
                    ' You passed: ' + className);
  }
  var getMapping = function(cssName) {
    return goog.cssNameMapping_ ? (goog.cssNameMapping_[cssName] || cssName) : cssName;
  };
  var rename = function(cssName) {
    if (goog.cssNameMappingStyle_ == 'BY_WHOLE') { return getMapping(cssName); }
    return cssName.split('-').map(getMapping).join('-');
  };
  return opt_modifier ? className + '-' + rename(opt_modifier) : rename(className);
};

// identity_ inlined. Returns null where the browser has no Trusted Types, which is
// the branch every caller already handles.
goog.createTrustedTypesPolicy ??= function(name) {
  var factory = goog.global.trustedTypes;
  if (!factory || !factory.createPolicy) { return null; }
  var identity = function(s) { return s; };
  try {
    return factory.createPolicy(name, {
      createHTML: identity, createScript: identity, createScriptURL: identity
    });
  } catch (e) {
    if (goog.DEBUG) { console.error(e.message); }
    return null;
  }
};
