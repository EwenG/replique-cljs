/**
 * @fileoverview `goog` itself, as something that can be REQUIRED.
 *
 * base.js already provides it - the goog object is what base.js is - but base.js
 * is the file everything IMPORTS, and so is excluded from the provide index:
 * nothing can require it. That leaves one name with no file behind it, and it is
 * a name cljs.core uses nineteen times without ever requiring it:
 *
 *     (identical? "string" (goog/typeOf x))        core.cljs:309
 *     (goog/getUid o)                              core.cljs:1496
 *
 * `goog` is implicitly available in ClojureScript. It is implicitly available
 * here too - see clojure.cljs.analyzer - but a namespace that names goog/typeOf
 * and requires nothing else from the subset would otherwise pull in no goog file
 * at all, and $ns("goog") would hand back an empty object. This is the file that
 * require fetches so that cannot happen. It is one import.
 *
 * The provide also puts `goog` in the index, so clojure.cljs.goog/known? needs no
 * special case for the one name that would otherwise not be in it.
 */
goog.provide('goog');
