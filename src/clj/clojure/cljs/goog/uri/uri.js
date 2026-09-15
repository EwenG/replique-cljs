/**
 * @fileoverview goog.Uri - DEFERRED, and this is the placeholder that says so.
 *
 * The real goog/Uri/uri.js is 1,600 lines whose transitive closure is 38 files
 * and 16,402 lines - the largest single item in the Closure Library subset, and
 * larger than the rest of this tree put together. It reaches goog.structs,
 * goog.collections.maps, goog.uri.utils and the whole of goog.string, which is
 * to say the safe-HTML type system, TrustedTypes and user-agent sniffing.
 *
 * cljs.core buys all of that for one expression (core.cljs:12224):
 *
 *     (defn uri? [x] (instance? goog.Uri x))
 *
 * So goog.Uri is a constructor here and nothing else. That keeps cljs.core
 * compiling unmodified - §4.4's property, and the one that keeps M5 bounded -
 * and it keeps `uri?` HONEST rather than merely quiet: nothing in this world can
 * construct a goog.Uri, so `false` is the right answer for every value, and it is
 * the answer `uri?` gives.
 *
 * What is not honest is silently doing nothing when someone wants a URI, so
 * constructing one throws and says why. A caller who needs URI parsing has
 * globalThis.URL, which node and every browser have and neither had when goog.Uri
 * was written.
 *
 * To undo this: vendor the 38 files the way the rest of this tree is vendored and
 * delete this file. Nothing else changes - the decision is recorded in
 * doc/cljs-compiler.md §7 and lives here, in one file.
 *
 * A SEPARATE question, open in §7 and deliberately not settled here: whether uri?
 * should be pluggable rather than closed on one class. It could be, without
 * touching core.cljs - core.cljc expands (instance? c x) to (x instanceof c), so a
 * static [Symbol.hasInstance] on this class would make `uri?` consult a registry of
 * predicates that anyone could add their own URI type to. That is an improvement on
 * ClojureScript rather than a repair of this deferral - stock cljs answers false for
 * globalThis.URL too - so it is priced at M6 against the test suite, not now.
 */
goog.provide('goog.Uri');

goog.Uri = function(opt_uri, opt_ignoreCase) {
  throw new Error(
      "goog.Uri is not implemented. Its 38-file dependency chain was deferred " +
      "at M5 because cljs.core uses it for one instance? test - see " +
      "clojure/cljs/goog/uri/uri.js. Use globalThis.URL, or vendor the real " +
      "goog.Uri. (uri? is unaffected: it answers false, which is correct while " +
      "nothing can construct one.)");
};

goog.Uri.QueryData = goog.Uri;
