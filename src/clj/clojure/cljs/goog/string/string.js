/**
 * @fileoverview goog.string, reduced to what cljs.core uses.
 *
 * NOT vendored - written for this tree, and the reason is a measurement. The
 * real goog/string/string.js is 1,492 lines whose transitive closure is 34 files
 * and 13,099 lines: it carries HTML escaping, which reaches goog.dom.safe,
 * goog.html.SafeHtml and the rest of the safe-HTML type system, TrustedTypes and
 * user-agent sniffing. cljs.core uses three functions.
 *
 * Those three are not reimplemented here. In the real file they are assignments:
 *
 *     goog.string.endsWith = goog.string.internal.endsWith;      (string.js:64)
 *     goog.string.contains = goog.string.internal.contains;      (string.js:962)
 *     goog.string.isEmpty  = goog.string.isEmptyOrWhitespace;    (string.js:165)
 *     goog.string.isEmptyOrWhitespace = goog.string.internal.isEmptyOrWhitespace;
 *
 * and goog/string/internal.js is 395 lines with NO dependencies at all, so it is
 * vendored whole beside this file. What follows is those lines. The behaviour is
 * Closure's; only the lines that were not being called are missing.
 *
 * Adding a function means checking it against internal.js first: anything that is
 * not there is likely to be there because it needs the safe-HTML types. Eight of
 * the fourteen below are not, and those eight are copied verbatim from string.js -
 * each is self-contained, and the line it came from is on it.
 *
 * clojure.string (M6) is what took this from four functions to eleven, and four
 * callers in ClojureScript's own test suite took it to fifteen:
 *
 *     isNumeric      cljs/tools/reader/impl/utils.cljs, and so cljs.reader
 *     isUnicodeChar  cljs/pprint.cljs:1966 and :2039
 *     urlEncode      cljs/invoke_test.cljs:38, which calls it directly
 *     urlDecode      cljs/invoke_test.cljs:40, the same, spelled js/goog.string.
 *
 * None of the eight widened the closure: every one of them is a line of arithmetic
 * on a string, and not one reaches anything at all.
 */
goog.provide('goog.string');
goog.require('goog.string.internal');

goog.string.startsWith = goog.string.internal.startsWith;
goog.string.endsWith = goog.string.internal.endsWith;
goog.string.contains = goog.string.internal.contains;
goog.string.trim = goog.string.internal.trim;
goog.string.isEmptyOrWhitespace = goog.string.internal.isEmptyOrWhitespace;

/** @deprecated Closure marks this deprecated; cljs.core calls it. */
goog.string.isEmpty = goog.string.isEmptyOrWhitespace;

/* The five that internal.js does not have, verbatim from goog/string/string.js. */

/** string.js:336 */
goog.string.trimLeft = function(str) {
  'use strict';
  // Since IE doesn't include non-breaking-space (0xa0) in their \s character
  // class (as required by section 7.2 of the ECMAScript spec), we explicitly
  // include it in the regexp to enforce consistent cross-browser behavior.
  return str.replace(/^[\s\xa0]+/, '');
};

/** string.js:350 */
goog.string.trimRight = function(str) {
  'use strict';
  // Since IE doesn't include non-breaking-space (0xa0) in their \s character
  // class (as required by section 7.2 of the ECMAScript spec), we explicitly
  // include it in the regexp to enforce consistent cross-browser behavior.
  return str.replace(/[\s\xa0]+$/, '');
};

/** string.js:1056 */
goog.string.regExpEscape = function(s) {
  'use strict';
  return String(s)
      .replace(/([-()\[\]{}+?*.$\^|,:#<!\\])/g, '\\$1')
      .replace(/\x08/g, '\\x08');
};

/** string.js:1118 */
goog.string.makeSafe = function(obj) {
  'use strict';
  return obj == null ? '' : String(obj);
};

/** string.js:1336 */
goog.string.capitalize = function(str) {
  'use strict';
  return String(str.charAt(0)).toUpperCase() +
      String(str.slice(1)).toLowerCase();
};

/** string.js:221 */
goog.string.isNumeric = function(str) {
  'use strict';
  return !/[^0-9]/.test(str);
};

/** string.js:254 */
goog.string.isUnicodeChar = function(ch) {
  'use strict';
  return ch.length == 1 && ch >= ' ' && ch <= '~' ||
      ch >= '\u0080' && ch <= '\uFFFD';
};

/** string.js:493 */
goog.string.urlEncode = function(str) {
  'use strict';
  return encodeURIComponent(String(str));
};

/** string.js:505 */
goog.string.urlDecode = function(str) {
  'use strict';
  return decodeURIComponent(str.replace(/\+/g, ' '));
};
