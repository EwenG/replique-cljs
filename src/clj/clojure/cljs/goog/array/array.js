/**
 * @fileoverview goog.array, reduced to what cljs.core uses.
 *
 * NOT vendored whole - the real goog/array/array.js is 1,782 lines and pulls in
 * goog.asserts (and so goog.debug.Error and goog.dom.NodeType) for the argument
 * checks in functions nothing here calls. cljs.core uses four: defaultCompare,
 * clone, stableSort and shuffle.
 *
 * The bodies below are COPIED VERBATIM from that file. sort and toArray come
 * along because stableSort and clone are written in terms of them (clone is
 * literally `const clone = toArray`, array.js:860), and slice and splice because
 * insertArrayAt is.
 *
 * cljs/tools/reader.cljs is what took this from six functions to eleven (M6) -
 * and so cljs.reader, cljs.pprint and cljs.tagged-literals, which reach it. It
 * calls three: insertArrayAt, isEmpty and removeAt. slice and splice come along
 * behind insertArrayAt.
 *
 * IT IS ALSO THE FIRST THING HERE TO TOUCH `asserts`, which the note this
 * replaced said was what made taking the others out of the file honest. It costs
 * nothing now: goog.asserts is vendored WHOLE, with goog.debug.Error and
 * goog.dom.NodeType behind it, so the chain the note was about is already paid
 * for - and goog.DEBUG is false, which makes ENABLE_ASSERTS false and an assert
 * a no-op that returns its argument.
 *
 * The real file is a goog.module, so a body says `slice` where this says
 * goog.array.slice and `asserts.assert` where this says goog.asserts.assert.
 * That is the same rebinding declareLegacyNamespace does, and the same one
 * goog/string/string.js gets here.
 *
 * Line numbers are into goog/array/array.js at 0.0-20250515-f04e4c0e.
 */
goog.provide('goog.array');
goog.require('goog.asserts');

/** array.js:1333 */
goog.array.defaultCompare = function(a, b) {
  return a > b ? 1 : a < b ? -1 : 0;
};

/** array.js:1147 */
goog.array.sort = function(arr, opt_compareFn) {
  arr.sort(opt_compareFn || goog.array.defaultCompare);
};

/** array.js:835 */
goog.array.toArray = function(object) {
  const length = object.length;

  // If length is not a number the following is false. This case is kept for
  // backwards compatibility since there are callers that pass objects that are
  // not array like.
  if (length > 0) {
    const rv = new Array(length);
    for (let i = 0; i < length; i++) {
      rv[i] = object[i];
    }
    return rv;
  }
  return [];
};

/** array.js:860 */
goog.array.clone = goog.array.toArray;

/** array.js:1172 */
goog.array.stableSort = function(arr, opt_compareFn) {
  const compArr = new Array(arr.length);
  for (let i = 0; i < arr.length; i++) {
    compArr[i] = {index: i, value: arr[i]};
  }
  const valueCompareFn = opt_compareFn || goog.array.defaultCompare;
  function stableCompareFn(obj1, obj2) {
    return valueCompareFn(obj1.value, obj2.value) || obj1.index - obj2.index;
  }
  goog.array.sort(compArr, stableCompareFn);
  for (let i = 0; i < arr.length; i++) {
    arr[i] = compArr[i].value;
  }
};

/** array.js:1729 */
goog.array.shuffle = function(arr, opt_randFn) {
  const randFn = opt_randFn || Math.random;

  for (let i = arr.length - 1; i > 0; i--) {
    // Choose a random array index in [0, i] (inclusive with i).
    const j = Math.floor(randFn() * (i + 1));

    const tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
  }
};

/** array.js:935 */
goog.array.slice = function(arr, start, opt_end) {
  goog.asserts.assert(arr.length != null);

  // passing 1 arg to slice is not the same as passing 2 where the second is
  // null or undefined (in that case the second argument is treated as 0).
  // we could use slice on the arguments object and then use apply instead of
  // testing the length
  if (arguments.length <= 2) {
    return Array.prototype.slice.call(arr, start);
  } else {
    return Array.prototype.slice.call(arr, start, opt_end);
  }
};

/** array.js:914 */
goog.array.splice = function(arr, index, howMany, var_args) {
  goog.asserts.assert(arr.length != null);

  return Array.prototype.splice.apply(arr, goog.array.slice(arguments, 1));
};

/** array.js:662 */
goog.array.insertArrayAt = function(arr, elementsToAdd, opt_i) {
  goog.partial(goog.array.splice, arr, opt_i, 0).apply(null, elementsToAdd);
};

/** array.js:605 */
goog.array.isEmpty = function(arr) {
  return arr.length == 0;
};

/** array.js:731 */
goog.array.removeAt = function(arr, i) {
  goog.asserts.assert(arr.length != null);

  // use generic form of splice
  // splice returns the removed items and if successful the length of that
  // will be 1
  return Array.prototype.splice.call(arr, i, 1).length == 1;
};
