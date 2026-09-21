// A Closure file that is not the Closure Library and not in any list this
// compiler keeps: it is found because it sits at the path its own name spells,
// which is what clojure.cljs.goog/js-path says and what transit-js and
// shadow-cljs both lay their jars out by.
//
// DOUBLE QUOTES, deliberately. transit-js writes every header line this way and
// the Closure Library writes none of them that way, so one of the two shapes had
// to be tested by a file we control - see clojure.cljs.goog/q.
goog.provide("closurejs.util");

goog.scope(function() {
  var util = closurejs.util;

  util.twice = function(x) { return x * 2; };
});
