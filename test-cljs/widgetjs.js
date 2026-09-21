// A one-segment Closure name on the classpath. It is here so that the three
// answers a bare symbol can have - a source, a Closure file, a package - can be
// asked of one another in the order they are asked in: see
// clojure.cljs.analyzer/js-module-ns?, which reaches the package last.
goog.provide("widgetjs");

widgetjs.origin = "closure";
