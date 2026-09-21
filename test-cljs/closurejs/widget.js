// A provide that requires another provide beside it AND a goog namespace out of
// the subset, which is the shape transit.js has: the two trees meet in one
// import line, and the relative specifier between them is computed across the
// output root.
goog.provide("closurejs.widget");
goog.require("closurejs.util");
goog.require("goog.object");

goog.scope(function() {
  var widget = closurejs.widget;

  // `closurejs` is a free variable here, as it is under Closure's own loader.
  // What binds it is the one line clojure.cljs.goog/convert adds at the top.
  widget.describe = function(o) {
    return goog.object.getKeys(o).join(",") + ":" + closurejs.util.twice(21);
  };
});
