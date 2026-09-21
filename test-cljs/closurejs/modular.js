// The other shape: a goog.module, which declares a legacy namespace exactly as
// shadow/loader.js does. Its exports become the namespace object, so a var in it
// is a property of what $ns("closurejs.modular") hands back.
goog.module("closurejs.modular");
goog.module.declareLegacyNamespace();

const util = goog.require("closurejs.util");

exports.quadruple = function(x) { return util.twice(util.twice(x)); };
