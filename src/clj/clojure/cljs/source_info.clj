;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Where each node came from: a line and a column on every node's :env.

  A PASS, not part of analysis, and it runs over clojure.cljs.ast - so it knows no
  node types and needs no update when one is added.

  WHY IT IS NEEDED AT ALL, since every node already carries the :form it was built
  from: because after macroexpansion most forms carry no reader metadata. The
  reader puts a position on what it reads, and the macroexpander synthesises the
  rest out of nothing:

    :def    form=(def f (cljs.core/fn ...))     form-meta={}
    :var    form=f                              form-meta={:line 1, :column 7}
    :fn     form=(fn* ([x] ...))                form-meta={}
    :let    form=(let* [y (+ x 1)] (str y))     form-meta={}
    :js     form=(js* \"(~{} + ~{})\" x 1)        form-meta={}
    :local  form=x                              form-meta={:line 2, :column 14}

  Only what the reader read keeps a position. Everything the macroexpander built
  has none, and no amount of looking at one node will recover it - the information
  is in the node's ANCESTRY, which is why this is a walk and not a lookup.

  THE RULE, and it is the whole pass: a node's position is its own form's if that
  form has one, and the nearest enclosing form's otherwise. So (let* ...) is
  wherever the (let ...) that expanded to it was written, and a symbol inside it
  that the reader did read overrides that with its own line.

  WHAT IT CANNOT RECOVER, and the limit is Clojure's rather than this pass's: a
  number, a string, a keyword and a boolean carry no metadata, so a constant's
  position is always its nearest enclosing form's. (+ x 1) on line 2 gives its 1
  the position of the binding it is the init of, not the column the 1 was typed in.
  Good enough to name a line in a stack trace, which is what it is for.

  ALL FOUR KEYS MOVE TOGETHER. A form with a :line but no :end-line does not
  inherit an :end-line from its parent: a start from one form and an end from
  another describes a region nobody wrote. ClojureScript's own pass merges them
  key by key and can mix them; this one takes the group or leaves it.

  WHAT USES IT: nothing yet, and that is worth saying plainly. It is the
  precondition for doc/cljs-repl.md R2's symbolicated stacks - a source map needs a
  source position for every emitted thing - and the half that is still missing is
  provenance through the emitter, which returns strings with no node attached
  (§5.1). Error messages would want the positions DURING analysis instead, which is
  a different and larger change: it means threading them through every analyze call
  rather than walking once at the end.

  Derived from clojure.tools.analyzer.passes.source-info, which is the same rule
  and the same trick for pushing it down. doc/cljs-compiler.md §5.41."}
  clojure.cljs.source-info
  (:require [clojure.cljs.ast :as ast]))

(def ^:private position-keys
  "What the reader records, and what a node carries. Kept as a group - see the
  docstring: these four are taken or left together."
  [:line :column :end-line :end-column])

(defn- own-position
  "The position the reader put on `form`, or nil. :line is the marker for having
  one at all, as it is in tools.analyzer: a form with no line has no position, and
  a column without a line is not one."
  [form]
  (let [m (meta form)]
    (when (:line m) (not-empty (select-keys m position-keys)))))

(defn source-info
  "`node`, with a position on every node's :env.

  `seed` is what the root inherits: a map carrying any of :file :line :column
  :end-line :end-column. Both halves of it are things only the caller knows.

  :file, because nothing here can work it out - the reader as this compiler calls
  it is given a string with no name (clojure.cljs.reader/reader-added), so the only
  thing that knows which file a form came from is whoever opened it. It is written
  onto every node.

  THE POSITION HALF IS NOT OPTIONAL DECORATION. A top-level (defn f ...) reaches
  the analyzer already macroexpanded, so the :def node's own form is
  (def f (cljs.core/fn ...)) and carries no metadata at all - the position the
  reader gave the form the user typed is on the form the CALLER still has and the
  node no longer does. Without a seed the root has no position, and the whole left
  spine of the tree inherits nothing from it.

  The trick, which is tools.analyzer's: on the way DOWN, a node takes its position
  and then writes that position into each of its children before the walk descends
  into them. A child that has a position of its own overwrites it when its own turn
  comes; a child that has none - every form macroexpansion invented - keeps it."
  ([node] (source-info node nil))
  ([node seed]
   (let [of-file  (not-empty (select-keys seed [:file]))
         root-pos (not-empty (select-keys seed position-keys))
         node     (cond-> node
                    root-pos (update :env #(merge root-pos %)))]
     (ast/prewalk
      node
      (fn [n]
        (let [pos (merge of-file
                         (or (own-position (:form n))
                             (not-empty (select-keys (:env n) position-keys))))
              push (fn [child] (update child :env merge pos))]
          (if (seq pos)
            (ast/update-children (push n) push)
            n)))))))
