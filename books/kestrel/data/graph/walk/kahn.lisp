; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../successors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

(local (include-book "../graph"))
(local (include-book "../nodes"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl emptyp-of-delete-by-cardinality
  (equal (treeset::emptyp (treeset::delete x set))
         (if (treeset::in x set)
             (equal (treeset::cardinality set) 1)
           (treeset::emptyp set)))
  :use (:instance treeset::equal-of-cardinality-and-0-becomes-emptyp
                  (set (treeset::delete x set)))
  :enable treeset::delete-when-not-in
  :disable treeset::emptyp-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Kahn's algorithm removes, one at a time, a node with no edge into it from
;; the nodes not yet removed. This version takes the least such node. The nodes
;; left when there is none are those reachable from a cycle.

(define kahn-remaining ((remaining treeset::setp) (graph graphp))
  :type-prescription :none
  :returns (remaining$ treeset::setp)
  :parents (cyclicp)
  :short "The nodes Kahn's algorithm cannot remove, which are those reachable
          from a cycle."
  (b* ((sources (treeset::diff remaining
                               (successors-of-set remaining graph)))
       ((when (treeset::emptyp sources))
        (treeset::fix remaining)))
    (kahn-remaining (treeset::delete (treeset::min sources) remaining)
                    graph))
  :measure (treeset::cardinality remaining)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-remaining-when-equiv-of-arg1-congruence
  (implies (treeset::equiv remaining0 remaining1)
           (equal (kahn-remaining remaining0 graph)
                  (kahn-remaining remaining1 graph)))
  :rule-classes :congruence
  :expand ((kahn-remaining remaining0 graph)
           (kahn-remaining remaining1 graph)))

(defrule kahn-remaining-when-equiv-of-arg2-congruence
  (implies (equiv graph0 graph1)
           (equal (kahn-remaining remaining graph0)
                  (kahn-remaining remaining graph1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-remaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The nodes removed, in the order of removal.

(define kahn-order ((remaining treeset::setp) (graph graphp))
  :returns (order true-listp)
  :parents (topological-sort)
  :short "The nodes Kahn's algorithm removes, in the order of removal."
  (b* ((sources (treeset::diff remaining
                               (successors-of-set remaining graph)))
       ((when (treeset::emptyp sources))
        nil)
       (node (treeset::min sources)))
    (cons node
          (kahn-order (treeset::delete node remaining) graph)))
  :measure (treeset::cardinality remaining)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-order-when-equiv-of-arg1-congruence
  (implies (treeset::equiv remaining0 remaining1)
           (equal (kahn-order remaining0 graph)
                  (kahn-order remaining1 graph)))
  :rule-classes :congruence
  :expand ((kahn-order remaining0 graph)
           (kahn-order remaining1 graph)))

(defrule kahn-order-when-equiv-of-arg2-congruence
  (implies (equiv graph0 graph1)
           (equal (kahn-order remaining graph0)
                  (kahn-order remaining graph1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The efficient version keeps counters: for each node not yet removed with an
;; edge into it from the nodes not yet removed, the number of such nodes. It
;; also keeps the frontier: the nodes not yet removed without a counter.
;; Removing a node decrements the counters of its successors, and a counter
;; which reaches zero is deleted and its node added to the frontier.

(define kahn-increment ((targets treeset::setp) (counters treemap::mapp))
  :type-prescription :none
  :returns (counters$ treemap::mapp)
  :parents (cyclicp)
  :short "Increment the counter of each node in a set."
  (b* (((when (treeset::emptyp targets))
        (treemap::fix counters))
       (node (treeset::min targets))
       (count (nfix (treemap::lookup node counters :default 0))))
    (kahn-increment (treeset::delete node targets)
                    (treemap::update node (+ 1 count) counters)))
  :measure (treeset::cardinality targets))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-increment-when-equiv-of-arg1-congruence
  (implies (treeset::equiv targets0 targets1)
           (equal (kahn-increment targets0 counters)
                  (kahn-increment targets1 counters)))
  :rule-classes :congruence
  :expand ((kahn-increment targets0 counters)
           (kahn-increment targets1 counters)))

(defrule kahn-increment-when-equiv-of-arg2-congruence
  (implies (treemap::equiv counters0 counters1)
           (equal (kahn-increment targets counters0)
                  (kahn-increment targets counters1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-increment)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kahn-counters
  ((set treeset::setp)
   (counters treemap::mapp)
   (graph graphp))
  :type-prescription :none
  :returns (counters$ treemap::mapp)
  :parents (cyclicp)
  :short "Count, for each node, the nodes of a set with an edge to it."
  (b* (((when (treeset::emptyp set))
        (treemap::fix counters))
       (node (treeset::min set)))
    (kahn-counters (treeset::delete node set)
                   (kahn-increment (successors node graph) counters)
                   graph))
  :measure (treeset::cardinality set))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-counters-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
           (equal (kahn-counters set0 counters graph)
                  (kahn-counters set1 counters graph)))
  :rule-classes :congruence
  :expand ((kahn-counters set0 counters graph)
           (kahn-counters set1 counters graph)))

(defrule kahn-counters-when-equiv-of-arg2-congruence
  (implies (treemap::equiv counters0 counters1)
           (equal (kahn-counters set counters0 graph)
                  (kahn-counters set counters1 graph)))
  :rule-classes :congruence
  :induct t
  :enable kahn-counters)

(defrule kahn-counters-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (kahn-counters set counters graph0)
                  (kahn-counters set counters graph1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-counters)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kahn-decrement
  ((targets treeset::setp)
   (frontier treeset::setp)
   (counters treemap::mapp))
  :returns (mv (frontier$ treeset::setp)
               (counters$ treemap::mapp))
  :parents (cyclicp)
  :short "Decrement the counter of each node in a set, moving each node whose
          counter reaches zero to the frontier."
  (b* (((when (treeset::emptyp targets))
        (mv (treeset::fix frontier)
            (treemap::fix counters)))
       (node (treeset::min targets))
       (count (nfix (treemap::lookup node counters :default 0)))
       ((when (eql count 1))
        (kahn-decrement (treeset::delete node targets)
                        (treeset::insert node frontier)
                        (treemap::delete node counters))))
    (kahn-decrement (treeset::delete node targets)
                    frontier
                    (treemap::update node (- count 1) counters)))
  :measure (treeset::cardinality targets))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-decrement-when-equiv-of-arg1-congruence
  (implies (treeset::equiv targets0 targets1)
           (equal (kahn-decrement targets0 frontier counters)
                  (kahn-decrement targets1 frontier counters)))
  :rule-classes :congruence
  :expand ((kahn-decrement targets0 frontier counters)
           (kahn-decrement targets1 frontier counters)))

(defrule kahn-decrement-when-equiv-of-arg2-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (kahn-decrement targets frontier0 counters)
                  (kahn-decrement targets frontier1 counters)))
  :rule-classes :congruence
  :induct t
  :enable kahn-decrement)

(defrule kahn-decrement-when-equiv-of-arg3-congruence
  (implies (treemap::equiv counters0 counters1)
           (equal (kahn-decrement targets frontier counters0)
                  (kahn-decrement targets frontier counters1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-decrement)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The order of removal is accumulated, most recent first.
;;
;; The frontier is always among the remaining nodes. The check that its least
;; node is one of them only makes termination evident.

(define kahn-loop
  ((remaining treeset::setp)
   (frontier treeset::setp)
   (counters treemap::mapp)
   (order true-listp)
   (graph graphp))
  :returns (mv (order$ true-listp
                       :hyp (true-listp order))
               (remaining$ treeset::setp))
  :parents (cyclicp)
  :short "Kahn's algorithm with counters and a frontier, accumulating the order
          of removal."
  (b* (((when (treeset::emptyp frontier))
        (mv order (treeset::fix remaining)))
       (node (treeset::min frontier))
       ((unless (treeset::in node remaining))
        (mv order (treeset::fix remaining)))
       ((mv frontier counters)
        (kahn-decrement (successors node graph)
                        (treeset::delete node frontier)
                        counters)))
    (kahn-loop (treeset::delete node remaining)
               frontier
               counters
               (cons node order)
               graph))
  :measure (treeset::cardinality remaining))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-loop-when-equiv-of-arg1-congruence
  (implies (treeset::equiv remaining0 remaining1)
           (equal (kahn-loop remaining0 frontier counters order graph)
                  (kahn-loop remaining1 frontier counters order graph)))
  :rule-classes :congruence
  :expand ((kahn-loop remaining0 frontier counters order graph)
           (kahn-loop remaining1 frontier counters order graph)))

(defrule kahn-loop-when-equiv-of-arg2-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (kahn-loop remaining frontier0 counters order graph)
                  (kahn-loop remaining frontier1 counters order graph)))
  :rule-classes :congruence
  :expand ((kahn-loop remaining frontier0 counters order graph)
           (kahn-loop remaining frontier1 counters order graph)))

(defrule kahn-loop-when-equiv-of-arg3-congruence
  (implies (treemap::equiv counters0 counters1)
           (equal (kahn-loop remaining frontier counters0 order graph)
                  (kahn-loop remaining frontier counters1 order graph)))
  :rule-classes :congruence
  :induct t
  :enable kahn-loop)

(defrule kahn-loop-when-equiv-of-arg5-congruence
  (implies (equiv graph0 graph1)
           (equal (kahn-loop remaining frontier counters order graph0)
                  (kahn-loop remaining frontier counters order graph1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-loop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The predecessors of a node among the nodes of a set are its predecessors
;; intersected with the set, and a node with an edge to it is one of them.

(defrulel cardinality-of-intersect-and-predecessors-when-in-of-successors-linear
  (implies (and (treeset::in node (successors pred graph))
                (treeset::in pred set))
           (< 0 (treeset::cardinality
                  (treeset::intersect set (predecessors node graph)))))
  :rule-classes :linear
  :enable treeset::cardinality-when-not-emptyp-linear)

;; A set including its own successors includes the successors of its nodes.

(defrulel in-when-in-of-successors-and-subset-of-successors-of-set
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (treeset::in pred set)
                (treeset::in node (successors pred graph)))
           (treeset::in node set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The efficient version leaves the same nodes. Its invariant: the remaining
;; nodes include their own successors, the counters are those computed afresh
;; for the remaining nodes, and the frontier is the remaining nodes that are
;; not successors of remaining nodes.

(defrulel lookup-of-kahn-increment
  (equal (treemap::lookup node
                          (kahn-increment targets counters)
                          :default default)
         (if (treeset::in node targets)
             (+ 1 (nfix (treemap::lookup node counters :default 0)))
           (treemap::lookup node counters :default default)))
  :induct t
  :enable kahn-increment)

(defrulel in-of-keys-of-kahn-increment
  (equal (treeset::in node (treemap::keys (kahn-increment targets counters)))
         (or (treeset::in node targets)
             (treeset::in node (treemap::keys counters))))
  :induct t
  :enable kahn-increment)

(defrulel lookup-of-kahn-counters
  (equal (treemap::lookup node
                          (kahn-counters set counters graph)
                          :default default)
         (if (treeset::emptyp
               (treeset::intersect set (predecessors node graph)))
             (treemap::lookup node counters :default default)
           (+ (nfix (treemap::lookup node counters :default 0))
              (treeset::cardinality
                (treeset::intersect set (predecessors node graph))))))
  :induct t
  :enable (kahn-counters
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable treeset::emptyp-of-delete)

(defrulel in-of-keys-of-kahn-counters
  (equal (treeset::in node
                      (treemap::keys (kahn-counters set counters graph)))
         (or (treeset::in node (successors-of-set set graph))
             (treeset::in node (treemap::keys counters))))
  :induct t
  :enable (kahn-counters
           successors-of-set))

(defrulel in-of-mv-nth-0-of-kahn-decrement
  (equal (treeset::in node
                      (mv-nth 0 (kahn-decrement targets frontier counters)))
         (or (treeset::in node frontier)
             (and (treeset::in node targets)
                  (equal (nfix (treemap::lookup node counters :default 0))
                         1))))
  :induct t
  :enable kahn-decrement)

(defrulel lookup-of-mv-nth-1-of-kahn-decrement
  (equal (treemap::lookup node
                          (mv-nth 1 (kahn-decrement targets frontier counters))
                          :default default)
         (if (treeset::in node targets)
             (if (equal (nfix (treemap::lookup node counters :default 0)) 1)
                 default
               (- (nfix (treemap::lookup node counters :default 0)) 1))
           (treemap::lookup node counters :default default)))
  :induct t
  :enable kahn-decrement)

;; The initial state

(defrulel keys-of-kahn-counters-of-empty
  (equal (treemap::keys (kahn-counters set (treemap::empty) graph))
         (successors-of-set set graph))
  :enable treeset::extensionality-polar)

;; A step

(defrulel mv-nth-1-of-kahn-decrement-of-successors
  (implies (treeset::in node remaining)
           (equal (mv-nth 1 (kahn-decrement
                              (successors node graph)
                              frontier
                              (kahn-counters remaining (treemap::empty) graph)))
                  (kahn-counters (treeset::delete node remaining)
                                 (treemap::empty)
                                 graph)))
  :enable (treemap::extensionality
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable treeset::emptyp-of-delete)

(defrulel mv-nth-0-of-kahn-decrement-of-successors
  (implies (and (treeset::subset (successors-of-set remaining graph)
                                 remaining)
                (treeset::in node remaining)
                (not (treeset::in node (successors-of-set remaining graph))))
           (equal (mv-nth 0 (kahn-decrement
                              (successors node graph)
                              (treeset::delete
                                node
                                (treeset::diff
                                  remaining
                                  (successors-of-set remaining graph)))
                              (kahn-counters remaining
                                             (treemap::empty)
                                             graph)))
                  (treeset::diff (treeset::delete node remaining)
                                 (successors-of-set
                                   (treeset::delete node remaining)
                                   graph))))
  :enable (treeset::extensionality-polar
           in-of-successors-of-set-becomes-not-emptyp-of-intersect
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable treeset::emptyp-of-delete)

;; So the loop leaves what the logical version leaves, and removes the nodes in
;; the same order, accumulating them most recent first.

(defrulel mv-nth-1-of-kahn-loop
  (implies (and (treeset::subset (successors-of-set remaining graph)
                                 remaining)
                (equal counters
                       (kahn-counters remaining (treemap::empty) graph))
                (equal frontier
                       (treeset::diff remaining
                                      (successors-of-set remaining graph))))
           (equal (mv-nth 1 (kahn-loop remaining frontier counters order graph))
                  (kahn-remaining remaining graph)))
  :induct (kahn-loop remaining frontier counters order graph)
  :enable (kahn-loop
           kahn-remaining))

(defrulel mv-nth-0-of-kahn-loop
  (implies (and (treeset::subset (successors-of-set remaining graph)
                                 remaining)
                (equal counters
                       (kahn-counters remaining (treemap::empty) graph))
                (equal frontier
                       (treeset::diff remaining
                                      (successors-of-set remaining graph))))
           (equal (mv-nth 0 (kahn-loop remaining frontier counters order graph))
                  (revappend (kahn-order remaining graph) order)))
  :induct (kahn-loop remaining frontier counters order graph)
  :enable (kahn-loop
           kahn-order
           revappend))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run the efficient version on a whole graph, from the counters and frontier
;; computed afresh for its nodes. This is what cyclicp and topological-sort
;; execute.

(define kahn ((graph graphp))
  :returns (mv (order true-listp)
               (remaining treeset::setp))
  :parents (cyclicp)
  :short "Run Kahn's algorithm on a @(see graph), returning the order of removal
          and the nodes left."
  (b* ((nodes (nodes graph))
       (counters (kahn-counters nodes (treemap::empty) graph)))
    (kahn-loop nodes
               (treeset::diff nodes (treemap::keys counters))
               counters
               nil
               graph)))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (kahn graph0)
                  (kahn graph1)))
  :rule-classes :congruence
  :enable kahn)

(defrule mv-nth-0-of-kahn
  (equal (mv-nth 0 (kahn graph))
         (revappend (kahn-order (nodes graph) graph) nil))
  :enable kahn)

(defrule mv-nth-1-of-kahn
  (equal (mv-nth 1 (kahn graph))
         (kahn-remaining (nodes graph) graph))
  :enable kahn)
