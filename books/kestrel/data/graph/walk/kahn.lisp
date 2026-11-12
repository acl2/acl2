; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../successors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))

(local (include-book "../graph"))
(local (include-book "../nodes"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl emptyp-of-delete-by-cardinality
  (equal (tset::emptyp (tset::delete x set))
         (if (tset::in x set)
             (equal (tset::cardinality set) 1)
           (tset::emptyp set)))
  :use (:instance tset::equal-of-cardinality-and-0-becomes-emptyp
                  (set (tset::delete x set)))
  :enable tset::delete-when-not-in
  :disable tset::emptyp-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Kahn's algorithm removes, one at a time, a node with no edge into it from
;; the nodes not yet removed. This version takes the least such node. The nodes
;; left when there is none are those reachable from a cycle.

(define kahn-remaining ((remaining tset::setp) (graph graphp))
  :type-prescription :none
  :returns (remaining$ tset::setp)
  :parents (cyclicp)
  :short "The nodes Kahn's algorithm cannot remove, which are those reachable
          from a cycle."
  (b* ((sources (tset::diff remaining
                            (successors-of-set remaining graph)))
       ((when (tset::emptyp sources))
        (tset::fix remaining)))
    (kahn-remaining (tset::delete (tset::min sources) remaining)
                    graph))
  :measure (tset::cardinality remaining)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-remaining-when-equiv-of-arg1-congruence
  (implies (tset::equiv remaining0 remaining1)
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

(define kahn-order ((remaining tset::setp) (graph graphp))
  :type-prescription :none
  :returns (order true-listp)
  :parents (topological-sort)
  :short "The nodes Kahn's algorithm removes, in the order of removal."
  (b* ((sources (tset::diff remaining
                            (successors-of-set remaining graph)))
       ((when (tset::emptyp sources))
        nil)
       (node (tset::min sources)))
    (cons node
          (kahn-order (tset::delete node remaining) graph)))
  :measure (tset::cardinality remaining)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-order-when-equiv-of-arg1-congruence
  (implies (tset::equiv remaining0 remaining1)
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

(define kahn-increment ((targets tset::setp) (counters tmap::mapp))
  :type-prescription :none
  :returns (counters$ tmap::mapp)
  :parents (cyclicp)
  :short "Increment the counter of each node in a set."
  (b* (((when (tset::emptyp targets))
        (tmap::fix counters))
       (node (tset::min targets))
       (count (nfix (tmap::lookup node counters :default 0))))
    (kahn-increment (tset::delete node targets)
                    (tmap::update node (+ 1 count) counters)))
  :measure (tset::cardinality targets))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-increment-when-equiv-of-arg1-congruence
  (implies (tset::equiv targets0 targets1)
           (equal (kahn-increment targets0 counters)
                  (kahn-increment targets1 counters)))
  :rule-classes :congruence
  :expand ((kahn-increment targets0 counters)
           (kahn-increment targets1 counters)))

(defrule kahn-increment-when-equiv-of-arg2-congruence
  (implies (tmap::equiv counters0 counters1)
           (equal (kahn-increment targets counters0)
                  (kahn-increment targets counters1)))
  :rule-classes :congruence
  :induct t
  :enable kahn-increment)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kahn-counters
  ((set tset::setp)
   (counters tmap::mapp)
   (graph graphp))
  :type-prescription :none
  :returns (counters$ tmap::mapp)
  :parents (cyclicp)
  :short "Count, for each node, the nodes of a set with an edge to it."
  (b* (((when (tset::emptyp set))
        (tmap::fix counters))
       (node (tset::min set)))
    (kahn-counters (tset::delete node set)
                   (kahn-increment (successors node graph) counters)
                   graph))
  :measure (tset::cardinality set))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-counters-when-equiv-of-arg1-congruence
  (implies (tset::equiv set0 set1)
           (equal (kahn-counters set0 counters graph)
                  (kahn-counters set1 counters graph)))
  :rule-classes :congruence
  :expand ((kahn-counters set0 counters graph)
           (kahn-counters set1 counters graph)))

(defrule kahn-counters-when-equiv-of-arg2-congruence
  (implies (tmap::equiv counters0 counters1)
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
  ((targets tset::setp)
   (frontier tset::setp)
   (counters tmap::mapp))
  :type-prescription :none
  :returns (mv (frontier$ tset::setp)
               (counters$ tmap::mapp))
  :parents (cyclicp)
  :short "Decrement the counter of each node in a set, moving each node whose
          counter reaches zero to the frontier."
  (b* (((when (tset::emptyp targets))
        (mv (tset::fix frontier)
            (tmap::fix counters)))
       (node (tset::min targets))
       (count (nfix (tmap::lookup node counters :default 0)))
       ((when (eql count 1))
        (kahn-decrement (tset::delete node targets)
                        (tset::insert node frontier)
                        (tmap::delete node counters))))
    (kahn-decrement (tset::delete node targets)
                    frontier
                    (tmap::update node (- count 1) counters)))
  :measure (tset::cardinality targets))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-decrement-when-equiv-of-arg1-congruence
  (implies (tset::equiv targets0 targets1)
           (equal (kahn-decrement targets0 frontier counters)
                  (kahn-decrement targets1 frontier counters)))
  :rule-classes :congruence
  :expand ((kahn-decrement targets0 frontier counters)
           (kahn-decrement targets1 frontier counters)))

(defrule kahn-decrement-when-equiv-of-arg2-congruence
  (implies (tset::equiv frontier0 frontier1)
           (equal (kahn-decrement targets frontier0 counters)
                  (kahn-decrement targets frontier1 counters)))
  :rule-classes :congruence
  :induct t
  :enable kahn-decrement)

(defrule kahn-decrement-when-equiv-of-arg3-congruence
  (implies (tmap::equiv counters0 counters1)
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
  ((remaining tset::setp)
   (frontier tset::setp)
   (counters tmap::mapp)
   (order true-listp)
   (graph graphp))
  :type-prescription :none
  :returns (mv (order$ true-listp
                       :hyp (true-listp order))
               (remaining$ tset::setp))
  :parents (cyclicp)
  :short "Kahn's algorithm with counters and a frontier, accumulating the order
          of removal."
  (b* (((when (tset::emptyp frontier))
        (mv order (tset::fix remaining)))
       (node (tset::min frontier))
       ((unless (tset::in node remaining))
        (mv order (tset::fix remaining)))
       ((mv frontier counters)
        (kahn-decrement (successors node graph)
                        (tset::delete node frontier)
                        counters)))
    (kahn-loop (tset::delete node remaining)
               frontier
               counters
               (cons node order)
               graph))
  :measure (tset::cardinality remaining))

;;;;;;;;;;;;;;;;;;;;

(defrule kahn-loop-when-equiv-of-arg1-congruence
  (implies (tset::equiv remaining0 remaining1)
           (equal (kahn-loop remaining0 frontier counters order graph)
                  (kahn-loop remaining1 frontier counters order graph)))
  :rule-classes :congruence
  :expand ((kahn-loop remaining0 frontier counters order graph)
           (kahn-loop remaining1 frontier counters order graph)))

(defrule kahn-loop-when-equiv-of-arg2-congruence
  (implies (tset::equiv frontier0 frontier1)
           (equal (kahn-loop remaining frontier0 counters order graph)
                  (kahn-loop remaining frontier1 counters order graph)))
  :rule-classes :congruence
  :expand ((kahn-loop remaining frontier0 counters order graph)
           (kahn-loop remaining frontier1 counters order graph)))

(defrule kahn-loop-when-equiv-of-arg3-congruence
  (implies (tmap::equiv counters0 counters1)
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
  (implies (and (tset::in node (successors pred graph))
                (tset::in pred set))
           (< 0 (tset::cardinality
                  (tset::intersect set (predecessors node graph)))))
  :rule-classes :linear
  :enable tset::cardinality-when-not-emptyp-linear)

;; A set including its own successors includes the successors of its nodes.

(defrulel in-when-in-of-successors-and-subset-of-successors-of-set
  (implies (and (tset::subset (successors-of-set set graph) set)
                (tset::in pred set)
                (tset::in node (successors pred graph)))
           (tset::in node set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The efficient version leaves the same nodes. Its invariant: the remaining
;; nodes include their own successors, the counters are those computed afresh
;; for the remaining nodes, and the frontier is the remaining nodes that are
;; not successors of remaining nodes.

(defrulel lookup-of-kahn-increment
  (equal (tmap::lookup node
                       (kahn-increment targets counters)
                       :default default)
         (if (tset::in node targets)
             (+ 1 (nfix (tmap::lookup node counters :default 0)))
           (tmap::lookup node counters :default default)))
  :induct t
  :enable kahn-increment)

(defrulel in-of-keys-of-kahn-increment
  (equal (tset::in node (tmap::keys (kahn-increment targets counters)))
         (or (tset::in node targets)
             (tset::in node (tmap::keys counters))))
  :induct t
  :enable kahn-increment)

(defrulel lookup-of-kahn-counters
  (equal (tmap::lookup node
                       (kahn-counters set counters graph)
                       :default default)
         (if (tset::emptyp
               (tset::intersect set (predecessors node graph)))
             (tmap::lookup node counters :default default)
           (+ (nfix (tmap::lookup node counters :default 0))
              (tset::cardinality
                (tset::intersect set (predecessors node graph))))))
  :induct t
  :enable (kahn-counters
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable tset::emptyp-of-delete)

(defrulel in-of-keys-of-kahn-counters
  (equal (tset::in node
                   (tmap::keys (kahn-counters set counters graph)))
         (or (tset::in node (successors-of-set set graph))
             (tset::in node (tmap::keys counters))))
  :induct t
  :enable (kahn-counters
           successors-of-set))

(defrulel in-of-mv-nth-0-of-kahn-decrement
  (equal (tset::in node
                   (mv-nth 0 (kahn-decrement targets frontier counters)))
         (or (tset::in node frontier)
             (and (tset::in node targets)
                  (equal (nfix (tmap::lookup node counters :default 0))
                         1))))
  :induct t
  :enable kahn-decrement)

(defrulel lookup-of-mv-nth-1-of-kahn-decrement
  (equal (tmap::lookup node
                       (mv-nth 1 (kahn-decrement targets frontier counters))
                       :default default)
         (if (tset::in node targets)
             (if (equal (nfix (tmap::lookup node counters :default 0)) 1)
                 default
               (- (nfix (tmap::lookup node counters :default 0)) 1))
           (tmap::lookup node counters :default default)))
  :induct t
  :enable kahn-decrement)

;; The initial state

(defrulel keys-of-kahn-counters-of-empty
  (equal (tmap::keys (kahn-counters set (tmap::empty) graph))
         (successors-of-set set graph))
  :enable tset::extensionality-polar)

;; A step

(defrulel mv-nth-1-of-kahn-decrement-of-successors
  (implies (tset::in node remaining)
           (equal (mv-nth 1 (kahn-decrement
                              (successors node graph)
                              frontier
                              (kahn-counters remaining (tmap::empty) graph)))
                  (kahn-counters (tset::delete node remaining)
                                 (tmap::empty)
                                 graph)))
  :enable (tmap::extensionality
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable tset::emptyp-of-delete)

(defrulel mv-nth-0-of-kahn-decrement-of-successors
  (implies (and (tset::subset (successors-of-set remaining graph)
                              remaining)
                (tset::in node remaining)
                (not (tset::in node (successors-of-set remaining graph))))
           (equal (mv-nth 0 (kahn-decrement
                              (successors node graph)
                              (tset::delete
                                node
                                (tset::diff
                                  remaining
                                  (successors-of-set remaining graph)))
                              (kahn-counters remaining
                                             (tmap::empty)
                                             graph)))
                  (tset::diff (tset::delete node remaining)
                              (successors-of-set
                                (tset::delete node remaining)
                                graph))))
  :enable (tset::extensionality-polar
           in-of-successors-of-set-becomes-not-emptyp-of-intersect
           emptyp-of-delete-by-cardinality
           nfix
           acl2::fix)
  :disable tset::emptyp-of-delete)

;; So the loop leaves what the logical version leaves, and removes the nodes in
;; the same order, accumulating them most recent first.

(defrulel mv-nth-1-of-kahn-loop
  (implies (and (tset::subset (successors-of-set remaining graph)
                              remaining)
                (equal counters
                       (kahn-counters remaining (tmap::empty) graph))
                (equal frontier
                       (tset::diff remaining
                                   (successors-of-set remaining graph))))
           (equal (mv-nth 1 (kahn-loop remaining frontier counters order graph))
                  (kahn-remaining remaining graph)))
  :induct (kahn-loop remaining frontier counters order graph)
  :enable (kahn-loop
           kahn-remaining))

(defrulel mv-nth-0-of-kahn-loop
  (implies (and (tset::subset (successors-of-set remaining graph)
                              remaining)
                (equal counters
                       (kahn-counters remaining (tmap::empty) graph))
                (equal frontier
                       (tset::diff remaining
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
  :type-prescription :none
  :returns (mv (order true-listp)
               (remaining tset::setp))
  :parents (cyclicp)
  :short "Run Kahn's algorithm on a @(see graph), returning the order of removal
          and the nodes left."
  (b* ((nodes (nodes graph))
       (counters (kahn-counters nodes (tmap::empty) graph)))
    (kahn-loop nodes
               (tset::diff nodes (tmap::keys counters))
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
