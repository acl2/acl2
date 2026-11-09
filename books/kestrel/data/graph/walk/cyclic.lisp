; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
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
(include-book "../adjacency-defs")
(include-book "../successors-defs")
(include-book "reachable-defs")

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
(local (include-book "../adjacency"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))
(local (include-book "reachable"))

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

(define-sk cyclicp-sk (graph)
  :parents (cyclicp)
  :short "Check if some node of a @(see graph) reaches itself."
  :long
  (xdoc::topstring-p
    "This is the specification of @(tsee cyclicp), to which it is equal. It
     is not executable.")
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (exists (node)
    (non-exec (reachable+p node node graph))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t cyclicp-sk)))

(defrule cyclicp-sk-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (cyclicp-sk graph0)
                  (cyclicp-sk graph1)))
  :rule-classes :congruence
  :use ((:instance cyclicp-sk-suff
                   (node (cyclicp-sk-witness graph0))
                   (graph graph1))
        (:instance cyclicp-sk-suff
                   (node (cyclicp-sk-witness graph1))
                   (graph graph0)))
  :enable cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Kahn's algorithm removes, one at a time, a node with no edge into it from
;; the nodes not yet removed. This version takes the least such node. The nodes
;; left when there is none are those reachable from a cycle.

(define kahn-remaining ((remaining treeset::setp) (graph graphp))
  :type-prescription :none
  :returns (remaining$ treeset::setp)
  :parents (cyclicp)
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
;; intersected with the set. A node is a successor of the set exactly when it
;; has one.

(defrulel emptyp-of-intersect-and-predecessors-when-in-of-successors
  (implies (and (treeset::in node (successors pred graph))
                (treeset::in pred set))
           (not (treeset::emptyp
                  (treeset::intersect set (predecessors node graph)))))
  :use (:instance treeset::not-emptyp-when-in
                  (x pred)
                  (set (treeset::intersect set (predecessors node graph)))))

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

;; Removing a node which is not one of their successors keeps that so.

(defrulel subset-of-successors-of-set-of-delete-and-delete
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (not (treeset::in node (successors-of-set set graph))))
           (treeset::subset (successors-of-set (treeset::delete node set)
                                               graph)
                            (treeset::delete node set)))
  :enable treeset::pick-a-point-polar)

(defruledl in-of-successors-of-set-becomes-not-emptyp-of-intersect
  (equal (treeset::in node (successors-of-set set graph))
         (not (treeset::emptyp
                (treeset::intersect set (predecessors node graph)))))
  :induct (successors-of-set set graph)
  :enable (successors-of-set
           emptyp-of-delete-by-cardinality)
  :disable treeset::emptyp-of-delete)

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

(defrulel diff-of-arg1-and-keys-of-kahn-counters
  (equal (treeset::diff set
                        (treemap::keys
                          (kahn-counters set (treemap::empty) graph)))
         (treeset::diff set (successors-of-set set graph)))
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

;; So the loop leaves what the logical version leaves.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cyclicp ((graph graphp))
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Check if a @(see graph) has a cycle."
  :long
  (xdoc::topstring
    (xdoc::p
      "A graph has a cycle exactly when some node reaches itself (see @(tsee
       reachable+p)). Logically this equals @(tsee cyclicp-sk), which states
       that directly. A graph without a cycle is a directed acyclic graph.")
    (xdoc::p
      "This uses Kahn's algorithm: it repeatedly removes a node with no edge
       into it from the nodes not yet removed, and the graph has a cycle
       exactly when it gets stuck before removing every node. It keeps, for
       each node, the number of nodes not yet removed with an edge to it.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
       nodes and @($m$) the number of pairs of nodes joined by an edge."))
  (mbe :logic (not (treeset::emptyp (kahn-remaining (nodes graph) graph)))
       :exec (b* ((nodes (nodes graph))
                  (counters (kahn-counters nodes (treemap::empty) graph))
                  ((mv - remaining)
                   (kahn-loop nodes
                              (treeset::diff nodes (treemap::keys counters))
                              counters
                              nil
                              graph)))
               (not (treeset::emptyp remaining)))))

;;;;;;;;;;;;;;;;;;;;

(defrule cyclicp-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (cyclicp graph0)
                  (cyclicp graph1)))
  :rule-classes :congruence
  :enable cyclicp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness: no node removed reaches itself. The remaining nodes include
;; their own successors, and still do after a node which is not one of their
;; successors is removed. Every node reachable from that node is then still
;; remaining, so the node itself is not.

(defrulel reachable+p-when-not-in-of-successors-of-set
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (treeset::in node set)
                (not (treeset::in node (successors-of-set set graph))))
           (not (reachable+p node node graph)))
  :enable in-when-reachable+p-and-subset-of-successors-of-set)

(defruledl reachable+p-when-not-in-of-kahn-remaining
  (implies (and (treeset::subset (successors-of-set remaining graph)
                                 remaining)
                (treeset::in node remaining)
                (not (treeset::in node (kahn-remaining remaining graph))))
           (not (reachable+p node node graph)))
  :induct (kahn-remaining remaining graph)
  :enable kahn-remaining)

;; A value which is not a node reaches nothing.

(defrulel in-of-nodes-when-reachable+p
  (implies (reachable+p from to graph)
           (treeset::in from (nodes graph)))
  :use (:instance in-when-reachable+p-and-subset-of-successors-of-set
                  (set (treeset::empty)))
  :enable successors-of-set)

(defruledl not-emptyp-of-kahn-remaining-when-cyclicp-sk
  (implies (cyclicp-sk graph)
           (not (treeset::emptyp (kahn-remaining (nodes graph) graph))))
  :use (:instance reachable+p-when-not-in-of-kahn-remaining
                  (node (cyclicp-sk-witness graph))
                  (remaining (nodes graph)))
  :enable cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness: a nonempty set whose nodes are all successors of its nodes has a
;; node on a cycle, so when there is no cycle, Kahn's algorithm removes every
;; node.
;;
;; In such a set, the nodes of the set reaching any one of its nodes form
;; another such set. If the least node is not on a cycle, the set formed for it
;; leaves it out, so the search descends into a smaller set.

(defrulel reachable+p-when-not-cyclicp-sk
  (implies (not (cyclicp-sk graph))
           (not (reachable+p node node graph)))
  :enable cyclicp-sk-suff)

(local
  (define find-node-on-cycle ((set treeset::setp) graph)
    (b* (((when (treeset::emptyp set))
          nil)
         (node (treeset::min set))
         ((when (reachable+p node node graph))
          node))
      (find-node-on-cycle (treeset::intersect set (predecessors+ node graph))
                          graph))
    :measure (treeset::cardinality set)
    :hints (("Goal" :use (:instance treeset::in-of-min-when-subset
                                    (treeset::set set)
                                    (treeset::y (predecessors+
                                                  (treeset::min set)
                                                  graph)))
                    :in-theory (disable treeset::in-of-min-when-subset)))
    :verify-guards nil))

(defrulel find-node-on-cycle-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
           (equal (find-node-on-cycle set0 graph)
                  (find-node-on-cycle set1 graph)))
  :rule-classes :congruence
  :expand ((find-node-on-cycle set0 graph)
           (find-node-on-cycle set1 graph)))

;; The predecessors of a node reaching another reach it too.

(defrulel reachable+p-when-reachable+p-and-in-of-successors
  (implies (and (reachable+p node to graph)
                (treeset::in node (successors from graph)))
           (reachable+p from to graph))
  :use (:instance reachable+p-transitivity (x node))
  :disable reachable+p-transitivity)

(defrulel subset-of-predecessors-and-predecessors+-when-reachable+p
  (implies (reachable+p node to graph)
           (treeset::subset (predecessors node graph)
                            (predecessors+ to graph)))
  :enable treeset::pick-a-point-polar)

;; A node stays a successor of a set restricted to another which includes its
;; predecessors.

(defrulel in-of-successors-of-set-of-intersect
  (implies (and (treeset::subset (predecessors node graph) set2)
                (treeset::in node (successors-of-set set graph)))
           (treeset::in node
                        (successors-of-set (treeset::intersect set set2)
                                           graph)))
  :enable in-of-successors-of-set-becomes-not-emptyp-of-intersect)

;; So in a set whose nodes are all successors of its nodes, the nodes reaching
;; a given node of it form a nonempty set whose nodes are all successors of its
;; nodes.

(defrulel emptyp-of-intersect-and-predecessors+
  (implies (treeset::in node (successors-of-set set graph))
           (not (treeset::emptyp
                  (treeset::intersect set (predecessors+ node graph)))))
  :use (:instance in-of-successors-of-set-of-intersect
                  (set2 (predecessors+ node graph)))
  :expand (successors-of-set (treeset::intersect set (predecessors+ node graph))
                             graph)
  :disable in-of-successors-of-set-of-intersect)

(defrulel subset-of-intersect-and-successors-of-set-of-intersect
  (implies (treeset::subset set (successors-of-set set graph))
           (treeset::subset
             (treeset::intersect set (predecessors+ node graph))
             (successors-of-set
               (treeset::intersect set (predecessors+ node graph))
               graph)))
  :enable treeset::pick-a-point-polar)

(defrulel reachable+p-of-find-node-on-cycle
  (implies (and (treeset::subset set (successors-of-set set graph))
                (not (treeset::emptyp set)))
           (reachable+p (find-node-on-cycle set graph)
                        (find-node-on-cycle set graph)
                        graph))
  :induct t
  :enable find-node-on-cycle)

(defruledl subset-of-arg1-and-successors-of-set-when-not-cyclicp-sk
  (implies (and (not (cyclicp-sk graph))
                (not (treeset::emptyp set)))
           (not (treeset::subset set (successors-of-set set graph))))
  :use (:instance reachable+p-when-not-cyclicp-sk
                  (node (find-node-on-cycle set graph)))
  :disable reachable+p-when-not-cyclicp-sk)

;; Kahn's algorithm stops only at a set whose nodes are all successors of its
;; nodes.

(defrulel subset-of-kahn-remaining-and-successors-of-set
  (treeset::subset (kahn-remaining remaining graph)
                   (successors-of-set (kahn-remaining remaining graph) graph))
  :induct t
  :enable kahn-remaining)

(defruledl emptyp-of-kahn-remaining-when-not-cyclicp-sk
  (implies (not (cyclicp-sk graph))
           (treeset::emptyp (kahn-remaining remaining graph)))
  :use (:instance subset-of-arg1-and-successors-of-set-when-not-cyclicp-sk
                  (set (kahn-remaining remaining graph))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cyclicp-becomes-cyclicp-sk
  (equal (cyclicp graph)
         (cyclicp-sk graph))
  :enable (cyclicp
           not-emptyp-of-kahn-remaining-when-cyclicp-sk
           emptyp-of-kahn-remaining-when-not-cyclicp-sk))

(defruled cyclicp-sk-becomes-cyclicp
  (equal (cyclicp-sk graph)
         (cyclicp graph))
  :by cyclicp-becomes-cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A graph without a cycle has no node which reaches itself, and a graph with
;; such a node has a cycle.

(defruled reachable+p-of-arg1-and-arg1-when-not-cyclicp
  (implies (not (cyclicp graph))
           (not (reachable+p node node graph)))
  :enable cyclicp-becomes-cyclicp-sk)

(defrule reachable+p-of-arg1-and-arg1-when-not-cyclicp-cheap
  (implies (not (cyclicp graph))
           (not (reachable+p node node graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by reachable+p-of-arg1-and-arg1-when-not-cyclicp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy cyclic-extra-rules
  '(reachable+p-of-arg1-and-arg1-when-not-cyclicp))
