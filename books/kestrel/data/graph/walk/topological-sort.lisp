; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/intersect-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../predecessors-defs")
(include-book "reachable-defs")
(include-book "kahn-defs")
(include-book "cyclic-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))

(local (include-book "../nodes"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))
(local (include-book "reachable"))
(local (include-book "kahn"))
(local (include-book "cyclic"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel from-list-of-cons
  (equal (treeset::from-list (cons x list))
         (treeset::insert x (treeset::from-list list)))
  :enable treeset::extensionality-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reachable+p-sortedp ((list true-listp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (topological-orderp)
  :short "Check if no node in a list reaches itself or an earlier node of the
          list."
  :long
  (xdoc::topstring-p
    "That is, a node does not reach any node at or before it in the list (see
     @(tsee reachable+p)). The list need not contain every node.")
  (or (endp list)
      (and (treeset::emptyp
             (treeset::intersect (predecessors+ (first list) graph)
                                 (treeset::from-list list)))
           (reachable+p-sortedp (rest list) graph))))

;;;;;;;;;;;;;;;;;;;;

(defrule reachable+p-sortedp-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (reachable+p-sortedp list graph0)
                  (reachable+p-sortedp list graph1)))
  :rule-classes :congruence
  :induct t
  :enable reachable+p-sortedp)

;;;;;;;;;;;;;;;;;;;;

;; No node of a sorted list reaches its first node.

(defrulel reachable+p-of-car-when-reachable+p-sortedp
  (implies (and (reachable+p-sortedp list graph)
                (member-equal from list))
           (not (reachable+p from (car list) graph)))
  :use (:instance treeset::not-emptyp-when-in
                  (x from)
                  (set (treeset::intersect (predecessors+ (car list) graph)
                                           (treeset::from-list list))))
  :enable reachable+p-sortedp)

;; So a node does not reach any node at or before it, and in particular not
;; itself.

(defruled reachable+p-when-reachable+p-sortedp
  (implies (and (reachable+p-sortedp list graph)
                (member-equal from (member-equal to list)))
           (not (reachable+p from to graph)))
  :induct (member-equal to list)
  :enable (reachable+p-sortedp
           member-equal))

;; Equivalently, of two nodes in the list, one reaching the other comes before
;; it.

(defruled member-equal-of-cdr-of-member-equal-when-reachable+p-sortedp
  (implies (and (reachable+p from to graph)
                (reachable+p-sortedp list graph)
                (member-equal from list)
                (member-equal to list))
           (member-equal to (cdr (member-equal from list))))
  :induct (member-equal from list)
  :enable (reachable+p-sortedp
           member-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topological-orderp ((order true-listp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (topological-sort)
  :short "Check if a list is a topological order of a @(see graph)."
  :long
  (xdoc::topstring-p
    "A topological order lists every node exactly once, and no node reaches
     itself or an earlier node (see @(tsee reachable+p-sortedp)). A graph has
     a topological order exactly when it has no cycle (see @(tsee
     cyclicp)).")
  (and (no-duplicatesp-equal order)
       (equal (treeset::from-list order) (nodes graph))
       (reachable+p-sortedp order graph)))

;;;;;;;;;;;;;;;;;;;;

(defrule topological-orderp-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (topological-orderp order graph0)
                  (topological-orderp order graph1)))
  :rule-classes :congruence
  :enable topological-orderp)

;;;;;;;;;;;;;;;;;;;;

;; A topological order lists exactly the nodes, each once, and is sorted.

(defrule member-equal-when-topological-orderp
  (implies (topological-orderp order graph)
           (iff (member-equal node order)
                (treeset::in node (nodes graph))))
  :enable topological-orderp)

(defrule no-duplicatesp-equal-when-topological-orderp
  (implies (topological-orderp order graph)
           (no-duplicatesp-equal order))
  :enable topological-orderp)

(defrule reachable+p-sortedp-when-topological-orderp
  (implies (topological-orderp order graph)
           (reachable+p-sortedp order graph))
  :enable topological-orderp)

;; Every node comes after every node reaching it.

(defrule member-equal-of-cdr-of-member-equal-when-topological-orderp
  (implies (and (topological-orderp order graph)
                (reachable+p from to graph))
           (member-equal to (cdr (member-equal from order))))
  :enable member-equal-of-cdr-of-member-equal-when-reachable+p-sortedp)

;; A graph with a topological order has no cycle: some node of a cycle would
;; reach itself.

(defruledl reachable+p-of-arg1-and-arg1-when-reachable+p-sortedp
  (implies (and (reachable+p-sortedp list graph)
                (member-equal node list))
           (not (reachable+p node node graph)))
  :induct (member-equal node list)
  :enable (reachable+p-sortedp
           member-equal))

(defrule cyclicp-when-topological-orderp
  (implies (topological-orderp order graph)
           (not (cyclicp graph)))
  :use (:instance reachable+p-of-arg1-and-arg1-when-reachable+p-sortedp
                  (list order)
                  (node (cyclicp-sk-witness graph)))
  :enable (cyclicp-becomes-cyclicp-sk
           cyclicp-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topological-sort ((graph graphp))
  :returns (mv (cyclicp booleanp)
               (order true-listp))
  :parents (walks)
  :short "Order the nodes of a @(see graph) so that no node reaches an earlier
          one."
  :long
  (xdoc::topstring
    (xdoc::p
      "The first value is @(tsee cyclicp). When the graph has no cycle, the
       second value is a topological order of it (see @(tsee
       topological-orderp)). When it has a cycle, the second value lists only
       some of the nodes, still without repetition and with no node reaching
       itself or an earlier one (see @(tsee reachable+p-sortedp)).")
    (xdoc::p
      "This uses Kahn's algorithm, as @(tsee cyclicp) does: it repeatedly
       removes a node with no edge into it from the nodes not yet removed, and
       lists the nodes in the order they are removed.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
       nodes and @($m$) the number of pairs of nodes joined by an edge."))
  (mbe :logic (mv (cyclicp graph)
                  (kahn-order (nodes graph) graph))
       :exec (b* ((nodes (nodes graph))
                  (counters (kahn-counters nodes (treemap::empty) graph))
                  ((mv order remaining)
                   (kahn-loop nodes
                              (treeset::diff nodes (treemap::keys counters))
                              counters
                              nil
                              graph)))
               (mv (not (treeset::emptyp remaining))
                   (revappend order nil))))
  :guard-hints (("Goal" :in-theory (enable cyclicp))))

;;;;;;;;;;;;;;;;;;;;

(defrule topological-sort-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (topological-sort graph0)
                  (topological-sort graph1)))
  :rule-classes :congruence
  :enable topological-sort)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Kahn's algorithm removes each node at most once, and lists exactly the nodes
;; it removes: those not left over.

(defrulel in-of-kahn-remaining-when-not-in
  (implies (not (treeset::in node remaining))
           (not (treeset::in node (kahn-remaining remaining graph))))
  :induct t
  :enable kahn-remaining)

(defrulel member-equal-of-kahn-order
  (iff (member-equal node (kahn-order remaining graph))
       (and (treeset::in node remaining)
            (not (treeset::in node (kahn-remaining remaining graph)))))
  :induct (kahn-order remaining graph)
  :enable (kahn-order
           kahn-remaining))

(defrulel no-duplicatesp-equal-of-kahn-order
  (no-duplicatesp-equal (kahn-order remaining graph))
  :induct t
  :enable (kahn-order
           no-duplicatesp-equal))

(defrulel from-list-of-kahn-order
  (equal (treeset::from-list (kahn-order remaining graph))
         (treeset::diff remaining (kahn-remaining remaining graph)))
  :enable treeset::extensionality-polar)

;; The remaining nodes include their own successors, so no remaining node
;; reaches the node removed, which is not one of their successors.

(defrulel emptyp-of-intersect-of-predecessors+-when-not-in-of-successors-of-set
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (not (treeset::in node (successors-of-set set graph)))
                (treeset::subset set2 set))
           (treeset::emptyp
             (treeset::intersect (predecessors+ node graph) set2)))
  :use (:instance treeset::in-of-min
                  (set (treeset::intersect (predecessors+ node graph) set2)))
  :enable reachable+p-when-not-in-of-successors-of-set
  :disable treeset::in-of-min)

(defrulel reachable+p-sortedp-of-kahn-order
  (implies (treeset::subset (successors-of-set remaining graph)
                            remaining)
           (reachable+p-sortedp (kahn-order remaining graph) graph))
  :induct (kahn-order remaining graph)
  :enable (kahn-order
           reachable+p-sortedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule mv-nth-0-of-topological-sort
  (equal (mv-nth 0 (topological-sort graph))
         (cyclicp graph))
  :enable topological-sort)

;; The order is sorted, without repetition, and lists only nodes, whether or
;; not the graph has a cycle.

(defrule reachable+p-sortedp-of-mv-nth-1-of-topological-sort
  (reachable+p-sortedp (mv-nth 1 (topological-sort graph)) graph)
  :enable topological-sort)

(defrule no-duplicatesp-equal-of-mv-nth-1-of-topological-sort
  (no-duplicatesp-equal (mv-nth 1 (topological-sort graph)))
  :enable topological-sort)

(defrule subset-of-from-list-of-mv-nth-1-of-topological-sort-and-nodes
  (treeset::subset (treeset::from-list (mv-nth 1 (topological-sort graph)))
                   (nodes graph))
  :enable topological-sort)

;; It is a topological order exactly when the graph has no cycle: when there is
;; none, Kahn's algorithm removes every node.

(defrulel topological-orderp-of-kahn-order-when-not-cyclicp
  (implies (not (cyclicp graph))
           (topological-orderp (kahn-order (nodes graph) graph) graph))
  :enable (topological-orderp
           cyclicp))

(defrule topological-orderp-of-mv-nth-1-of-topological-sort
  (equal (topological-orderp (mv-nth 1 (topological-sort graph)) graph)
         (not (cyclicp graph)))
  :enable (topological-sort
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy topological-sort-extra-rules
  '(reachable+p-when-reachable+p-sortedp
    member-equal-of-cdr-of-member-equal-when-reachable+p-sortedp))
