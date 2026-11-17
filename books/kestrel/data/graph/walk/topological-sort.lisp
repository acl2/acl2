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

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/intersect-defs" :dir :system)
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../successors-defs")
(include-book "../predecessors-defs")
(include-book "reachable-defs")
(include-book "kahn-defs")
(include-book "cyclic-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))

(local (include-book "../nodes"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))
(local (include-book "reachable"))
(local (include-book "kahn"))
(local (include-book "cyclic"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In a set containing the successors of its own nodes, the nodes reaching a
;; node which is not one of those successors are outside the set. A node which
;; is reached by no node of a set is not one of its successors.

(defrulel emptyp-of-intersect-of-predecessors+-when-not-in-of-successors-of-set
  (implies (and (tset::subset (successors-of-set set graph) set)
                (not (tset::in node (successors-of-set set graph)))
                (tset::subset set2 set))
           (tset::emptyp
             (tset::intersect (predecessors+ node graph) set2)))
  :use (:instance tset::in-of-min
                  (set (tset::intersect (predecessors+ node graph) set2)))
  :enable reachable+p-when-not-in-of-successors-of-set
  :disable tset::in-of-min)

(defrulel in-of-successors-of-set-when-emptyp-of-intersect-of-predecessors+
  (implies (tset::emptyp
             (tset::intersect (predecessors+ node graph) set))
           (not (tset::in node (successors-of-set set graph))))
  :use ((:instance tset::in-of-min
                   (set (tset::intersect set (predecessors node graph))))
        (:instance tset::not-emptyp-when-in
                   (x (tset::min
                        (tset::intersect set (predecessors node graph))))
                   (set (tset::intersect set
                                         (predecessors+ node graph)))))
  :enable in-of-successors-of-set-becomes-not-emptyp-of-intersect
  :disable tset::in-of-min)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reachable+p-sortedp ((list true-listp) (graph graphp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (topological-orderp)
  :short "Check if no node in a list reaches itself or an earlier node of the
          list."
  :long
  (xdoc::topstring-p
    "That is, a node does not reach any node at or before it in the list (see
     @(tsee reachable+p)). The list need not contain every node.")
  (or (endp list)
      (and (tset::emptyp
             (tset::intersect (predecessors+ (first list) graph)
                              (tset::from-list list)))
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
  :use (:instance tset::not-emptyp-when-in
                  (x from)
                  (set (tset::intersect (predecessors+ (car list) graph)
                                        (tset::from-list list))))
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

;; The efficient check of a topological order walks the list once, keeping the
;; set of nodes seen. It rejects a node already seen, or one with an edge to
;; itself or to a node seen, and at the end checks that the nodes seen are the
;; nodes.

(define topological-orderp-loop
  ((order true-listp)
   (seen tset::setp)
   (graph graphp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (topological-orderp)
  :short "Check a list in one pass, keeping the set of nodes seen."
  (b* (((when (endp order))
        (equal (tset::fix seen) (nodes graph)))
       (node (first order))
       ((when (tset::in node seen))
        nil)
       (seen (tset::insert node seen)))
    (and (tset::emptyp
           (tset::intersect (successors node graph) seen))
         (topological-orderp-loop (rest order) seen graph))))

;;;;;;;;;;;;;;;;;;;;

(defrule topological-orderp-loop-when-equiv-of-arg2-congruence
  (implies (tset::equiv seen0 seen1)
           (equal (topological-orderp-loop order seen0 graph)
                  (topological-orderp-loop order seen1 graph)))
  :rule-classes :congruence
  :expand ((topological-orderp-loop order seen0 graph)
           (topological-orderp-loop order seen1 graph)))

(defrule topological-orderp-loop-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (topological-orderp-loop order seen graph0)
                  (topological-orderp-loop order seen graph1)))
  :rule-classes :congruence
  :induct t
  :enable topological-orderp-loop)

;;;;;;;;;;;;;;;;;;;;

;; When the check succeeds, the nodes seen and the nodes of the list are
;; together the nodes, the list has no repetition and no node seen, and no node
;; of the list has an edge to a node seen.

(defrulel union-of-arg2-and-from-list-when-topological-orderp-loop
  (implies (topological-orderp-loop order seen graph)
           (equal (tset::union seen (tset::from-list order))
                  (nodes graph)))
  :induct t
  :enable topological-orderp-loop)

(defrulel member-equal-when-topological-orderp-loop
  (implies (and (topological-orderp-loop order seen graph)
                (tset::in node seen))
           (not (member-equal node order)))
  :induct t
  :enable (topological-orderp-loop
           member-equal))

(defrulel no-duplicatesp-equal-when-topological-orderp-loop
  (implies (topological-orderp-loop order seen graph)
           (no-duplicatesp-equal order))
  :induct t
  :enable (topological-orderp-loop
           no-duplicatesp-equal))

(defrulel emptyp-of-intersect-of-arg2-and-successors-of-set-when-topological-orderp-loop
  (implies (topological-orderp-loop order seen graph)
           (tset::emptyp
             (tset::intersect seen
                              (successors-of-set (tset::from-list order)
                                                 graph))))
  :induct t
  :enable (topological-orderp-loop
           tset::from-list-when-consp
           tset::intersect-of-insert
           tset::intersect-of-arg1-and-insert))

;; So the nodes of the list include their own successors, and the first is not
;; one of them. Hence the list is sorted.

(defrulel subset-of-successors-of-set-of-from-list-when-topological-orderp-loop
  (implies (topological-orderp-loop order seen graph)
           (tset::subset (successors-of-set (tset::from-list order)
                                            graph)
                         (tset::from-list order)))
  :use (:instance tset::subset-of-arg1-and-union-when-emptyp-of-intersect0
                  (tset::x (successors-of-set (tset::from-list order)
                                              graph))
                  (tset::y seen)
                  (tset::z (tset::from-list order))))

(defrulel subset-of-successors-when-topological-orderp-loop
  (implies (and (topological-orderp-loop rest
                                         (tset::insert node seen)
                                         graph)
                (tset::emptyp
                  (tset::intersect (tset::insert node seen)
                                   (successors node graph))))
           (tset::subset (successors node graph)
                         (tset::from-list rest)))
  :use ((:instance tset::subset-of-arg1-and-union-when-emptyp-of-intersect0
                   (tset::x (successors node graph))
                   (tset::y (tset::insert node seen))
                   (tset::z (tset::from-list rest)))
        (:instance union-of-arg2-and-from-list-when-topological-orderp-loop
                   (order rest)
                   (seen (tset::insert node seen))))
  :disable union-of-arg2-and-from-list-when-topological-orderp-loop)

(defrulel emptyp-of-intersect-of-from-list-and-predecessors+-of-car-when-topological-orderp-loop
  (implies (and (topological-orderp-loop (cdr order)
                                         (tset::insert (car order) seen)
                                         graph)
                (consp order)
                (tset::emptyp
                  (tset::intersect (tset::insert (car order) seen)
                                   (successors (car order) graph))))
           (tset::emptyp
             (tset::intersect (tset::from-list order)
                              (predecessors+ (car order) graph))))
  :use ((:instance
          emptyp-of-intersect-of-predecessors+-when-not-in-of-successors-of-set
          (node (car order))
          (set (tset::from-list order))
          (set2 (tset::from-list order)))
        (:instance
          emptyp-of-intersect-of-arg2-and-successors-of-set-when-topological-orderp-loop
          (order (cdr order))
          (seen (tset::insert (car order) seen))))
  :enable (tset::from-list-when-consp
           tset::intersect-of-insert
           tset::intersect-of-arg1-and-insert)
  :disable
  (emptyp-of-intersect-of-predecessors+-when-not-in-of-successors-of-set
   emptyp-of-intersect-of-arg2-and-successors-of-set-when-topological-orderp-loop))

(defrulel reachable+p-sortedp-when-topological-orderp-loop
  (implies (topological-orderp-loop order seen graph)
           (reachable+p-sortedp order graph))
  :induct t
  :enable (topological-orderp-loop
           reachable+p-sortedp))

;; In the other direction, a sorted list repeating no node, such that it and
;; the nodes seen are together the nodes, with no node seen and no edge to a
;; node seen, passes the check.

(defrulel topological-orderp-loop-when-reachable+p-sortedp
  (implies (and (no-duplicatesp-equal order)
                (tset::emptyp
                  (tset::intersect seen (tset::from-list order)))
                (equal (tset::union seen (tset::from-list order))
                       (nodes graph))
                (reachable+p-sortedp order graph)
                (tset::emptyp
                  (tset::intersect
                    seen
                    (successors-of-set (tset::from-list order) graph))))
           (topological-orderp-loop order seen graph))
  :induct (topological-orderp-loop order seen graph)
  :enable (topological-orderp-loop
           reachable+p-sortedp
           no-duplicatesp-equal
           tset::from-list-when-consp
           tset::intersect-of-insert
           tset::intersect-of-arg1-and-insert))

(defrulel topological-orderp-loop-of-empty
  (equal (topological-orderp-loop order (tset::empty) graph)
         (and (no-duplicatesp-equal order)
              (equal (tset::from-list order) (nodes graph))
              (reachable+p-sortedp order graph)))
  :use ((:instance topological-orderp-loop-when-reachable+p-sortedp
                   (seen (tset::empty)))
        (:instance union-of-arg2-and-from-list-when-topological-orderp-loop
                   (seen (tset::empty))))
  :disable (topological-orderp-loop-when-reachable+p-sortedp
            union-of-arg2-and-from-list-when-topological-orderp-loop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topological-orderp ((order true-listp) (graph graphp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (topological-sort)
  :short "Check if a list is a topological order of a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "A topological order lists every node exactly once, and no node reaches
       itself or an earlier node (see @(tsee reachable+p-sortedp)). A graph
       has a topological order exactly when it has no cycle (see @(tsee
       cyclicp)).")
    (xdoc::p
      "In execution, this walks the list once, checking that no node repeats
       and that no node has an edge to itself or to an earlier node. For a
       list of every node, that is enough: a walk to an earlier node would
       need an edge to an earlier node somewhere along it.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
       nodes and @($m$) the number of pairs of nodes joined by an edge."))
  (mbe :logic (and (no-duplicatesp-equal order)
                   (equal (tset::from-list order) (nodes graph))
                   (reachable+p-sortedp order graph))
       :exec (topological-orderp-loop order (tset::empty) graph))
  :inline t)

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
                (tset::in node (nodes graph))))
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
       :exec (b* (((mv order remaining) (kahn graph)))
               (mv (not (tset::emptyp remaining))
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
  (implies (not (tset::in node remaining))
           (not (tset::in node (kahn-remaining remaining graph))))
  :induct t
  :enable kahn-remaining)

(defrulel member-equal-of-kahn-order
  (iff (member-equal node (kahn-order remaining graph))
       (and (tset::in node remaining)
            (not (tset::in node (kahn-remaining remaining graph)))))
  :induct (kahn-order remaining graph)
  :enable (kahn-order
           kahn-remaining))

(defrulel no-duplicatesp-equal-of-kahn-order
  (no-duplicatesp-equal (kahn-order remaining graph))
  :induct t
  :enable (kahn-order
           no-duplicatesp-equal))

(defrulel from-list-of-kahn-order
  (equal (tset::from-list (kahn-order remaining graph))
         (tset::diff remaining (kahn-remaining remaining graph)))
  :enable tset::extensionality-polar)

;; The remaining nodes include their own successors, so no remaining node
;; reaches the node removed, which is not one of their successors.

(defrulel reachable+p-sortedp-of-kahn-order
  (implies (tset::subset (successors-of-set remaining graph)
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
  (tset::subset (tset::from-list (mv-nth 1 (topological-sort graph)))
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
