; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/union-defs" :dir :system)
(include-book "kestrel/data/tset/intersect-defs" :dir :system)
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "successors-defs")
(include-book "internal/predecessors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/predecessors"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors (node (graph graphp))
  :type-prescription :none
  :returns (predecessors tset::setp)
  :parents (graph)
  :short "The predecessors of a node of a @(see graph): the nodes with an edge
          to it."
  :long
  (xdoc::topstring
    (xdoc::p
      "A graph records only each node's outgoing edges, so finding the
       predecessors of a node means visiting every node. A value which is not
       a node has no predecessors.")
    (xdoc::p
      "Time complexity: @($O(n(\\log(n) + \\log(d)) + k\\log(k))$), where
       @($n$) is the number of nodes, @($d$) the largest number of successors
       of a node, and @($k$) the number of predecessors. This is not optimal:
       each step takes and deletes the least remaining node, where a traversal
       with an iterator would avoid the deletions."))
  (adj-list-predecessors node (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (predecessors node graph0)
                  (predecessors node graph1)))
  :rule-classes :congruence
  :enable predecessors)

;; A node is a predecessor of another exactly when the other is one of its
;; successors.

(defrule in-of-predecessors
  (equal (tset::in from (predecessors to graph))
         (tset::in to (successors from graph)))
  :enable (predecessors
           successors
           adjacency
           in-of-adj-list-predecessors)
  :disable keys-of-adjacency)

;; Every predecessor is a node, and a value which is not a node has none.

(defrule subset-of-predecessors-and-nodes
  (tset::subset (predecessors node graph)
                (nodes graph))
  :enable tset::pick-a-point-polar)

(defruled predecessors-when-not-in-of-nodes
  (implies (not (tset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (tset::empty)))
  :enable tset::extensionality-polar)

(defrule predecessors-when-not-in-of-nodes-cheap
  (implies (not (tset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by predecessors-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors-of-set ((set tset::setp) (graph graphp))
  :type-prescription :none
  :returns (predecessors tset::setp)
  :parents (graph)
  :short "The predecessors of the nodes in a set: the nodes with an edge to
          some node in the set."
  :long
  (xdoc::topstring-p
    "Values in the set which are not nodes have no predecessors. Time
     complexity: @($O(k\\,n(\\log(n) + \\log(d)) + m\\log(n))$), where
     @($k$) is the size of the set, @($n$) the number of nodes, @($d$) the
     largest number of successors of a node, and @($m$) the number of pairs
     of nodes joined by an edge to a node in the set. Like @(tsee
     predecessors), this is not optimal.")
  (if (tset::emptyp set)
      (tset::empty)
    (tset::union (predecessors (tset::min set) graph)
                 (predecessors-of-set (tset::delete (tset::min set)
                                                    set)
                                      graph)))
  :measure (tset::cardinality set)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors-of-set-when-equiv-of-arg1-congruence
  (implies (tset::equiv set0 set1)
           (equal (predecessors-of-set set0 graph)
                  (predecessors-of-set set1 graph)))
  :rule-classes :congruence
  :expand ((predecessors-of-set set0 graph)
           (predecessors-of-set set1 graph)))

(defrule predecessors-of-set-when-equiv-of-arg2-congruence
  (implies (equiv graph0 graph1)
           (equal (predecessors-of-set set graph0)
                  (predecessors-of-set set graph1)))
  :rule-classes :congruence
  :induct t
  :enable predecessors-of-set)

;; The predecessors of each node in the set are among them, and every one of
;; them is a node.

(defrule subset-of-predecessors-and-predecessors-of-set-when-in
  (implies (tset::in node set)
           (tset::subset (predecessors node graph)
                         (predecessors-of-set set graph)))
  :induct (predecessors-of-set set graph)
  :enable predecessors-of-set)

(defrule subset-of-predecessors-of-set-and-nodes
  (tset::subset (predecessors-of-set set graph)
                (nodes graph))
  :induct t
  :enable predecessors-of-set)

(defrule monotonicity-of-predecessors-of-set
  (implies (tset::subset x y)
           (tset::subset (predecessors-of-set x graph)
                         (predecessors-of-set y graph)))
  :induct (predecessors-of-set x graph)
  :enable predecessors-of-set)

;; Inserting a node into a set adds its predecessors.

(defrulel subset-of-predecessors-when-in-of-insert
  (implies (tset::in x (tset::insert node set))
           (tset::subset (predecessors x graph)
                         (tset::union (predecessors node graph)
                                      (predecessors-of-set set graph)))))

(defruledl subset-of-predecessors-of-set-when-subset-of-insert
  (implies (tset::subset x (tset::insert node set))
           (tset::subset (predecessors-of-set x graph)
                         (tset::union (predecessors node graph)
                                      (predecessors-of-set set graph))))
  :induct (predecessors-of-set x graph)
  :enable predecessors-of-set
  :disable tset::in-of-insert)

(defrule predecessors-of-set-of-insert
  (equal (predecessors-of-set (tset::insert node set) graph)
         (tset::union (predecessors node graph)
                      (predecessors-of-set set graph)))
  :use (:instance tset::subset-antisymmetry
                  (x (predecessors-of-set (tset::insert node set) graph))
                  (y (tset::union (predecessors node graph)
                                  (predecessors-of-set set graph))))
  :enable subset-of-predecessors-of-set-when-subset-of-insert)

;; A node is a successor of a set exactly when one of its predecessors is in
;; the set, and a predecessor of a set exactly when one of its successors is.

(defrule emptyp-of-intersect-and-predecessors-when-in-of-successors
  (implies (and (tset::in node (successors pred graph))
                (tset::in pred set))
           (not (tset::emptyp
                  (tset::intersect set (predecessors node graph)))))
  :use (:instance tset::not-emptyp-when-in
                  (tset::x pred)
                  (tset::set (tset::intersect
                               set
                               (predecessors node graph)))))

(defruledl not-emptyp-of-intersect-and-predecessors-when-in-of-successors-of-set
  (implies (tset::in node (successors-of-set set graph))
           (not (tset::emptyp
                  (tset::intersect set (predecessors node graph)))))
  :induct (successors-of-set set graph)
  :enable successors-of-set)

(defruledl in-of-successors-of-set-when-in-of-predecessors
  (implies (and (tset::in pred (predecessors node graph))
                (tset::in pred set))
           (tset::in node (successors-of-set set graph))))

(defruledl in-of-successors-of-set-when-not-emptyp-of-intersect
  (implies (not (tset::emptyp
                  (tset::intersect set (predecessors node graph))))
           (tset::in node (successors-of-set set graph)))
  :use (:instance in-of-successors-of-set-when-in-of-predecessors
                  (pred (tset::min (tset::intersect
                                     set
                                     (predecessors node graph)))))
  :disable in-of-predecessors)

(defruled in-of-successors-of-set-becomes-not-emptyp-of-intersect
  (equal (tset::in node (successors-of-set set graph))
         (not (tset::emptyp
                (tset::intersect set (predecessors node graph)))))
  :use (not-emptyp-of-intersect-and-predecessors-when-in-of-successors-of-set
        in-of-successors-of-set-when-not-emptyp-of-intersect))

(defrulel emptyp-of-intersect-and-successors-when-in-of-successors
  (implies (and (tset::in succ (successors node graph))
                (tset::in succ set))
           (not (tset::emptyp
                  (tset::intersect set (successors node graph)))))
  :use (:instance tset::not-emptyp-when-in
                  (tset::x succ)
                  (tset::set (tset::intersect
                               set
                               (successors node graph)))))

(defruledl not-emptyp-of-intersect-and-successors-when-in-of-predecessors-of-set
  (implies (tset::in node (predecessors-of-set set graph))
           (not (tset::emptyp
                  (tset::intersect set (successors node graph)))))
  :induct (predecessors-of-set set graph)
  :enable predecessors-of-set)

(defruledl in-of-predecessors-of-set-when-in-of-successors
  (implies (and (tset::in succ (successors node graph))
                (tset::in succ set))
           (tset::in node (predecessors-of-set set graph)))
  :use (:instance tset::in-when-in-and-subset
                  (tset::a node)
                  (tset::x (predecessors succ graph))
                  (tset::y (predecessors-of-set set graph)))
  :disable tset::in-when-in-and-subset)

(defruledl in-of-predecessors-of-set-when-not-emptyp-of-intersect
  (implies (not (tset::emptyp
                  (tset::intersect set (successors node graph))))
           (tset::in node (predecessors-of-set set graph)))
  :use (:instance in-of-predecessors-of-set-when-in-of-successors
                  (succ (tset::min (tset::intersect
                                     set
                                     (successors node graph))))))

(defruled in-of-predecessors-of-set-becomes-not-emptyp-of-intersect
  (equal (tset::in node (predecessors-of-set set graph))
         (not (tset::emptyp
                (tset::intersect set (successors node graph)))))
  :use (not-emptyp-of-intersect-and-successors-when-in-of-predecessors-of-set
        in-of-predecessors-of-set-when-not-emptyp-of-intersect))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expand nodes from a frontier until it runs out, and return the expanded
;; nodes. A node is expanded by adding its unexpanded predecessors to the
;; frontier.
;;
;; Each step either expands a new node, of which a graph has finitely many, or
;; drops a node from the frontier. A value which is not a node has no
;; predecessors, so expanding it also only shrinks the frontier.

(define predecessors+-search
  ((frontier tset::setp)
   (expanded tset::setp)
   (graph graphp))
  :type-prescription :none
  :returns (closure tset::setp)
  :parents (predecessors+)
  :short "Expand nodes from a frontier, each at most once, adding a node's
          predecessors, and return the expanded nodes."
  (b* (((when (tset::emptyp frontier))
        (tset::fix expanded))
       (node (tset::min frontier))
       (frontier (tset::delete node frontier))
       ((when (tset::in node expanded))
        (predecessors+-search frontier expanded graph))
       (expanded (tset::insert node expanded)))
    (predecessors+-search (tset::union
                            frontier
                            (tset::diff (predecessors node graph)
                                        expanded))
                          expanded
                          graph))
  :measure (acl2::two-nats-measure
             (tset::cardinality (tset::diff (nodes graph) expanded))
             (tset::cardinality frontier))
  :hints (("Goal" :in-theory (e/d (nfix
                                   acl2::fix
                                   tset::cardinality-of-delete
                                   tset::equal-of-cardinality-and-0-becomes-emptyp)
                                  (tset::cardinality-of-diff)))))

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors+-search-when-equiv-of-arg1-congruence
  (implies (tset::equiv frontier0 frontier1)
           (equal (predecessors+-search frontier0 expanded graph)
                  (predecessors+-search frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((predecessors+-search frontier0 expanded graph)
           (predecessors+-search frontier1 expanded graph)))

(defrule predecessors+-search-when-equiv-of-arg2-congruence
  (implies (tset::equiv expanded0 expanded1)
           (equal (predecessors+-search frontier expanded0 graph)
                  (predecessors+-search frontier expanded1 graph)))
  :rule-classes :congruence
  :induct t
  :enable predecessors+-search)

(defrule predecessors+-search-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (predecessors+-search frontier expanded graph0)
                  (predecessors+-search frontier expanded graph1)))
  :rule-classes :congruence
  :induct t
  :enable predecessors+-search)

;; The frontier and the expanded nodes are all eventually expanded.

(defrule in-of-predecessors+-search-when-in-of-arg2
  (implies (tset::in x expanded)
           (tset::in x (predecessors+-search frontier expanded graph)))
  :induct t
  :enable predecessors+-search)

(defrule in-of-predecessors+-search-when-in-of-arg1
  (implies (tset::in x frontier)
           (tset::in x (predecessors+-search frontier expanded graph)))
  :induct t
  :enable predecessors+-search)

;; One search step keeps every expanded or frontier node, and puts the
;; predecessors of the expanded node among them.

(defrulel subset-of-union-and-union-of-insert-and-union-of-delete
  (tset::subset (tset::union expanded frontier)
                (tset::union (tset::insert node expanded)
                             (tset::union
                               (tset::delete node frontier)
                               new)))
  :enable tset::pick-a-point-polar)

(defrulel subset-of-arg1-and-union-of-insert-and-union-of-delete-of-diff
  (tset::subset targets
                (tset::union (tset::insert node expanded)
                             (tset::union
                               frontier
                               (tset::delete
                                 node
                                 (tset::diff targets expanded)))))
  :enable tset::pick-a-point-polar)

;; So if the predecessors of the expanded nodes are expanded or in the
;; frontier, the search ends with a set containing the predecessors of its own
;; nodes.

(defrulel subset-of-predecessors-of-set-of-predecessors+-search
  (implies (tset::subset (predecessors-of-set expanded graph)
                         (tset::union expanded frontier))
           (tset::subset
             (predecessors-of-set
               (predecessors+-search frontier expanded graph)
               graph)
             (predecessors+-search frontier expanded graph)))
  :induct t
  :enable (predecessors+-search
           tset::union-of-arg1-and-delete-when-in-arg1-cheap)
  :disable (tset::union-of-insert
            tset::commutativity-of-union
            tset::commutativity-2-of-union
            tset::union-of-arg1-and-diff
            tset::union-of-arg1-and-delete-when-not-in-arg1-cheap))

;; If the frontier and the expanded nodes are nodes, so is the result.

(defrulel subset-of-predecessors+-search-and-nodes
  (implies (and (tset::subset frontier (nodes graph))
                (tset::subset expanded (nodes graph)))
           (tset::subset (predecessors+-search frontier expanded graph)
                         (nodes graph)))
  :induct t
  :enable predecessors+-search)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors+ (node (graph graphp))
  :type-prescription :none
  :returns (predecessors+ tset::setp)
  :parents (graph)
  :short "The nodes from which a node of a @(see graph) is reachable by a walk
          of at least one step."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the transitive closure of @(tsee predecessors), without the
       reflexive closure: a node is among its own @('predecessors+') only if
       it is on a cycle. Membership is @(tsee reachable+p), by the rule
       @('in-of-predecessors+').")
    (xdoc::p
      "The search expands each node at most once, finding its predecessors
       with @(tsee predecessors). Time complexity: @($O(n^2\\log(n))$), where
       @($n$) is the number of nodes. This is not optimal, since each
       expansion visits every node."))
  (predecessors+-search (predecessors node graph) (tset::empty) graph))

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors+-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (predecessors+ node graph0)
                  (predecessors+ node graph1)))
  :rule-classes :congruence
  :enable predecessors+)

;; The predecessors of a node are among the nodes reaching it, and so are the
;; predecessors of each of those.

(defrule subset-of-predecessors-and-predecessors+
  (tset::subset (predecessors node graph)
                (predecessors+ node graph))
  :enable (predecessors+
           tset::pick-a-point-polar))

(defrule subset-of-predecessors-of-set-of-predecessors+-and-predecessors+
  (tset::subset (predecessors-of-set (predecessors+ node graph) graph)
                (predecessors+ node graph))
  :enable (predecessors+
           predecessors-of-set))

;; Every node reaching a node is a node, and a value which is not a node is
;; reached by none.

(defrule subset-of-predecessors+-and-nodes
  (tset::subset (predecessors+ node graph)
                (nodes graph))
  :enable predecessors+)

(defruled predecessors+-when-not-in-of-nodes
  (implies (not (tset::in node (nodes graph)))
           (equal (predecessors+ node graph)
                  (tset::empty)))
  :enable (predecessors+
           predecessors+-search))

(defrule predecessors+-when-not-in-of-nodes-cheap
  (implies (not (tset::in node (nodes graph)))
           (equal (predecessors+ node graph)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by predecessors+-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy predecessors-extra-rules
  '(predecessors-when-not-in-of-nodes
    predecessors+-when-not-in-of-nodes))
