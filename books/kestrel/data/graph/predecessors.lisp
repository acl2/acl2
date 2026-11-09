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

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "successors-defs")
(include-book "internal/predecessors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/predecessors"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors (node (graph graphp))
  :type-prescription :none
  :returns (predecessors treeset::setp)
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
  (equal (treeset::in from (predecessors to graph))
         (treeset::in to (successors from graph)))
  :enable (predecessors
           successors
           adjacency
           in-of-adj-list-predecessors)
  :disable keys-of-adjacency)

;; Every predecessor is a node, and a value which is not a node has none.

(defrule subset-of-predecessors-and-nodes
  (treeset::subset (predecessors node graph)
                   (nodes graph))
  :enable treeset::pick-a-point-polar)

(defruled predecessors-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (treeset::empty)))
  :enable treeset::extensionality-polar)

(defrule predecessors-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by predecessors-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors-of-set ((set treeset::setp) (graph graphp))
  :type-prescription :none
  :returns (predecessors treeset::setp)
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
  (if (treeset::emptyp set)
      (treeset::empty)
    (treeset::union (predecessors (treeset::min set) graph)
                    (predecessors-of-set (treeset::delete (treeset::min set)
                                                          set)
                                         graph)))
  :measure (treeset::cardinality set)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors-of-set-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
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
  (implies (treeset::in node set)
           (treeset::subset (predecessors node graph)
                            (predecessors-of-set set graph)))
  :induct (predecessors-of-set set graph)
  :enable predecessors-of-set)

(defrule subset-of-predecessors-of-set-and-nodes
  (treeset::subset (predecessors-of-set set graph)
                   (nodes graph))
  :induct t
  :enable predecessors-of-set)

(defrule monotonicity-of-predecessors-of-set
  (implies (treeset::subset x y)
           (treeset::subset (predecessors-of-set x graph)
                            (predecessors-of-set y graph)))
  :induct (predecessors-of-set x graph)
  :enable predecessors-of-set)

;; Inserting a node into a set adds its predecessors.

(defrulel subset-of-predecessors-when-in-of-insert
  (implies (treeset::in x (treeset::insert node set))
           (treeset::subset (predecessors x graph)
                            (treeset::union (predecessors node graph)
                                            (predecessors-of-set set graph)))))

(defruledl subset-of-predecessors-of-set-when-subset-of-insert
  (implies (treeset::subset x (treeset::insert node set))
           (treeset::subset (predecessors-of-set x graph)
                            (treeset::union (predecessors node graph)
                                            (predecessors-of-set set graph))))
  :induct (predecessors-of-set x graph)
  :enable predecessors-of-set
  :disable treeset::in-of-insert)

(defrule predecessors-of-set-of-insert
  (equal (predecessors-of-set (treeset::insert node set) graph)
         (treeset::union (predecessors node graph)
                         (predecessors-of-set set graph)))
  :use (:instance treeset::subset-antisymmetry
                  (x (predecessors-of-set (treeset::insert node set) graph))
                  (y (treeset::union (predecessors node graph)
                                     (predecessors-of-set set graph))))
  :enable subset-of-predecessors-of-set-when-subset-of-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expand nodes from a frontier until it runs out, and return the expanded
;; nodes. A node is expanded by adding its unexpanded predecessors to the
;; frontier.
;;
;; Each step either expands a new node, of which a graph has finitely many, or
;; drops a node from the frontier. A value which is not a node has no
;; predecessors, so expanding it also only shrinks the frontier.

(define predecessors+-search
  ((frontier treeset::setp)
   (expanded treeset::setp)
   (graph graphp))
  :returns (closure treeset::setp)
  :parents (predecessors+)
  (b* (((when (treeset::emptyp frontier))
        (treeset::fix expanded))
       (node (treeset::min frontier))
       (frontier (treeset::delete node frontier))
       ((when (treeset::in node expanded))
        (predecessors+-search frontier expanded graph))
       (expanded (treeset::insert node expanded)))
    (predecessors+-search (treeset::union
                            frontier
                            (treeset::diff (predecessors node graph)
                                           expanded))
                          expanded
                          graph))
  :measure (acl2::two-nats-measure
             (treeset::cardinality (treeset::diff (nodes graph) expanded))
             (treeset::cardinality frontier))
  :hints (("Goal" :in-theory (e/d (nfix
                                   treeset::cardinality-of-delete
                                   treeset::equal-of-cardinality-and-0-becomes-emptyp)
                                  (treeset::cardinality-of-diff)))))

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors+-search-when-equiv-of-arg1-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (predecessors+-search frontier0 expanded graph)
                  (predecessors+-search frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((predecessors+-search frontier0 expanded graph)
           (predecessors+-search frontier1 expanded graph)))

(defrule predecessors+-search-when-equiv-of-arg2-congruence
  (implies (treeset::equiv expanded0 expanded1)
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
  (implies (treeset::in x expanded)
           (treeset::in x (predecessors+-search frontier expanded graph)))
  :induct t
  :enable predecessors+-search)

(defrule in-of-predecessors+-search-when-in-of-arg1
  (implies (treeset::in x frontier)
           (treeset::in x (predecessors+-search frontier expanded graph)))
  :induct t
  :enable predecessors+-search)

;; One search step keeps every expanded or frontier node, and puts the
;; predecessors of the expanded node among them.

(defrulel subset-of-union-and-union-of-insert-and-union-of-delete
  (treeset::subset (treeset::union expanded frontier)
                   (treeset::union (treeset::insert node expanded)
                                   (treeset::union
                                     (treeset::delete node frontier)
                                     new)))
  :enable treeset::pick-a-point-polar)

(defrulel subset-of-arg1-and-union-of-insert-and-union-of-delete-of-diff
  (treeset::subset targets
                   (treeset::union (treeset::insert node expanded)
                                   (treeset::union
                                     frontier
                                     (treeset::delete
                                       node
                                       (treeset::diff targets expanded)))))
  :enable treeset::pick-a-point-polar)

;; So if the predecessors of the expanded nodes are expanded or in the
;; frontier, the search ends with a set containing the predecessors of its own
;; nodes.

(defrulel subset-of-predecessors-of-set-of-predecessors+-search
  (implies (treeset::subset (predecessors-of-set expanded graph)
                            (treeset::union expanded frontier))
           (treeset::subset
             (predecessors-of-set
               (predecessors+-search frontier expanded graph)
               graph)
             (predecessors+-search frontier expanded graph)))
  :induct t
  :enable (predecessors+-search
           treeset::union-of-arg1-and-delete-when-in-arg1-cheap)
  :disable (treeset::union-of-insert
            treeset::commutativity-of-union
            treeset::commutativity-2-of-union
            treeset::union-of-arg1-and-diff
            treeset::union-of-arg1-and-delete-when-not-in-arg1-cheap))

;; If the frontier and the expanded nodes are nodes, so is the result.

(defrulel subset-of-predecessors+-search-and-nodes
  (implies (and (treeset::subset frontier (nodes graph))
                (treeset::subset expanded (nodes graph)))
           (treeset::subset (predecessors+-search frontier expanded graph)
                            (nodes graph)))
  :induct t
  :enable predecessors+-search)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors+ (node (graph graphp))
  :type-prescription :none
  :returns (predecessors+ treeset::setp)
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
  (predecessors+-search (predecessors node graph) (treeset::empty) graph)
  :inline t)

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
  (treeset::subset (predecessors node graph)
                   (predecessors+ node graph))
  :enable (predecessors+
           treeset::pick-a-point-polar))

(defrule subset-of-predecessors-of-set-of-predecessors+-and-predecessors+
  (treeset::subset (predecessors-of-set (predecessors+ node graph) graph)
                   (predecessors+ node graph))
  :enable (predecessors+
           predecessors-of-set))

;; Every node reaching a node is a node, and a value which is not a node is
;; reached by none.

(defrule subset-of-predecessors+-and-nodes
  (treeset::subset (predecessors+ node graph)
                   (nodes graph))
  :enable predecessors+)

(defruled predecessors+-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors+ node graph)
                  (treeset::empty)))
  :enable (predecessors+
           predecessors+-search))

(defrule predecessors+-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors+ node graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by predecessors+-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy predecessors-extra-rules
  '(predecessors-when-not-in-of-nodes
    predecessors+-when-not-in-of-nodes))
