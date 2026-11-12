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
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")

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
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "adjacency"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/well-formed"))
(local (include-book "internal/edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors (node (graph graphp))
  :type-prescription :none
  :returns (successors tset::setp)
  :parents (graph)
  :short "The successors of a node of a @(see graph): the nodes with an edge
          from it."
  :long
  (xdoc::topstring-p
    "A value which is not a node has no successors. Time complexity:
     @($O(\\log(n) + d)$), where @($n$) is the number of nodes and @($d$) the
     number of successors.")
  (tmap::keys (adjacency node graph))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule successors-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (successors node graph0)
                  (successors node graph1)))
  :rule-classes :congruence
  :enable successors)

;; The successors of a node are the keys of its adjacency, which are written
;; as successors.

(defrule keys-of-adjacency
  (equal (tmap::keys (adjacency node graph))
         (successors node graph))
  :enable successors)

(theory-invariant (incompatible! (:definition successors$inline)
                                 (:rewrite keys-of-adjacency)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The labels from one node to another are nonempty exactly when the second
;; node is a successor of the first.

(defrule emptyp-of-labels
  (equal (tset::emptyp (labels from to graph))
         (not (tset::in to (successors from graph))))
  :enable (labels
           adjacency
           successors
           break-abstraction
           tmap::lookup-with-default-becomes-lookup-syntaxp)
  :disable (lookup-of-adjacency
            keys-of-adjacency))

;; The same fact read the other way.

(defruled in-of-successors-becomes-not-emptyp-of-labels
  (equal (tset::in to (successors from graph))
         (not (tset::emptyp (labels from to graph))))
  :enable not)

(theory-invariant
  (incompatible! (:rewrite emptyp-of-labels)
                 (:rewrite in-of-successors-becomes-not-emptyp-of-labels)))

;; So an edge leads to a successor of its source, and every successor has an
;; edge to it, for instance with the least of the labels.

(defrule in-of-successors-when-in-of-edges
  (implies (tset::in (edge from to label) (edges graph))
           (tset::in to (successors from graph)))
  :rule-classes (:rewrite :forward-chaining)
  :use (:instance tset::not-emptyp-when-in
                  (x label)
                  (set (labels from to graph))))

(defrule in-of-edge-of-min-of-labels-and-edges
  (equal (tset::in (edge from to (tset::min (labels from to graph)))
                   (edges graph))
         (tset::in to (successors from graph)))
  :use (:instance in-of-labels
                  (label (tset::min (labels from to graph))))
  :enable not
  :disable in-of-labels)

;; Every successor is a node.

(defrule subset-of-successors-and-nodes
  (tset::subset (successors node graph)
                (nodes graph))
  :enable (successors
           adjacency
           nodes
           break-abstraction)
  :disable keys-of-adjacency)

(defruled successors-when-not-in-of-nodes
  (implies (not (tset::in node (nodes graph)))
           (equal (successors node graph)
                  (tset::empty)))
  :enable successors
  :disable keys-of-adjacency)

(defrule successors-when-not-in-of-nodes-cheap
  (implies (not (tset::in node (nodes graph)))
           (equal (successors node graph)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by successors-when-not-in-of-nodes)

(defruled labels-when-not-in-of-successors
  (implies (not (tset::in to (successors from graph)))
           (equal (labels from to graph)
                  (tset::empty)))
  :enable (labels
           tmap::lookup-when-not-in-of-keys)
  :disable lookup-of-adjacency)

(defrule labels-when-not-in-of-successors-cheap
  (implies (not (tset::in to (successors from graph)))
           (equal (labels from to graph)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by labels-when-not-in-of-successors)

;; So both ends of a successor relationship are nodes.

(defrule in-of-nodes-when-in-of-successors-forward-chaining
  (implies (tset::in to (successors from graph))
           (and (tset::in from (nodes graph))
                (tset::in to (nodes graph))))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define adjacentp (from to (graph graphp))
  :type-prescription :none
  :parents (graph)
  :short "Check if there is an edge from one node of a @(see graph) to
          another."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n) + \\log(d))$), where @($n$) is the
       number of nodes and @($d$) the number of successors of @('from').")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(adjacentp from to graph)') becomes
       @('(tset::in to (successors from graph))'). Unlike that form, it
       does not construct the set of successors when executed."))
  (mbe :logic (tset::in to (successors from graph))
       :exec (tmap::in to (adjacency from graph)))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors-of-set ((set tset::setp) (graph graphp))
  :type-prescription :none
  :returns (successors tset::setp)
  :parents (graph)
  :short "The successors of the nodes in a set: the nodes with an edge from
          some node in the set."
  :long
  (xdoc::topstring-p
    "Values in the set which are not nodes have no successors. Time
     complexity: @($O((k + m)\\log(n))$), where @($k$) is the size of the
     set, @($m$) the number of pairs of nodes joined by an edge from a node in
     the set, and @($n$) the number of nodes.")
  (if (tset::emptyp set)
      (tset::empty)
    (tset::union (successors (tset::min set) graph)
                 (successors-of-set (tset::delete (tset::min set) set)
                                    graph)))
  :measure (tset::cardinality set)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule successors-of-set-when-equiv-of-arg1-congruence
  (implies (tset::equiv set0 set1)
           (equal (successors-of-set set0 graph)
                  (successors-of-set set1 graph)))
  :rule-classes :congruence
  :expand ((successors-of-set set0 graph)
           (successors-of-set set1 graph)))

(defrule successors-of-set-when-equiv-of-arg2-congruence
  (implies (equiv graph0 graph1)
           (equal (successors-of-set set graph0)
                  (successors-of-set set graph1)))
  :rule-classes :congruence
  :induct t
  :enable successors-of-set)

;; The empty set has no successors. The successors of each node in a set are
;; among the successors of the set, and every one of them is a node.

(defrule successors-of-set-of-empty
  (equal (successors-of-set (tset::empty) graph)
         (tset::empty))
  :enable successors-of-set)

(defrule subset-of-successors-and-successors-of-set-when-in
  (implies (tset::in node set)
           (tset::subset (successors node graph)
                         (successors-of-set set graph)))
  :induct (successors-of-set set graph)
  :enable successors-of-set)

(defrule subset-of-successors-of-set-and-nodes
  (tset::subset (successors-of-set set graph)
                (nodes graph))
  :induct t
  :enable successors-of-set)

(defrule monotonicity-of-successors-of-set
  (implies (tset::subset x y)
           (tset::subset (successors-of-set x graph)
                         (successors-of-set y graph)))
  :induct (successors-of-set x graph)
  :enable successors-of-set)

;; Inserting a node into a set adds its successors.

(defrulel subset-of-successors-when-in-of-insert
  (implies (tset::in x (tset::insert node set))
           (tset::subset (successors x graph)
                         (tset::union (successors node graph)
                                      (successors-of-set set graph)))))

(defruledl subset-of-successors-of-set-when-subset-of-insert
  (implies (tset::subset x (tset::insert node set))
           (tset::subset (successors-of-set x graph)
                         (tset::union (successors node graph)
                                      (successors-of-set set graph))))
  :induct (successors-of-set x graph)
  :enable successors-of-set
  :disable tset::in-of-insert)

(defrule successors-of-set-of-insert
  (equal (successors-of-set (tset::insert node set) graph)
         (tset::union (successors node graph)
                      (successors-of-set set graph)))
  :use (:instance tset::subset-antisymmetry
                  (x (successors-of-set (tset::insert node set) graph))
                  (y (tset::union (successors node graph)
                                  (successors-of-set set graph))))
  :enable subset-of-successors-of-set-when-subset-of-insert)

;; A set containing the successors of its own nodes still does after removing
;; a node which is not one of them.

(defrule subset-of-successors-of-set-of-delete-and-delete
  (implies (and (tset::subset (successors-of-set set graph) set)
                (not (tset::in node (successors-of-set set graph))))
           (tset::subset (successors-of-set (tset::delete node set)
                                            graph)
                         (tset::delete node set)))
  :enable tset::pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expand nodes from a frontier until it runs out, and return the expanded
;; nodes. A node is expanded by adding its unexpanded successors to the
;; frontier.
;;
;; Each step either expands a new node, of which a graph has finitely many, or
;; drops a node from the frontier. A value which is not a node has no
;; successors, so expanding it also only shrinks the frontier.

(define successors+-search
  ((frontier tset::setp)
   (expanded tset::setp)
   (graph graphp))
  :type-prescription :none
  :returns (closure tset::setp)
  :parents (successors+)
  :short "Expand nodes from a frontier, each at most once, and return the
          expanded nodes."
  (b* (((when (tset::emptyp frontier))
        (tset::fix expanded))
       (node (tset::min frontier))
       (frontier (tset::delete node frontier))
       ((when (tset::in node expanded))
        (successors+-search frontier expanded graph))
       (expanded (tset::insert node expanded)))
    (successors+-search (tset::union
                          frontier
                          (tset::diff (successors node graph)
                                      expanded))
                        expanded
                        graph))
  :measure (acl2::two-nats-measure
             (tset::cardinality (tset::diff (nodes graph) expanded))
             (tset::cardinality frontier))
  :hints (("Goal" :in-theory (e/d (nfix
                                   tset::cardinality-of-delete
                                   tset::equal-of-cardinality-and-0-becomes-emptyp)
                                  (tset::cardinality-of-diff)))))

;;;;;;;;;;;;;;;;;;;;

(defrule successors+-search-when-equiv-of-arg1-congruence
  (implies (tset::equiv frontier0 frontier1)
           (equal (successors+-search frontier0 expanded graph)
                  (successors+-search frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((successors+-search frontier0 expanded graph)
           (successors+-search frontier1 expanded graph)))

(defrule successors+-search-when-equiv-of-arg2-congruence
  (implies (tset::equiv expanded0 expanded1)
           (equal (successors+-search frontier expanded0 graph)
                  (successors+-search frontier expanded1 graph)))
  :rule-classes :congruence
  :induct t
  :enable successors+-search)

(defrule successors+-search-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (successors+-search frontier expanded graph0)
                  (successors+-search frontier expanded graph1)))
  :rule-classes :congruence
  :induct t
  :enable successors+-search)

;; The frontier and the expanded nodes are all eventually expanded.

(defrule in-of-successors+-search-when-in-of-arg2
  (implies (tset::in x expanded)
           (tset::in x (successors+-search frontier expanded graph)))
  :induct t
  :enable successors+-search)

(defrule in-of-successors+-search-when-in-of-arg1
  (implies (tset::in x frontier)
           (tset::in x (successors+-search frontier expanded graph)))
  :induct t
  :enable successors+-search)

;; One search step keeps every expanded or frontier node, and puts the
;; successors of the expanded node among them.

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

;; So if the successors of the expanded nodes are expanded or in the frontier,
;; the search ends with a set containing the successors of its own nodes.

(defrulel subset-of-successors-of-set-of-successors+-search
  (implies (tset::subset (successors-of-set expanded graph)
                         (tset::union expanded frontier))
           (tset::subset
             (successors-of-set (successors+-search frontier expanded graph)
                                graph)
             (successors+-search frontier expanded graph)))
  :induct t
  :enable (successors+-search
           tset::union-of-arg1-and-delete-when-in-arg1-cheap)
  :disable (tset::union-of-insert
            tset::commutativity-of-union
            tset::commutativity-2-of-union
            tset::union-of-arg1-and-diff
            tset::union-of-arg1-and-delete-when-not-in-arg1-cheap))

;; If the frontier and the expanded nodes are nodes, so is the result.

(defrulel subset-of-successors+-search-and-nodes
  (implies (and (tset::subset frontier (nodes graph))
                (tset::subset expanded (nodes graph)))
           (tset::subset (successors+-search frontier expanded graph)
                         (nodes graph)))
  :induct t
  :enable successors+-search)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors+ (node (graph graphp))
  :type-prescription :none
  :returns (successors+ tset::setp)
  :parents (graph)
  :short "The nodes reachable from a node of a @(see graph) by a walk of at
          least one step."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the transitive closure of @(tsee successors), without the
       reflexive closure: a node is among its own @('successors+') only if it
       is on a cycle. Membership is @(tsee reachable+p), by the rule
       @('in-of-successors+').")
    (xdoc::p
      "The search expands each node at most once. Time complexity:
       @($O((n + m)\\log(n))$), where @($n$) is the number of nodes and @($m$)
       the number of pairs of nodes joined by an edge."))
  (successors+-search (successors node graph) (tset::empty) graph))

;;;;;;;;;;;;;;;;;;;;

(defrule successors+-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (successors+ node graph0)
                  (successors+ node graph1)))
  :rule-classes :congruence
  :enable successors+)

;; The successors of a node are among the nodes reachable from it, and so are
;; the successors of each of those.

(defrule subset-of-successors-and-successors+
  (tset::subset (successors node graph)
                (successors+ node graph))
  :enable (successors+
           tset::pick-a-point-polar))

(defrule subset-of-successors-of-set-of-successors+-and-successors+
  (tset::subset (successors-of-set (successors+ node graph) graph)
                (successors+ node graph))
  :enable (successors+
           successors-of-set))

;; Every node reachable from a node is a node, and a value which is not a node
;; reaches none.

(defrule subset-of-successors+-and-nodes
  (tset::subset (successors+ node graph)
                (nodes graph))
  :enable successors+)

(defruled successors+-when-not-in-of-nodes
  (implies (not (tset::in node (nodes graph)))
           (equal (successors+ node graph)
                  (tset::empty)))
  :enable (successors+
           successors+-search))

(defrule successors+-when-not-in-of-nodes-cheap
  (implies (not (tset::in node (nodes graph)))
           (equal (successors+ node graph)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by successors+-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy successors-extra-rules
  '(successors-when-not-in-of-nodes
    labels-when-not-in-of-successors
    successors+-when-not-in-of-nodes
    ))
