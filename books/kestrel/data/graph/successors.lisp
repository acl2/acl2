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
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")

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
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

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
  :returns (successors treeset::setp)
  :parents (graph)
  :short "The successors of a node of a @(see graph): the nodes with an edge
          from it."
  :long
  (xdoc::topstring-p
    "A value which is not a node has no successors. Time complexity:
     @($O(\\log(n) + d)$), where @($n$) is the number of nodes and @($d$) the
     number of successors.")
  (treemap::keys (adjacency node graph))
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
  (equal (treemap::keys (adjacency node graph))
         (successors node graph))
  :enable successors)

(theory-invariant (incompatible! (:definition successors$inline)
                                 (:rewrite keys-of-adjacency)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The labels from one node to another are nonempty exactly when the second
;; node is a successor of the first.

(defrule emptyp-of-labels
  (equal (treeset::emptyp (labels from to graph))
         (not (treeset::in to (successors from graph))))
  :enable (labels
           adjacency
           successors
           break-abstraction
           treemap::lookup-with-default-becomes-lookup-syntaxp)
  :disable (lookup-of-adjacency
            keys-of-adjacency))

;; The same fact read the other way.

(defruled in-of-successors-becomes-not-emptyp-of-labels
  (equal (treeset::in to (successors from graph))
         (not (treeset::emptyp (labels from to graph))))
  :enable not)

(theory-invariant
  (incompatible! (:rewrite emptyp-of-labels)
                 (:rewrite in-of-successors-becomes-not-emptyp-of-labels)))

;; So an edge leads to a successor of its source, and every successor has an
;; edge to it, for instance with the least of the labels.

(defrule in-of-successors-when-in-of-edges
  (implies (treeset::in (edge from to label) (edges graph))
           (treeset::in to (successors from graph)))
  :rule-classes (:rewrite :forward-chaining)
  :use (:instance treeset::not-emptyp-when-in
                  (x label)
                  (set (labels from to graph))))

(defrule in-of-edge-of-min-of-labels-and-edges
  (equal (treeset::in (edge from to (treeset::min (labels from to graph)))
                      (edges graph))
         (treeset::in to (successors from graph)))
  :use (:instance in-of-labels
                  (label (treeset::min (labels from to graph))))
  :enable not
  :disable in-of-labels)

;; Every successor is a node.

(defrule subset-of-successors-and-nodes
  (treeset::subset (successors node graph)
                   (nodes graph))
  :enable (successors
           adjacency
           nodes
           break-abstraction)
  :disable keys-of-adjacency)

(defruled successors-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (successors node graph)
                  (treeset::empty)))
  :enable successors
  :disable keys-of-adjacency)

(defrule successors-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (successors node graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by successors-when-not-in-of-nodes)

(defruled labels-when-not-in-of-successors
  (implies (not (treeset::in to (successors from graph)))
           (equal (labels from to graph)
                  (treeset::empty)))
  :enable (labels
           treemap::lookup-when-not-in-of-keys)
  :disable lookup-of-adjacency)

(defrule labels-when-not-in-of-successors-cheap
  (implies (not (treeset::in to (successors from graph)))
           (equal (labels from to graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by labels-when-not-in-of-successors)

;; So both ends of a successor relationship are nodes.

(defrule in-of-nodes-when-in-of-successors-forward-chaining
  (implies (treeset::in to (successors from graph))
           (and (treeset::in from (nodes graph))
                (treeset::in to (nodes graph))))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define adjacentp (from to (graph graphp))
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
       @('(treeset::in to (successors from graph))'). Unlike that form, it
       does not construct the set of successors when executed."))
  (mbe :logic (treeset::in to (successors from graph))
       :exec (treemap::in to (adjacency from graph)))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors-of-set ((set treeset::setp) (graph graphp))
  :type-prescription :none
  :returns (successors treeset::setp)
  :parents (graph)
  :short "The successors of the nodes in a set: the nodes with an edge from
          some node in the set."
  :long
  (xdoc::topstring-p
    "Values in the set which are not nodes have no successors. Time
     complexity: @($O((k + m)\\log(n))$), where @($k$) is the size of the
     set, @($m$) the number of pairs of nodes joined by an edge from a node in
     the set, and @($n$) the number of nodes.")
  (if (treeset::emptyp set)
      (treeset::empty)
    (treeset::union (successors (treeset::min set) graph)
                    (successors-of-set (treeset::delete (treeset::min set) set)
                                       graph)))
  :measure (treeset::cardinality set)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule successors-of-set-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
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
  (equal (successors-of-set (treeset::empty) graph)
         (treeset::empty))
  :enable successors-of-set)

(defrule subset-of-successors-and-successors-of-set-when-in
  (implies (treeset::in node set)
           (treeset::subset (successors node graph)
                            (successors-of-set set graph)))
  :induct (successors-of-set set graph)
  :enable successors-of-set)

(defrule subset-of-successors-of-set-and-nodes
  (treeset::subset (successors-of-set set graph)
                   (nodes graph))
  :induct t
  :enable successors-of-set)

(defrule monotonicity-of-successors-of-set
  (implies (treeset::subset x y)
           (treeset::subset (successors-of-set x graph)
                            (successors-of-set y graph)))
  :induct (successors-of-set x graph)
  :enable successors-of-set)

;; Inserting a node into a set adds its successors.

(defrulel subset-of-successors-when-in-of-insert
  (implies (treeset::in x (treeset::insert node set))
           (treeset::subset (successors x graph)
                            (treeset::union (successors node graph)
                                            (successors-of-set set graph)))))

(defruledl subset-of-successors-of-set-when-subset-of-insert
  (implies (treeset::subset x (treeset::insert node set))
           (treeset::subset (successors-of-set x graph)
                            (treeset::union (successors node graph)
                                            (successors-of-set set graph))))
  :induct (successors-of-set x graph)
  :enable successors-of-set
  :disable treeset::in-of-insert)

(defrule successors-of-set-of-insert
  (equal (successors-of-set (treeset::insert node set) graph)
         (treeset::union (successors node graph)
                         (successors-of-set set graph)))
  :use (:instance treeset::subset-antisymmetry
                  (x (successors-of-set (treeset::insert node set) graph))
                  (y (treeset::union (successors node graph)
                                     (successors-of-set set graph))))
  :enable subset-of-successors-of-set-when-subset-of-insert)

;; A set containing the successors of its own nodes still does after removing
;; a node which is not one of them.

(defrule subset-of-successors-of-set-of-delete-and-delete
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (not (treeset::in node (successors-of-set set graph))))
           (treeset::subset (successors-of-set (treeset::delete node set)
                                               graph)
                            (treeset::delete node set)))
  :enable treeset::pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expand nodes from a frontier until it runs out, and return the expanded
;; nodes. A node is expanded by adding its unexpanded successors to the
;; frontier.
;;
;; Each step either expands a new node, of which a graph has finitely many, or
;; drops a node from the frontier. A value which is not a node has no
;; successors, so expanding it also only shrinks the frontier.

(define successors+-search
  ((frontier treeset::setp)
   (expanded treeset::setp)
   (graph graphp))
  :returns (closure treeset::setp)
  :parents (successors+)
  (b* (((when (treeset::emptyp frontier))
        (treeset::fix expanded))
       (node (treeset::min frontier))
       (frontier (treeset::delete node frontier))
       ((when (treeset::in node expanded))
        (successors+-search frontier expanded graph))
       (expanded (treeset::insert node expanded)))
    (successors+-search (treeset::union
                          frontier
                          (treeset::diff (successors node graph)
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

(defrule successors+-search-when-equiv-of-arg1-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (successors+-search frontier0 expanded graph)
                  (successors+-search frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((successors+-search frontier0 expanded graph)
           (successors+-search frontier1 expanded graph)))

(defrule successors+-search-when-equiv-of-arg2-congruence
  (implies (treeset::equiv expanded0 expanded1)
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
  (implies (treeset::in x expanded)
           (treeset::in x (successors+-search frontier expanded graph)))
  :induct t
  :enable successors+-search)

(defrule in-of-successors+-search-when-in-of-arg1
  (implies (treeset::in x frontier)
           (treeset::in x (successors+-search frontier expanded graph)))
  :induct t
  :enable successors+-search)

;; One search step keeps every expanded or frontier node, and puts the
;; successors of the expanded node among them.

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

;; So if the successors of the expanded nodes are expanded or in the frontier,
;; the search ends with a set containing the successors of its own nodes.

(defrulel subset-of-successors-of-set-of-successors+-search
  (implies (treeset::subset (successors-of-set expanded graph)
                            (treeset::union expanded frontier))
           (treeset::subset
             (successors-of-set (successors+-search frontier expanded graph)
                                graph)
             (successors+-search frontier expanded graph)))
  :induct t
  :enable (successors+-search
           treeset::union-of-arg1-and-delete-when-in-arg1-cheap)
  :disable (treeset::union-of-insert
            treeset::commutativity-of-union
            treeset::commutativity-2-of-union
            treeset::union-of-arg1-and-diff
            treeset::union-of-arg1-and-delete-when-not-in-arg1-cheap))

;; If the frontier and the expanded nodes are nodes, so is the result.

(defrulel subset-of-successors+-search-and-nodes
  (implies (and (treeset::subset frontier (nodes graph))
                (treeset::subset expanded (nodes graph)))
           (treeset::subset (successors+-search frontier expanded graph)
                            (nodes graph)))
  :induct t
  :enable successors+-search)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors+ (node (graph graphp))
  :type-prescription :none
  :returns (successors+ treeset::setp)
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
  (successors+-search (successors node graph) (treeset::empty) graph))

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
  (treeset::subset (successors node graph)
                   (successors+ node graph))
  :enable (successors+
           treeset::pick-a-point-polar))

(defrule subset-of-successors-of-set-of-successors+-and-successors+
  (treeset::subset (successors-of-set (successors+ node graph) graph)
                   (successors+ node graph))
  :enable (successors+
           successors-of-set))

;; Every node reachable from a node is a node, and a value which is not a node
;; reaches none.

(defrule subset-of-successors+-and-nodes
  (treeset::subset (successors+ node graph)
                   (nodes graph))
  :enable successors+)

(defruled successors+-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (successors+ node graph)
                  (treeset::empty)))
  :enable (successors+
           successors+-search))

(defrule successors+-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (successors+ node graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by successors+-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy successors-extra-rules
  '(successors-when-not-in-of-nodes
    labels-when-not-in-of-successors
    successors+-when-not-in-of-nodes
    ))
