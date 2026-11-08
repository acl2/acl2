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
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/well-formed"))
(local (include-book "internal/edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define adjacency (node (graph graphp))
  :type-prescription :none
  :returns (adj treemap::mapp
                :hints (("Goal" :in-theory (enable* break-abstraction))))
  :parents (graph)
  :short "The targets of the edges out of a node of a @(see graph), with their
          labels."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is a "
      (xdoc::seetopic "acl2::treemap" "treemap")
      " from each target of an edge out of the node to the nonempty "
      (xdoc::seetopic "acl2::treeset" "treeset")
      " of labels on the edges to it. The graph stores this map for each node,
       so it is returned without being constructed. A value which is not a
       node has the empty map, as does a node with no outgoing edges.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$), where @($n$) is the number of
       nodes."))
  (treemap::lookup node (fix graph) :default (treemap::empty))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (adjacency node graph0)
                  (adjacency node graph1)))
  :rule-classes :congruence
  :enable adjacency)

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

;; The labels at a target are the labels of the edges to it, and a target is
;; present exactly when it is a successor. A lookup may give an absent target
;; any empty default: treemap rewrites a default of @('(treeset::empty)') to
;; @('nil') once the target is known to be present.

(defrule in-of-lookup-of-adjacency
  (implies (treeset::emptyp (double-rewrite default))
           (equal (treeset::in label
                               (treemap::lookup to
                                                (adjacency from graph)
                                                :default default))
                  (treeset::in (edge from to label) (edges graph))))
  :enable (adjacency
           edges
           in-of-adj-list-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

(defrule setp-of-lookup-of-adjacency
  (implies (treeset::setp default)
           (treeset::setp (treemap::lookup to
                                           (adjacency from graph)
                                           :default default)))
  :enable (adjacency
           break-abstraction
           treemap::lookup-with-default-becomes-lookup-syntaxp))

(defrule emptyp-of-lookup-of-adjacency
  (equal (treeset::emptyp (treemap::lookup to
                                           (adjacency from graph)
                                           :default default))
         (and (not (treeset::in to (successors from graph)))
              (treeset::emptyp (double-rewrite default))))
  :enable (adjacency
           successors
           break-abstraction)
  :disable keys-of-adjacency)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An edge leads to a successor of its source, and every successor is a node.

(defrule in-of-successors-when-in-of-edges
  (implies (treeset::in (edge from to label) (edges graph))
           (treeset::in to (successors from graph)))
  :rule-classes (:rewrite :forward-chaining)
  :use ((:instance in-of-lookup-of-adjacency (default nil))
        (:instance treeset::not-emptyp-when-in
                   (x label)
                   (set (treemap::lookup to (adjacency from graph)))))
  :disable in-of-lookup-of-adjacency)

(defrule subset-of-successors-and-nodes
  (treeset::subset (successors node graph)
                   (nodes graph))
  :enable (successors
           adjacency
           nodes
           break-abstraction)
  :disable keys-of-adjacency)

(defrule in-of-nodes-when-in-of-successors-forward-chaining
  (implies (treeset::in to (successors from graph))
           (treeset::in to (nodes graph)))
  :rule-classes :forward-chaining)

(defruled adjacency-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (adjacency node graph)
                  (treemap::empty)))
  :enable (adjacency
           nodes))

(defrule adjacency-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (adjacency node graph)
                  (treemap::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by adjacency-when-not-in-of-nodes)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define adjacency! (node (graph graphp))
  :guard (node-in node graph)
  :parents (adjacency)
  :short "The targets of the edges out of a node of a @(see graph), with their
          labels, for a node known to be in the graph."
  :long
  (xdoc::topstring
    (xdoc::p
      "Logically this is @(tsee adjacency), to which it is rewritten. The
       guard lets it skip the check for a missing node.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$), where @($n$) is the number of
       nodes."))
  (mbe :logic (adjacency node graph)
       :exec (treemap::lookup! node graph))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* adjacency
                                            nodes
                                            break-abstraction))))
