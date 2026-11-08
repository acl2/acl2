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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The labels at a target are the labels of the edges to it, and a target is
;; present exactly when there is at least one such edge. A lookup may give an
;; absent target any empty default: treemap rewrites a default of
;; @('(treeset::empty)') to @('nil') once the target is known to be present.

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
  (implies (treeset::emptyp (double-rewrite default))
           (equal (treeset::emptyp (treemap::lookup to
                                                    (adjacency from graph)
                                                    :default default))
                  (not (treeset::in to (treemap::keys (adjacency from graph))))))
  :enable (adjacency
           break-abstraction
           treemap::lookup-with-default-becomes-lookup-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every target is a node.

(defrule subset-of-keys-of-adjacency-and-nodes
  (treeset::subset (treemap::keys (adjacency node graph))
                   (nodes graph))
  :enable (adjacency
           nodes
           break-abstraction))

(defrule in-of-nodes-when-in-of-keys-of-adjacency-forward-chaining
  (implies (treeset::in to (treemap::keys (adjacency from graph)))
           (treeset::in to (nodes graph)))
  :rule-classes :forward-chaining)

(defrule adjacency-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (adjacency node graph)
                  (treemap::empty)))
  :enable (adjacency
           nodes))
