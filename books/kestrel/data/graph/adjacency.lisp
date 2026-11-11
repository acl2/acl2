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
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define labels (from to (graph graphp))
  :type-prescription :none
  :returns (labels treeset::setp
                   :hints (("Goal" :in-theory (enable* adjacency
                                                       break-abstraction))))
  :parents (graph)
  :short "The labels of the edges from one node of a @(see graph) to
          another."
  :long
  (xdoc::topstring-p
    "The set is empty when there is no such edge. Time complexity:
     @($O(\\log(n) + \\log(d))$), where @($n$) is the number of nodes and
     @($d$) the number of successors of @('from').")
  (treemap::lookup to (adjacency from graph) :default (treeset::empty))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule labels-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (labels from to graph0)
                  (labels from to graph1)))
  :rule-classes :congruence
  :enable labels)

;; The value at a target of an adjacency is the set of labels of the edges to
;; it, which is written as labels. An absent target may be read with either
;; empty default, @('nil') or @('(treeset::empty)').

(defrule lookup-of-adjacency
  (implies (and (treeset::setp default)
                (treeset::emptyp (double-rewrite default)))
           (equal (treemap::lookup to (adjacency from graph) :default default)
                  (labels from to graph)))
  :enable (labels
           treeset::emptyp-alt-definition))

(theory-invariant (incompatible! (:definition labels$inline)
                                 (:rewrite lookup-of-adjacency)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The labels from one node to another are the labels of the edges between
;; them.

(defrule in-of-labels
  (equal (treeset::in label (labels from to graph))
         (treeset::in (edge from to label) (edges graph)))
  :enable (labels
           adjacency
           edges
           in-of-adj-list-edges)
  :disable lookup-of-adjacency)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge-in (from to label (graph graphp))
  :parents (graph)
  :short "Check if a labeled edge is an edge of a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), where @($n$)
       is the number of nodes, @($d$) the number of successors of
       @('from'), and @($l$) the number of labels on edges from @('from') to
       @('to').")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(edge-in from to label graph)')
       becomes @('(treeset::in (edge from to label) (edges graph))'). Unlike
       that form, it does not construct the edge set when executed."))
  (mbe :logic (treeset::in (edge from to label) (edges graph))
       :exec (treeset::in label (labels from to graph)))
  :enabled t
  :inline t)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy adjacency-extra-rules
  '(adjacency-when-not-in-of-nodes))
