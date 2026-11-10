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

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")
(include-book "successors-defs")
(include-book "predecessors-defs")
(include-book "internal/transpose-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "predecessors"))
(local (include-book "extensionality"))
(local (include-book "internal/transpose"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transpose ((graph graphp))
  :type-prescription :none
  :returns (graph$ graphp
                   :hints (("Goal" :in-theory (enable* graphp
                                                       break-abstraction))))
  :parents (graph)
  :short "Reverse every edge of a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "The nodes are the same, and each edge from one node to another becomes
       an edge with the same label from the second to the first. So the
       successors of a node in the transpose are its predecessors in the
       graph, and the other way around.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
       nodes and @($m$) the number of pairs of nodes joined by an edge. The
       sets of labels are shared with the graph, not copied."))
  (adj-list-transpose (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule transpose-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (transpose graph0)
                  (transpose graph1)))
  :rule-classes :congruence
  :enable transpose)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the nodes and edges: the nodes are kept, and every edge is
;; reversed.

(defrule nodes-of-transpose
  (equal (nodes (transpose graph))
         (nodes graph))
  :enable (nodes
           transpose
           graphp
           break-abstraction))

(defrule in-of-edges-of-transpose
  (implies (edge-equiv edge$ (double-rewrite edge))
           (equal (treeset::in edge (edges (transpose graph)))
                  (and (edgep edge)
                       (treeset::in (edge (edge->to edge$)
                                          (edge->from edge$)
                                          (edge->label edge$))
                                    (edges graph)))))
  :enable (edges
           transpose
           graphp
           break-abstraction
           in-of-adj-list-edges-of-adj-list-transpose))

;; So the labels, successors, and predecessors are those of the graph with the
;; directions swapped.

(defrule labels-of-transpose
  (equal (labels x y (transpose graph))
         (labels y x graph))
  :enable (labels
           adjacency
           transpose
           graphp
           break-abstraction)
  :disable lookup-of-adjacency)

(defrule successors-of-transpose
  (equal (successors node (transpose graph))
         (predecessors node graph))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels)
  :disable emptyp-of-labels)

(defrule predecessors-of-transpose
  (equal (predecessors node (transpose graph))
         (successors node graph))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels)
  :disable emptyp-of-labels)

(defrule transpose-of-transpose
  (equal (transpose (transpose graph))
         (fix graph))
  :enable (extensionality
           treeset::extensionality-polar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The search for the nodes reaching a node steps as the search for the nodes
;; reachable from it in the transpose does. So the nodes reachable from a node
;; in the transpose are those reaching it in the graph, and the other way
;; around.

(defrulel predecessors+-search-becomes-successors+-search-of-transpose
  (equal (predecessors+-search frontier expanded graph)
         (successors+-search frontier expanded (transpose graph)))
  :induct t
  :enable (predecessors+-search
           successors+-search))

(defrule successors+-of-transpose
  (equal (successors+ node (transpose graph))
         (predecessors+ node graph))
  :enable (successors+
           predecessors+))

(defrule predecessors+-of-transpose
  (equal (predecessors+ node (transpose graph))
         (successors+ node graph))
  :enable (successors+
           predecessors+))
