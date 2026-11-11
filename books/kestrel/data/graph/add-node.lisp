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

(include-book "kestrel/data/treeset/insert-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")
(include-book "successors-defs")
(include-book "predecessors-defs")
(include-book "internal/add-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "predecessors"))
(local (include-book "extensionality"))
(local (include-book "internal/add-node"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-node (node (graph graphp))
  :type-prescription :none
  :returns (graph$ graphp
                   :hints (("Goal" :in-theory (enable* graphp
                                                       break-abstraction))))
  :parents (graph)
  :short "Add a node to a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "The node is added with no edges. A node already in the graph is left
       alone, along with its edges.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$), where @($n$) is the number of
       nodes."))
  (adj-list-add-node node (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule add-node-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (add-node node graph0)
                  (add-node node graph1)))
  :rule-classes :congruence
  :enable add-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nodes-of-add-node
  (equal (nodes (add-node node graph))
         (treeset::insert node (nodes graph)))
  :enable (nodes
           add-node
           graphp
           break-abstraction))

(defrule edges-of-add-node
  (equal (edges (add-node node graph))
         (edges graph))
  :enable (edges
           add-node
           graphp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The new node has no edges, so no labels, successors, or predecessors
;; change.

(defrule labels-of-add-node
  (equal (labels x y (add-node node graph))
         (labels x y graph))
  :enable treeset::extensionality-polar)

(defrule successors-of-add-node
  (equal (successors x (add-node node graph))
         (successors x graph))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels)
  :disable emptyp-of-labels)

(defrule predecessors-of-add-node
  (equal (predecessors y (add-node node graph))
         (predecessors y graph))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels)
  :disable emptyp-of-labels)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-node-of-add-node-same
  (equal (add-node node (add-node node graph))
         (add-node node graph))
  :enable extensionality)

(defrule add-node-of-add-node-commutative
  (equal (add-node node0 (add-node node1 graph))
         (add-node node1 (add-node node0 graph)))
  :enable extensionality)
