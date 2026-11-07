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
(include-book "kestrel/data/treeset/delete-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "add-node-defs")
(include-book "internal/delete-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "extensionality"))
(local (include-book "add-node"))
(local (include-book "internal/delete-node"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-node (node (graph graphp))
  :type-prescription :none
  :returns (graph$ graphp
                   :hints (("Goal" :in-theory (enable* graphp
                                                       break-abstraction))))
  :parents (graph)
  :short "Remove a node from a @(see graph), along with every edge into or
          out of it."
  :long
  (xdoc::topstring
    (xdoc::p
      "Removing a value which is not a node leaves the graph unchanged.")
    (xdoc::p
      "Finding the edges into the node means visiting every node, since a
       graph records only each node's outgoing edges.")
    (xdoc::p
      "Time complexity: @($O(n (\\log(n) + \\log(d)))$), where @($n$) is the
       number of nodes and @($d$) the largest number of targets of a
       node."))
  (adj-list-delete-node node (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-node-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (delete-node node graph0)
                  (delete-node node graph1)))
  :rule-classes :congruence
  :enable delete-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the nodes and edges: the node is removed, and an edge survives
;; exactly when neither of its ends is the node.

(defrule nodes-of-delete-node
  (equal (nodes (delete-node node graph))
         (treeset::delete node (nodes graph)))
  :enable (nodes
           delete-node
           graphp
           break-abstraction))

(defrule in-of-edges-of-delete-node
  (implies (edge-equiv edge$ (double-rewrite edge))
           (equal (treeset::in edge (edges (delete-node node graph)))
                  (and (treeset::in edge (edges graph))
                       (not (equal (edge->from edge$) node))
                       (not (equal (edge->to edge$) node)))))
  :enable (edges
           delete-node
           graphp
           break-abstraction
           in-of-adj-list-edges-of-adj-list-delete-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removing a value which is not a node does nothing. No edge touches it,
;; since both ends of every edge are nodes.

(defrule delete-node-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (delete-node node graph)
                  (fix graph)))
  :enable (extensionality
           treeset::extensionality-no-backchain-limit-polar))

(defrule delete-node-of-delete-node-same
  (equal (delete-node node (delete-node node graph))
         (delete-node node graph))
  :enable (extensionality
           treeset::extensionality-no-backchain-limit-polar))

(defrule delete-node-of-delete-node-commutative
  (equal (delete-node node0 (delete-node node1 graph))
         (delete-node node1 (delete-node node0 graph)))
  :enable (extensionality
           treeset::extensionality-no-backchain-limit-polar))

(defrule delete-node-of-add-node-same
  (equal (delete-node node (add-node node graph))
         (delete-node node graph))
  :enable (extensionality
           treeset::extensionality-no-backchain-limit-polar))
