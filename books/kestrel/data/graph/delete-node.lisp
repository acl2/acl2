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
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/intersect-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")
(include-book "successors-defs")
(include-book "predecessors-defs")
(include-book "add-node-defs")
(include-book "internal/delete-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "predecessors"))
(local (include-book "extensionality"))
(local (include-book "add-node"))
(local (include-book "internal/edges"))
(local (include-book "internal/predecessors"))
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
      "Time complexity: @($O(n \\log(d))$), where @($n$) is the number of
       nodes and @($d$) the largest number of successors of a node."))
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

;; The effect on the nodes and edges: the node is removed, and so is every edge
;; out of or into it.

(defrule nodes-of-delete-node
  (equal (nodes (delete-node node graph))
         (treeset::delete node (nodes graph)))
  :enable (nodes
           delete-node
           graphp
           break-abstraction))

(defruled in-of-edges-of-delete-node
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

;; The edges less those out of the node and those into it, in the normal form
;; treeset gives a difference from a union.

(defrule edges-of-delete-node
  (equal (edges (delete-node node graph))
         (treeset::intersect
           (treeset::diff (edges graph) (edges-from node graph))
           (treeset::diff (edges graph) (edges-to node graph))))
  :enable (treeset::extensionality-no-backchain-limit-polar
           in-of-edges-of-delete-node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every label from or to the node is gone, and no other label changes.

(defruled labels-of-delete-node
  (equal (labels x y (delete-node node graph))
         (if (or (equal x node)
                 (equal y node))
             (treeset::empty)
           (labels x y graph)))
  :enable (treeset::extensionality-polar
           in-of-edges-of-delete-node))

(defrule labels-of-delete-node-same-from
  (equal (labels node y (delete-node node graph))
         (treeset::empty))
  :enable labels-of-delete-node)

(defrule labels-of-delete-node-same-to
  (equal (labels x node (delete-node node graph))
         (treeset::empty))
  :enable labels-of-delete-node)

(defrule labels-of-delete-node-diff-cheap
  (implies (and (not (equal x node))
                (not (equal y node)))
           (equal (labels x y (delete-node node graph))
                  (labels x y graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :enable labels-of-delete-node)

;;;;;;;;;;;;;;;;;;;;

;; The node has no successors or predecessors left, and is no longer a
;; successor or predecessor of any other node.

(defruled successors-of-delete-node
  (equal (successors x (delete-node node graph))
         (if (equal x node)
             (treeset::empty)
           (treeset::delete node (successors x graph))))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels
           labels-of-delete-node)
  :disable emptyp-of-labels)

(defrule successors-of-delete-node-same
  (equal (successors node (delete-node node graph))
         (treeset::empty))
  :enable successors-of-delete-node)

(defrule successors-of-delete-node-diff-cheap
  (implies (not (equal x node))
           (equal (successors x (delete-node node graph))
                  (treeset::delete node (successors x graph))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable successors-of-delete-node)

(defruled predecessors-of-delete-node
  (equal (predecessors y (delete-node node graph))
         (if (equal y node)
             (treeset::empty)
           (treeset::delete node (predecessors y graph))))
  :enable (treeset::extensionality-polar
           in-of-successors-becomes-not-emptyp-of-labels
           labels-of-delete-node)
  :disable emptyp-of-labels)

(defrule predecessors-of-delete-node-same
  (equal (predecessors node (delete-node node graph))
         (treeset::empty))
  :enable predecessors-of-delete-node)

(defrule predecessors-of-delete-node-diff-cheap
  (implies (not (equal y node))
           (equal (predecessors y (delete-node node graph))
                  (treeset::delete node (predecessors y graph))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable predecessors-of-delete-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removing a value which is not a node does nothing. No edge touches it,
;; since both ends of every edge are nodes.

(defruled delete-node-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (delete-node node graph)
                  (fix graph)))
  :enable (extensionality
           treeset::extensionality-no-backchain-limit-polar))

(defrule delete-node-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (delete-node node graph)
                  (fix graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-node-when-not-in-of-nodes)

(defrule delete-node-of-delete-node-same
  (equal (delete-node node (delete-node node graph))
         (delete-node node graph))
  :enable delete-node-when-not-in-of-nodes)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-node! (node (graph graphp))
  :guard (treeset::subset (predecessors node graph)
                          (treeset::set node))
  :parents (delete-node)
  :short "Remove a node from a @(see graph) when no other node has an edge to
          it."
  :long
  (xdoc::topstring
    (xdoc::p
      "Logically this is @(tsee delete-node), to which it is rewritten. The
       guard requires that no edge leads into the node from another node, so
       removing the node's own entry, with its outgoing edges and any edges to
       itself, is all there is to do. Checking the guard, however, visits
       every node.")
    (xdoc::p
      "Time complexity: @($O(\\log(n))$), where @($n$) is the number of
       nodes."))
  (mbe :logic (delete-node node graph)
       :exec (treemap::delete node graph))
  :enabled t
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable* delete-node
             predecessors
             adj-list-delete-node-when-subset-of-adj-list-predecessors
             break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy delete-node-extra-rules
  '(delete-node-when-not-in-of-nodes
    labels-of-delete-node
    successors-of-delete-node
    predecessors-of-delete-node))
