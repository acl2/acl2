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
(include-book "adjacency-defs")
(include-book "successors-defs")
(include-book "predecessors-defs")
(include-book "add-node-defs")
(include-book "add-edge-defs")
(include-book "internal/delete-edge-defs")

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
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "predecessors"))
(local (include-book "extensionality"))
(local (include-book "add-node"))
(local (include-book "add-edge"))
(local (include-book "internal/delete-edge"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-edge (from to label (graph graphp))
  :type-prescription :none
  :returns (graph$ graphp
                   :hints (("Goal" :in-theory (enable* graphp
                                                       break-abstraction))))
  :parents (graph)
  :short "Remove a labeled edge from a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "The nodes are left alone, including the endpoints of the removed edge.
       Removing an edge which is not in the graph leaves the graph
       unchanged.")
    (xdoc::p
      "Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), where @($n$)
       is the number of nodes, @($d$) the number of successors of the source,
       and @($l$) the number of labels on edges from the source to the
       target."))
  (adj-list-delete-edge from to label (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-edge-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (delete-edge from to label graph0)
                  (delete-edge from to label graph1)))
  :rule-classes :congruence
  :enable delete-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nodes-of-delete-edge
  (equal (nodes (delete-edge from to label graph))
         (nodes graph))
  :enable (nodes
           delete-edge
           graphp
           break-abstraction))

(defrule edges-of-delete-edge
  (equal (edges (delete-edge from to label graph))
         (treeset::delete (edge from to label) (edges graph)))
  :enable (edges
           delete-edge
           graphp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only the labels from the source to the target change.

(defruled labels-of-delete-edge
  (equal (labels x y (delete-edge from to label graph))
         (if (and (equal x from)
                  (equal y to))
             (treeset::delete label (labels x y graph))
           (labels x y graph)))
  :enable treeset::extensionality-polar)

(defrule labels-of-delete-edge-same
  (equal (labels from to (delete-edge from to label graph))
         (treeset::delete label (labels from to graph)))
  :enable labels-of-delete-edge)

(defrule labels-of-delete-edge-diff-from-cheap
  (implies (not (equal x from))
           (equal (labels x y (delete-edge from to label graph))
                  (labels x y graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable labels-of-delete-edge)

(defrule labels-of-delete-edge-diff-to-cheap
  (implies (not (equal y to))
           (equal (labels x y (delete-edge from to label graph))
                  (labels x y graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable labels-of-delete-edge)

;;;;;;;;;;;;;;;;;;;;

;; The target stops being a successor of the source only if the label was the
;; only one from the source to the target.

(defruled successors-of-delete-edge
  (equal (successors x (delete-edge from to label graph))
         (if (and (equal x from)
                  (equal (labels from to graph)
                         (treeset::insert label (treeset::empty))))
             (treeset::delete to (successors x graph))
           (successors x graph)))
  :enable (treeset::extensionality
           in-of-successors-becomes-not-emptyp-of-labels
           labels-of-delete-edge)
  :disable emptyp-of-labels)

(defrule successors-of-delete-edge-diff-cheap
  (implies (not (equal x from))
           (equal (successors x (delete-edge from to label graph))
                  (successors x graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable successors-of-delete-edge)

(defruled predecessors-of-delete-edge
  (equal (predecessors y (delete-edge from to label graph))
         (if (and (equal y to)
                  (equal (labels from to graph)
                         (treeset::insert label (treeset::empty))))
             (treeset::delete from (predecessors y graph))
           (predecessors y graph)))
  :enable (treeset::extensionality
           in-of-successors-becomes-not-emptyp-of-labels
           labels-of-delete-edge)
  :disable emptyp-of-labels)

(defrule predecessors-of-delete-edge-diff-cheap
  (implies (not (equal y to))
           (equal (predecessors y (delete-edge from to label graph))
                  (predecessors y graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable predecessors-of-delete-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removing an edge which is not there does nothing.

(defruled delete-edge-when-not-in-of-edges
  (implies (not (treeset::in (edge from to label) (edges graph)))
           (equal (delete-edge from to label graph)
                  (fix graph)))
  :enable extensionality)

(defrule delete-edge-when-not-in-of-edges-cheap
  (implies (not (treeset::in (edge from to label) (edges graph)))
           (equal (delete-edge from to label graph)
                  (fix graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-edge-when-not-in-of-edges)

(defrule delete-edge-of-delete-edge-same
  (equal (delete-edge from to label (delete-edge from to label graph))
         (delete-edge from to label graph))
  :enable extensionality)

(defrule delete-edge-of-delete-edge-commutative
  (equal (delete-edge from0 to0 label0 (delete-edge from1 to1 label1 graph))
         (delete-edge from1 to1 label1 (delete-edge from0 to0 label0 graph)))
  :enable extensionality)

;; As with adding an edge, adding a node moves inward past deleting one.

(defrule add-node-of-delete-edge
  (equal (add-node node (delete-edge from to label graph))
         (delete-edge from to label (add-node node graph)))
  :enable extensionality)

;; Adding an edge and then deleting it leaves both endpoints behind as nodes.

(defrule delete-edge-of-add-edge-same
  (equal (delete-edge from to label (add-edge from to label graph))
         (delete-edge from to label (add-node from (add-node to graph))))
  :enable extensionality)

(defrule add-edge-of-delete-edge-same
  (equal (add-edge from to label (delete-edge from to label graph))
         (add-edge from to label graph))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy delete-edge-extra-rules
  '(delete-edge-when-not-in-of-edges
    labels-of-delete-edge
    successors-of-delete-edge
    predecessors-of-delete-edge))
