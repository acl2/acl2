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

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "successors-defs")
(include-book "internal/predecessors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "adjacency"))
(local (include-book "successors"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/predecessors"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors (node (graph graphp))
  :type-prescription :none
  :returns (predecessors treeset::setp)
  :parents (graph)
  :short "The predecessors of a node of a @(see graph): the nodes with an edge
          to it."
  :long
  (xdoc::topstring
    (xdoc::p
      "A graph records only each node's outgoing edges, so finding the
       predecessors of a node means visiting every node. A value which is not
       a node has no predecessors.")
    (xdoc::p
      "Time complexity: @($O(n(\\log(n) + \\log(d)) + k\\log(k))$), where
       @($n$) is the number of nodes, @($d$) the largest number of successors
       of a node, and @($k$) the number of predecessors. This is not optimal:
       each step takes and deletes the least remaining node, where a traversal
       with an iterator would avoid the deletions."))
  (adj-list-predecessors node (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule predecessors-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (predecessors node graph0)
                  (predecessors node graph1)))
  :rule-classes :congruence
  :enable predecessors)

;; A node is a predecessor of another exactly when the other is one of its
;; successors.

(defrule in-of-predecessors
  (equal (treeset::in from (predecessors to graph))
         (treeset::in to (successors from graph)))
  :enable (predecessors
           successors
           adjacency
           in-of-adj-list-predecessors)
  :disable keys-of-adjacency)

;; Every predecessor is a node, and a value which is not a node has none.

(defrule subset-of-predecessors-and-nodes
  (treeset::subset (predecessors node graph)
                   (nodes graph))
  :enable treeset::pick-a-point-polar)

(defruled predecessors-when-not-in-of-nodes
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (treeset::empty)))
  :enable treeset::extensionality-polar)

(defrule predecessors-when-not-in-of-nodes-cheap
  (implies (not (treeset::in node (nodes graph)))
           (equal (predecessors node graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by predecessors-when-not-in-of-nodes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy predecessors-extra-rules
  '(predecessors-when-not-in-of-nodes))
