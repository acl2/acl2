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

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "add-node-defs")
(include-book "internal/add-node-defs")
(include-book "internal/add-edge-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "extensionality"))
(local (include-book "add-node"))
(local (include-book "internal/add-node"))
(local (include-book "internal/add-edge"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-edge (from to label (graph graphp))
  :type-prescription :none
  :returns (graph$ graphp
                   :hints (("Goal" :in-theory (enable* graphp
                                                       break-abstraction))))
  :parents (graph)
  :short "Add a labeled edge to a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Both endpoints are added as nodes if they are not nodes already. An
       edge already in the graph is left alone. See @(tsee add-edge!) for a
       slightly faster version which requires the target to already be a
       node.")
    (xdoc::p
      "Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), where @($n$)
       is the number of nodes, @($d$) the number of targets of the source, and
       @($l$) the number of labels on edges from the source to the target."))
  (adj-list-add-edge from to label (adj-list-add-node to (fix graph)))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule add-edge-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (add-edge from to label graph0)
                  (add-edge from to label graph1)))
  :rule-classes :congruence
  :enable add-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-edge! (from to label (graph graphp))
  :guard (node-in to graph)
  :parents (add-edge)
  :short "Add a labeled edge to a @(see graph) whose target is already a
          node."
  :long
  (xdoc::topstring
    (xdoc::p
      "Logically this is @(tsee add-edge), to which it is rewritten. It saves
       checking for the target, which the guard requires to be present
       already. The source need not be.")
    (xdoc::p
      "Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), as for @(tsee
       add-edge)."))
  (mbe :logic (add-edge from to label graph)
       :exec (adj-list-add-edge from to label graph))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* add-edge
                                            adj-list-add-node
                                            nodes
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nodes-of-add-edge
  (equal (nodes (add-edge from to label graph))
         (treeset::insert from (treeset::insert to (nodes graph))))
  :enable (nodes
           add-edge
           graphp
           break-abstraction))

(defrule edges-of-add-edge
  (equal (edges (add-edge from to label graph))
         (treeset::insert (edge from to label) (edges graph)))
  :enable (edges
           add-edge
           graphp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-edge-of-add-edge-same
  (equal (add-edge from to label (add-edge from to label graph))
         (add-edge from to label graph))
  :enable extensionality)

(defrule add-edge-of-add-edge-commutative
  (equal (add-edge from0 to0 label0 (add-edge from1 to1 label1 graph))
         (add-edge from1 to1 label1 (add-edge from0 to0 label0 graph)))
  :enable extensionality)

;; Adding an edge already adds both of its endpoints as nodes, and adding a
;; node moves inward past adding an edge, so that a graph is built by adding
;; its nodes first.

(defrule add-edge-of-add-node-same-from
  (equal (add-edge from to label (add-node from graph))
         (add-edge from to label graph))
  :enable extensionality)

(defrule add-edge-of-add-node-same-to
  (equal (add-edge from to label (add-node to graph))
         (add-edge from to label graph))
  :enable extensionality)

(defrule add-node-of-add-edge
  (equal (add-node node (add-edge from to label graph))
         (add-edge from to label (add-node node graph)))
  :enable extensionality)
