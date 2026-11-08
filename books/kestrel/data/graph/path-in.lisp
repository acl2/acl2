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
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")
(include-book "adjacency-defs")
(include-book "step-defs")
(include-book "path-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "adjacency"))
(local (include-book "step"))
(local (include-book "path"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check that each step, taken from the given node, follows an edge of the
;; graph, reading the step's label from the adjacency of the node it is taken
;; from. This builds no edge set, so it is what path-in executes.

(define steps-in (from (steps step-listp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (path-in)
  (if (consp steps)
      (b* ((to (step->to (car steps))))
        (and (treeset::in (step->label (car steps))
                          (treemap::lookup to (adjacency from graph)))
             (steps-in to (cdr steps) graph)))
    t))

;;;;;;;;;;;;;;;;;;;;

(defrule steps-in-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (steps-in from steps graph0)
                  (steps-in from steps graph1)))
  :rule-classes :congruence
  :induct t
  :enable steps-in)

(defruledl steps-in-becomes-subset-of-steps-edges
  (equal (steps-in from steps graph)
         (treeset::subset (steps-edges from steps) (edges graph)))
  :induct t
  :enable (steps-in
           steps-edges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-in ((path pathp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (graph)
  :short "Check if a path is a path in a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "A path is in a graph when it starts at a node and every edge it follows
       is an edge of the graph. Its other nodes are then nodes too, as the
       ends of its edges.")
    (xdoc::p
      "Time complexity: @($O(k(\\log(n) + \\log(d) + \\log(l)))$), where @($k$)
       is the number of steps, @($n$) the number of nodes, @($d$) the largest
       number of targets of a node, and @($l$) the largest number of labels
       on edges between two nodes."))
  (mbe :logic (and (treeset::in (path->start path) (nodes graph))
                   (treeset::subset (path-edges path) (edges graph)))
       :exec (and (node-in (path->start path) graph)
                  (steps-in (path->start path) (path->steps path) graph)))
  :guard-hints (("Goal" :in-theory (enable path-edges
                                           steps-in-becomes-subset-of-steps-edges))))

;;;;;;;;;;;;;;;;;;;;

(defrule path-in-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path-in path0 graph)
                  (path-in path1 graph)))
  :rule-classes :congruence
  :enable path-in)

(defrule path-in-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (path-in path graph0)
                  (path-in path graph1)))
  :rule-classes :congruence
  :enable path-in)
