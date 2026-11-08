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

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../edges-defs")
(include-book "../adjacency-defs")
(include-book "step-defs")
(include-book "walk-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))

(local (include-book "../graph"))
(local (include-book "../nodes"))
(local (include-book "../edges"))
(local (include-book "../adjacency"))
(local (include-book "step"))
(local (include-book "walk"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check that each step, taken from the given node, follows an edge of the
;; graph, reading the step's label from the adjacency of the node it is taken
;; from. This builds no edge set, so it is what walk-in executes.

(define steps-in (from (steps step-listp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (walk-in)
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

(define walk-in ((walk walkp) (graph graphp))
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Check if a walk is a walk in a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "A walk is in a graph when it starts at a node and every edge it follows
       is an edge of the graph. Its other nodes are then nodes too, as the
       ends of its edges.")
    (xdoc::p
      "Time complexity: @($O(k(\\log(n) + \\log(d) + \\log(l)))$), where @($k$)
       is the number of steps, @($n$) the number of nodes, @($d$) the largest
       number of successors of a node, and @($l$) the largest number of labels
       on edges between two nodes."))
  (mbe :logic (and (treeset::in (walk->start walk) (nodes graph))
                   (treeset::subset (walk-edges walk) (edges graph)))
       :exec (and (node-in (walk->start walk) graph)
                  (steps-in (walk->start walk) (walk->steps walk) graph)))
  :guard-hints (("Goal" :in-theory (enable walk-edges
                                           steps-in-becomes-subset-of-steps-edges))))

;;;;;;;;;;;;;;;;;;;;

(defrule walk-in-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-in walk0 graph)
                  (walk-in walk1 graph)))
  :rule-classes :congruence
  :enable walk-in)

(defrule walk-in-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (walk-in walk graph0)
                  (walk-in walk graph1)))
  :rule-classes :congruence
  :enable walk-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk with no steps is in a graph exactly when its start is a node.

(defrule walk-in-when-not-consp-of-walk->steps
  (implies (not (consp (walk->steps walk)))
           (equal (walk-in walk graph)
                  (treeset::in (walk->start walk) (nodes graph))))
  :enable walk-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk in a graph ends at a node: it starts at one, and each edge it follows
;; leads to one.

(defrulel in-of-steps-end-and-nodes
  (implies (and (treeset::in from (nodes graph))
                (treeset::subset (steps-edges from steps) (edges graph)))
           (treeset::in (steps-end from steps) (nodes graph)))
  :induct t
  :enable (steps-end
           steps-edges))

(defrule in-of-walk-end-and-nodes-when-walk-in
  (implies (walk-in walk graph)
           (treeset::in (walk-end walk) (nodes graph)))
  :enable (walk-in
           walk-end
           walk-edges))
