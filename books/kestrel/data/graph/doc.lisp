; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book is used only for the manual. It is not intended to be included by
;; ordinary books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ graph
  :parents (data::data-lib)
  :short "A tree-based implementation of finite directed graphs with labeled
          edges."
  :long
  (xdoc::topstring
    (xdoc::p
      "A @(see graph) is a finite set of nodes together with a finite set of
       edges between them. An edge is a triple of a source node, a target
       node, and a label (see @(tsee edgep)). Nodes and labels may be any
       values. Two nodes may be joined by several edges in the same
       direction, provided their labels differ. Edges from a node to itself
       are allowed, as are nodes with no edges at all.")
    (xdoc::p
      "A graph is determined by its @(tsee nodes) and its @(tsee edges) (see
       @(see extensionality)), and the properties of the operations are stated
       in terms of those two sets. They are the logical view of a graph, and
       are not necessarily meant to be computed in execution. The edge set in
       particular is expensive to build.")
    (xdoc::p
      "A graph is represented as an adjacency list: a "
      (xdoc::seetopic "acl2::treemap" "treemap")
      " from each node to a treemap from each of its successors to the
       nonempty "
      (xdoc::seetopic "acl2::treeset" "treeset")
      " of labels on the edges between them. Following the edges out of a node
       is therefore cheap, but finding the edges into a node means visiting
       every node. A program which needs a node's predecessors should maintain
       the transpose of the graph as well.")
    (xdoc::p
      "The core operations are:")
    (xdoc::table_
      (xdoc::tr
        (xdoc::td "@(tsee graphp)")
        (xdoc::td "@($O(n + m\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee emptyp)")
        (xdoc::td "@($O(1)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee nodes)")
        (xdoc::td "@($O(n)$)"))
      (xdoc::tr
        (xdoc::td "@(tsee node-in)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee edges-from)")
        (xdoc::td "@($O(\\log(n) + k\\log(k))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee edges-to)")
        (xdoc::td "@($O(n(\\log(n) + \\log(d)) + k\\log(k))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee adjacency), @(tsee adjacency!)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee add-node)")
        (xdoc::td "@($O(\\log(n))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee add-edge), @(tsee add-edge!)")
        (xdoc::td "@($O(\\log(n) + \\log(d) + \\log(l))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee delete-edge)")
        (xdoc::td "@($O(\\log(n) + \\log(d) + \\log(l))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee delete-node)")
        (xdoc::td "@($O(n\\log(d))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee delete-node!)")
        (xdoc::td "@($O(\\log(n))$)")))
    (xdoc::p
      "(where @($n$) is the number of nodes, @($m$) the number of pairs of
       nodes joined by an edge, @($d$) the number of successors of a node, or
       the largest such number for @(tsee edges-to) and @(tsee delete-node),
       @($l$) the number of labels on edges between two nodes, and @($k$) the
       number of edges returned).")
    (xdoc::p
      "A function whose name ends in @('!') is logically the same as the
       function without the @('!'), to which it is rewritten. It has a
       stronger guard, which lets it skip work in execution."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ walks
  :parents (graph)
  :short "Walks in a @(see graph), and the properties defined by them."
  :long
  (xdoc::topstring
    (xdoc::p
      "A @(see walkp) is a start node and a list of steps, each naming the
       node it moves to and the label of the edge it follows. Whether a walk
       is a walk in a particular graph is @(tsee walk-in). Reachability is the
       existence of a walk of at least one step (see @(tsee reachablep)).")
    (xdoc::p
      "The operations are:")
    (xdoc::table_
      (xdoc::tr
        (xdoc::td "@(tsee walk-in)")
        (xdoc::td "@($O(k(\\log(n) + \\log(d) + \\log(l)))$)"))
      (xdoc::tr
        (xdoc::td "@(tsee reachablep)")
        (xdoc::td "@($O((n + m)\\log(n))$)")))
    (xdoc::p
      "(where @($n$) is the number of nodes, @($m$) the number of pairs of
       nodes joined by an edge, @($d$) the largest number of successors of a
       node, @($l$) the largest number of labels on edges between two nodes,
       and @($k$) the number of steps of the walk)."))
  :order-subtopics t)
