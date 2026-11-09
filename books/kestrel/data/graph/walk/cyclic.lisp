; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "kahn-defs")
(include-book "reachable-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))

(local (include-book "../graph"))
(local (include-book "../nodes"))
(local (include-book "../successors"))
(local (include-book "../predecessors"))
(local (include-book "kahn"))
(local (include-book "reachable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk cyclicp-sk (graph)
  :parents (cyclicp)
  :short "Check if some node of a @(see graph) reaches itself."
  :long
  (xdoc::topstring-p
    "This is the specification of @(tsee cyclicp), to which it is equal. It
     is not executable.")
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (exists (node)
    (non-exec (reachable+p node node graph))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t cyclicp-sk)))

(defrule cyclicp-sk-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (cyclicp-sk graph0)
                  (cyclicp-sk graph1)))
  :rule-classes :congruence
  :use ((:instance cyclicp-sk-suff
                   (node (cyclicp-sk-witness graph0))
                   (graph graph1))
        (:instance cyclicp-sk-suff
                   (node (cyclicp-sk-witness graph1))
                   (graph graph0)))
  :enable cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cyclicp ((graph graphp))
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Check if a @(see graph) has a cycle."
  :long
  (xdoc::topstring
    (xdoc::p
      "A graph has a cycle exactly when some node reaches itself (see @(tsee
       reachable+p)). Logically this equals @(tsee cyclicp-sk), which states
       that directly. A graph without a cycle is a directed acyclic graph.")
    (xdoc::p
      "This uses Kahn's algorithm: it repeatedly removes a node with no edge
       into it from the nodes not yet removed, and the graph has a cycle
       exactly when it gets stuck before removing every node. It keeps, for
       each node, the number of nodes not yet removed with an edge to it.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
       nodes and @($m$) the number of pairs of nodes joined by an edge."))
  (mbe :logic (not (treeset::emptyp (kahn-remaining (nodes graph) graph)))
       :exec (b* ((nodes (nodes graph))
                  (counters (kahn-counters nodes (treemap::empty) graph))
                  ((mv - remaining)
                   (kahn-loop nodes
                              (treeset::diff nodes (treemap::keys counters))
                              counters
                              nil
                              graph)))
               (not (treeset::emptyp remaining)))))

;;;;;;;;;;;;;;;;;;;;

(defrule cyclicp-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (cyclicp graph0)
                  (cyclicp graph1)))
  :rule-classes :congruence
  :enable cyclicp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness: no node removed reaches itself. The remaining nodes include
;; their own successors, and still do after a node which is not one of their
;; successors is removed. Every node reachable from that node is then still
;; remaining, so the node itself is not.

(defruledl reachable+p-when-not-in-of-kahn-remaining
  (implies (and (treeset::subset (successors-of-set remaining graph)
                                 remaining)
                (treeset::in node remaining)
                (not (treeset::in node (kahn-remaining remaining graph))))
           (not (reachable+p node node graph)))
  :induct (kahn-remaining remaining graph)
  :enable (kahn-remaining
           reachable+p-when-not-in-of-successors-of-set))

(defruledl not-emptyp-of-kahn-remaining-when-cyclicp-sk
  (implies (cyclicp-sk graph)
           (not (treeset::emptyp (kahn-remaining (nodes graph) graph))))
  :use (:instance reachable+p-when-not-in-of-kahn-remaining
                  (node (cyclicp-sk-witness graph))
                  (remaining (nodes graph)))
  :enable cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness: a nonempty set whose nodes are all successors of its nodes has a
;; node on a cycle, so when there is no cycle, Kahn's algorithm removes every
;; node.
;;
;; In such a set, the nodes of the set reaching any one of its nodes form
;; another such set. If the least node is not on a cycle, the set formed for it
;; leaves it out, so the search descends into a smaller set.

(defrulel reachable+p-when-not-cyclicp-sk
  (implies (not (cyclicp-sk graph))
           (not (reachable+p node node graph)))
  :enable cyclicp-sk-suff)

(local
  (define find-node-on-cycle ((set treeset::setp) graph)
    (b* (((when (treeset::emptyp set))
          nil)
         (node (treeset::min set))
         ((when (reachable+p node node graph))
          node))
      (find-node-on-cycle (treeset::intersect set (predecessors+ node graph))
                          graph))
    :measure (treeset::cardinality set)
    :hints (("Goal" :use (:instance treeset::in-of-min-when-subset
                                    (treeset::set set)
                                    (treeset::y (predecessors+
                                                  (treeset::min set)
                                                  graph)))
                    :in-theory (disable treeset::in-of-min-when-subset)))
    :verify-guards nil))

(defrulel find-node-on-cycle-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
           (equal (find-node-on-cycle set0 graph)
                  (find-node-on-cycle set1 graph)))
  :rule-classes :congruence
  :expand ((find-node-on-cycle set0 graph)
           (find-node-on-cycle set1 graph)))

;; A node stays a successor of a set restricted to another which includes its
;; predecessors.

(defrulel in-of-successors-of-set-of-intersect
  (implies (and (treeset::subset (predecessors node graph) set2)
                (treeset::in node (successors-of-set set graph)))
           (treeset::in node
                        (successors-of-set (treeset::intersect set set2)
                                           graph)))
  :enable in-of-successors-of-set-becomes-not-emptyp-of-intersect)

;; So in a set whose nodes are all successors of its nodes, the nodes reaching
;; a given node of it form a nonempty set whose nodes are all successors of its
;; nodes.

(defrulel emptyp-of-intersect-and-predecessors+
  (implies (treeset::in node (successors-of-set set graph))
           (not (treeset::emptyp
                  (treeset::intersect set (predecessors+ node graph)))))
  :use (:instance in-of-successors-of-set-of-intersect
                  (set2 (predecessors+ node graph)))
  :expand (successors-of-set (treeset::intersect set (predecessors+ node graph))
                             graph)
  :disable in-of-successors-of-set-of-intersect)

(defrulel subset-of-intersect-and-successors-of-set-of-intersect
  (implies (treeset::subset set (successors-of-set set graph))
           (treeset::subset
             (treeset::intersect set (predecessors+ node graph))
             (successors-of-set
               (treeset::intersect set (predecessors+ node graph))
               graph)))
  :enable treeset::pick-a-point-polar)

(defrulel reachable+p-of-find-node-on-cycle
  (implies (and (treeset::subset set (successors-of-set set graph))
                (not (treeset::emptyp set)))
           (reachable+p (find-node-on-cycle set graph)
                        (find-node-on-cycle set graph)
                        graph))
  :induct t
  :enable find-node-on-cycle)

(defruledl subset-of-arg1-and-successors-of-set-when-not-cyclicp-sk
  (implies (and (not (cyclicp-sk graph))
                (not (treeset::emptyp set)))
           (not (treeset::subset set (successors-of-set set graph))))
  :use (:instance reachable+p-when-not-cyclicp-sk
                  (node (find-node-on-cycle set graph)))
  :disable reachable+p-when-not-cyclicp-sk)

;; Kahn's algorithm stops only at a set whose nodes are all successors of its
;; nodes.

(defrulel subset-of-kahn-remaining-and-successors-of-set
  (treeset::subset (kahn-remaining remaining graph)
                   (successors-of-set (kahn-remaining remaining graph) graph))
  :induct t
  :enable kahn-remaining)

(defruledl emptyp-of-kahn-remaining-when-not-cyclicp-sk
  (implies (not (cyclicp-sk graph))
           (treeset::emptyp (kahn-remaining remaining graph)))
  :use (:instance subset-of-arg1-and-successors-of-set-when-not-cyclicp-sk
                  (set (kahn-remaining remaining graph))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cyclicp-becomes-cyclicp-sk
  (equal (cyclicp graph)
         (cyclicp-sk graph))
  :enable (cyclicp
           not-emptyp-of-kahn-remaining-when-cyclicp-sk
           emptyp-of-kahn-remaining-when-not-cyclicp-sk))

(defruled cyclicp-sk-becomes-cyclicp
  (equal (cyclicp-sk graph)
         (cyclicp graph))
  :by cyclicp-becomes-cyclicp-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A graph without a cycle has no node which reaches itself, and a graph with
;; such a node has a cycle.

(defruled reachable+p-of-arg1-and-arg1-when-not-cyclicp
  (implies (not (cyclicp graph))
           (not (reachable+p node node graph)))
  :enable cyclicp-becomes-cyclicp-sk)

(defrule reachable+p-of-arg1-and-arg1-when-not-cyclicp-cheap
  (implies (not (cyclicp graph))
           (not (reachable+p node node graph)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by reachable+p-of-arg1-and-arg1-when-not-cyclicp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy cyclic-extra-rules
  '(reachable+p-of-arg1-and-arg1-when-not-cyclicp))
