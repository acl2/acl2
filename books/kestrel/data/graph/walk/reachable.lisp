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
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../adjacency-defs")
(include-book "walk-defs")
(include-book "walk-in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))

(local (include-book "../edge"))
(local (include-book "step"))
(local (include-book "../graph"))
(local (include-book "../nodes"))
(local (include-book "../edges"))
(local (include-book "../adjacency"))
(local (include-book "walk"))
(local (include-book "walk-in"))
(local (include-book "walk-snoc"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel delete-of-arg1-and-empty
  (equal (treeset::delete a (treeset::empty))
         (treeset::empty))
  :enable treeset::delete-when-not-in)

(defrulel diff-of-arg1-and-insert
  (equal (treeset::diff x (treeset::insert a y))
         (treeset::delete a (treeset::diff x y)))
  :enable treeset::extensionality-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk reachablep-sk (from to graph)
  :parents (reachablep)
  :short "Check if there is a walk of at least one step from one node to
          another in a @(see graph)."
  :long
  (xdoc::topstring-p
    "This is the specification of @(tsee reachablep), to which it is equal.
     It is not executable.")
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (exists (walk)
    (non-exec
      (and (walk-in walk graph)
           (equal (walk->start walk) from)
           (equal (walk-end walk) to)
           (consp (walk->steps walk))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t reachablep-sk)))

(defrule reachablep-sk-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (reachablep-sk from to graph0)
                  (reachablep-sk from to graph1)))
  :rule-classes :congruence
  :use ((:instance reachablep-sk-suff
                   (walk (reachablep-sk-witness from to graph0))
                   (graph graph1))
        (:instance reachablep-sk-suff
                   (walk (reachablep-sk-witness from to graph1))
                   (graph graph0)))
  :enable reachablep-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Search for a node, expanding nodes from a frontier. A node is expanded by
;; adding its unexpanded successors to the frontier. The search succeeds when
;; it takes the node it is looking for from the frontier.
;;
;; Each step either expands a new node, of which a graph has finitely many, or
;; drops a node from the frontier. A value which is not a node has no
;; successors, so expanding it also only shrinks the frontier.

(define reachablep-search
  (to
   (frontier treeset::setp)
   (expanded treeset::setp)
   (graph graphp))
  :returns (yes/no booleanp)
  :parents (reachablep)
  (b* (((when (treeset::emptyp frontier))
        nil)
       (node (treeset::min frontier))
       ((when (equal node to))
        t)
       (frontier (treeset::delete node frontier))
       ((when (treeset::in node expanded))
        (reachablep-search to frontier expanded graph))
       (expanded (treeset::insert node expanded)))
    (reachablep-search to
                       (treeset::union
                         frontier
                         (treeset::diff (successors node graph)
                                        expanded))
                       expanded
                       graph))
  :measure (acl2::two-nats-measure
             (treeset::cardinality (treeset::diff (nodes graph) expanded))
             (treeset::cardinality frontier))
  :hints (("Goal" :in-theory (e/d (nfix
                                   treeset::cardinality-of-delete
                                   treeset::equal-of-cardinality-and-0-becomes-emptyp)
                                  (treeset::cardinality-of-diff)))))

;;;;;;;;;;;;;;;;;;;;

(defrule reachablep-search-when-equiv-of-arg2-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (reachablep-search to frontier0 expanded graph)
                  (reachablep-search to frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((reachablep-search to frontier0 expanded graph)
           (reachablep-search to frontier1 expanded graph)))

(defrule reachablep-search-when-equiv-of-arg3-congruence
  (implies (treeset::equiv expanded0 expanded1)
           (equal (reachablep-search to frontier expanded0 graph)
                  (reachablep-search to frontier expanded1 graph)))
  :rule-classes :congruence
  :induct t
  :enable reachablep-search)

(defrule reachablep-search-when-equiv-of-arg4-congruence
  (implies (equiv graph0 graph1)
           (equal (reachablep-search to frontier expanded graph0)
                  (reachablep-search to frontier expanded graph1)))
  :rule-classes :congruence
  :induct t
  :enable reachablep-search)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reachablep (from to (graph graphp))
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Check if there is a walk of at least one step from one node to
          another in a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the transitive closure of the edge relation, without the
       reflexive closure: a node reaches itself only if it is on a cycle.
       Logically it equals @(tsee reachablep-sk), which states the existence
       of the walk directly.")
    (xdoc::p
      "The search expands each node at most once and stops when it finds the
       target. Time complexity: @($O((n + m)\\log(n))$) in the worst case,
       where @($n$) is the number of nodes and @($m$) the number of pairs of
       nodes joined by an edge."))
  (reachablep-search to
                     (successors from graph)
                     (treeset::empty)
                     graph))

;;;;;;;;;;;;;;;;;;;;

(defrule reachablep-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (reachablep from to graph0)
                  (reachablep from to graph1)))
  :rule-classes :congruence
  :enable reachablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walks extended by one step

;; A successor of a node is the end of a one-step walk from it, along the
;; least label of the edges to the successor.

(defrulel reachablep-sk-when-in-of-successors
  (implies (treeset::in to (successors from graph))
           (reachablep-sk from to graph))
  :use (:instance reachablep-sk-suff
                  (walk (walk-snoc (walk from nil)
                                   to
                                   (treeset::min (labels from to graph))))))

;; A walk to a node extends to each of its successors.

(defrulel reachablep-sk-when-reachablep-sk-and-in-of-successors
  (implies (and (reachablep-sk from x graph)
                (treeset::in to (successors x graph)))
           (reachablep-sk from to graph))
  :use ((:instance reachablep-sk-suff
                   (walk (walk-snoc (reachablep-sk-witness from x graph)
                                    to
                                    (treeset::min (labels x to graph)))))
        (:instance reachablep-sk (to x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness: every node in the frontier is reachable, so the node found is.

(local
  (define set-all-reachablep-sk (from (set treeset::setp) graph)
    :returns (yes/no booleanp)
    (or (treeset::emptyp set)
        (and (reachablep-sk from (treeset::min set) graph)
             (set-all-reachablep-sk from
                                    (treeset::delete (treeset::min set) set)
                                    graph)))
    :measure (treeset::cardinality set)
    :hints (("Goal" :in-theory (enable o-p
                                       o-finp
                                       o<
                                       treeset::cardinality-of-delete-when-in
                                       treeset::in-of-min)))
    :verify-guards nil))

(defrulel set-all-reachablep-sk-when-equiv-of-arg2-congruence
  (implies (treeset::equiv set0 set1)
           (equal (set-all-reachablep-sk from set0 graph)
                  (set-all-reachablep-sk from set1 graph)))
  :rule-classes :congruence
  :expand ((set-all-reachablep-sk from set0 graph)
           (set-all-reachablep-sk from set1 graph)))

(defrulel set-all-reachablep-sk-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (set-all-reachablep-sk from set graph0)
                  (set-all-reachablep-sk from set graph1)))
  :rule-classes :congruence
  :induct t
  :enable set-all-reachablep-sk)

(defrulel reachablep-sk-when-set-all-reachablep-sk-and-in
  (implies (and (set-all-reachablep-sk from set graph)
                (treeset::in x set))
           (reachablep-sk from x graph))
  :use (:instance
         (:functional-instance
           treeset::genericp-when-set-all-genericp-and-in
           (treeset::genericp (lambda (x) (reachablep-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachablep-sk from set graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachablep-sk)

(defrulel set-all-reachablep-sk-of-delete
  (implies (set-all-reachablep-sk from set graph)
           (set-all-reachablep-sk from (treeset::delete x set) graph))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-delete
           (treeset::genericp (lambda (x) (reachablep-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachablep-sk from set graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachablep-sk)

(defrulel set-all-reachablep-sk-of-union
  (equal (set-all-reachablep-sk from (treeset::union x y) graph)
         (and (set-all-reachablep-sk from x graph)
              (set-all-reachablep-sk from y graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-union
           (treeset::genericp (lambda (x) (reachablep-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachablep-sk from set graph))))
         (treeset::x x)
         (treeset::y y))
  :enable set-all-reachablep-sk)

;; The successors of the start, and of any reachable node, are reachable.

(defrulel set-all-reachablep-sk-when-subset-of-successors-of-arg1
  (implies (treeset::subset set (successors from graph))
           (set-all-reachablep-sk from set graph))
  :induct t
  :enable set-all-reachablep-sk)

(defruledl set-all-reachablep-sk-when-subset-of-successors
  (implies (and (reachablep-sk from x graph)
                (treeset::subset set (successors x graph)))
           (set-all-reachablep-sk from set graph))
  :induct (set-all-reachablep-sk from set graph)
  :enable set-all-reachablep-sk)

(defrulel set-all-reachablep-sk-of-diff-of-successors
  (implies (reachablep-sk from x graph)
           (set-all-reachablep-sk from
                                  (treeset::diff
                                    (successors x graph)
                                    set)
                                  graph))
  :enable set-all-reachablep-sk-when-subset-of-successors)

(defrulel reachablep-sk-when-reachablep-search
  (implies (and (reachablep-search to frontier expanded graph)
                (set-all-reachablep-sk from frontier graph))
           (reachablep-sk from to graph))
  :induct t
  :enable reachablep-search)

(defruledl reachablep-sk-when-reachablep
  (implies (reachablep from to graph)
           (reachablep-sk from to graph))
  :enable reachablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness: a set containing the successors of the start and the
;; successors of each of its own nodes contains every reachable node. The expanded nodes
;; and the frontier together form such a set when the frontier runs out, and
;; the node sought is never among the expanded nodes.

(local
  (define set-all-successors-subsetp ((set treeset::setp)
                                             (nodes treeset::setp)
                                             (graph graphp))
    :returns (yes/no booleanp)
    (or (treeset::emptyp set)
        (and (treeset::subset (successors (treeset::min set) graph)
                              nodes)
             (set-all-successors-subsetp
               (treeset::delete (treeset::min set) set)
               nodes
               graph)))
    :measure (treeset::cardinality set)
    :hints (("Goal" :in-theory (enable o-p
                                       o-finp
                                       o<
                                       treeset::cardinality-of-delete-when-in
                                       treeset::in-of-min)))
    :verify-guards nil))

(defrulel set-all-successors-subsetp-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
           (equal (set-all-successors-subsetp set0 nodes graph)
                  (set-all-successors-subsetp set1 nodes graph)))
  :rule-classes :congruence
  :expand ((set-all-successors-subsetp set0 nodes graph)
           (set-all-successors-subsetp set1 nodes graph)))

(defrulel set-all-successors-subsetp-when-equiv-of-arg2-congruence
  (implies (treeset::equiv nodes0 nodes1)
           (equal (set-all-successors-subsetp set nodes0 graph)
                  (set-all-successors-subsetp set nodes1 graph)))
  :rule-classes :congruence
  :induct t
  :enable set-all-successors-subsetp)

(defrulel set-all-successors-subsetp-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (set-all-successors-subsetp set nodes graph0)
                  (set-all-successors-subsetp set nodes graph1)))
  :rule-classes :congruence
  :induct t
  :enable set-all-successors-subsetp)

(defrulel subset-of-successors-when-set-all-successors-subsetp-and-in
  (implies (and (set-all-successors-subsetp set nodes graph)
                (treeset::in x set))
           (treeset::subset (successors x graph) nodes))
  :use (:instance
         (:functional-instance
           treeset::genericp-when-set-all-genericp-and-in
           (treeset::genericp
             (lambda (x)
               (treeset::subset (successors x graph) nodes)))
           (treeset::set-all-genericp
             (lambda (set)
               (set-all-successors-subsetp set nodes graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-successors-subsetp)

(defrulel set-all-successors-subsetp-of-insert
  (equal (set-all-successors-subsetp (treeset::insert x set)
                                            nodes
                                            graph)
         (and (treeset::subset (successors x graph) nodes)
              (set-all-successors-subsetp set nodes graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-insert
           (treeset::genericp
             (lambda (x)
               (treeset::subset (successors x graph) nodes)))
           (treeset::set-all-genericp
             (lambda (set)
               (set-all-successors-subsetp set nodes graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-successors-subsetp)

(defrulel set-all-successors-subsetp-when-subset-of-arg2
  (implies (and (set-all-successors-subsetp set nodes0 graph)
                (treeset::subset nodes0 nodes1))
           (set-all-successors-subsetp set nodes1 graph))
  :induct t
  :enable set-all-successors-subsetp)

;; At least one step from a node whose successors are in a closed set ends in
;; that set.

(defrulel in-of-steps-end-when-set-all-successors-subsetp
  (implies (and (set-all-successors-subsetp set set graph)
                (treeset::subset (successors from graph) set)
                (consp steps)
                (treeset::subset (steps-edges from steps) (edges graph)))
           (treeset::in (steps-end from steps) set))
  :induct t
  :enable (steps-end
           steps-edges))

(defrulel in-when-reachablep-sk-and-set-all-successors-subsetp
  (implies (and (reachablep-sk from to graph)
                (treeset::subset (successors from graph) set)
                (set-all-successors-subsetp set set graph))
           (treeset::in to set))
  :use (:instance in-of-steps-end-when-set-all-successors-subsetp
                  (steps (walk->steps (reachablep-sk-witness from to graph))))
  :enable (reachablep-sk
           walk-in
           walk-end
           walk-edges)
  :disable in-of-steps-end-when-set-all-successors-subsetp)

;; One search step keeps every expanded or frontier node, and puts the
;; successors of the expanded node among them.

(defrulel subset-of-union-and-union-of-insert-and-union-of-delete
  (treeset::subset (treeset::union expanded frontier)
                   (treeset::union (treeset::insert node expanded)
                                   (treeset::union
                                     (treeset::delete node frontier)
                                     new)))
  :enable treeset::pick-a-point-polar)

(defrulel subset-of-arg1-and-union-of-insert-and-union-of-delete-of-diff
  (treeset::subset targets
                   (treeset::union (treeset::insert node expanded)
                                   (treeset::union
                                     frontier
                                     (treeset::delete
                                       node
                                       (treeset::diff targets expanded)))))
  :enable treeset::pick-a-point-polar)

(defrulel reachablep-search-when-reachablep-sk
  (implies (and (reachablep-sk from to graph)
                (treeset::subset (successors from graph)
                                 (treeset::union expanded frontier))
                (set-all-successors-subsetp
                  expanded
                  (treeset::union expanded frontier)
                  graph)
                (not (treeset::in to expanded)))
           (reachablep-search to frontier expanded graph))
  :induct t
  :enable (reachablep-search
           treeset::union-of-arg1-and-delete-when-in-arg1-cheap)
  :disable (treeset::union-of-insert
            treeset::commutativity-of-union
            treeset::commutativity-2-of-union
            treeset::union-of-arg1-and-diff
            treeset::union-of-arg1-and-delete-when-not-in-arg1-cheap))

(defruledl reachablep-when-reachablep-sk
  (implies (reachablep-sk from to graph)
           (reachablep from to graph))
  :enable (reachablep
           set-all-successors-subsetp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled reachablep-becomes-reachablep-sk
  (equal (reachablep from to graph)
         (reachablep-sk from to graph))
  :use (reachablep-sk-when-reachablep
        reachablep-when-reachablep-sk))

(defruled reachablep-sk-becomes-reachablep
  (equal (reachablep-sk from to graph)
         (reachablep from to graph))
  :by reachablep-becomes-reachablep-sk)
