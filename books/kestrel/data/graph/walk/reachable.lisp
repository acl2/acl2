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
(include-book "../successors-defs")
(include-book "../predecessors-defs")
(include-book "walk-defs")
(include-book "walk-in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

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
(local (include-book "../successors"))
(local (include-book "../predecessors"))
(local (include-book "walk"))
(local (include-book "walk-in"))
(local (include-book "walk-snoc"))
(local (include-book "walk-append"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk reachable+p-sk (from to graph)
  :parents (reachable+p)
  :short "Check if there is a walk of at least one step from one node to
          another in a @(see graph)."
  :long
  (xdoc::topstring-p
    "This is the specification of @(tsee reachable+p), to which it is equal.
     It is not executable.")
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (exists (walk)
    (non-exec
      (and (walk-in walk graph)
           (equal (walk->start walk) from)
           (equal (walk-end walk) to)
           (consp (walk->steps walk))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t reachable+p-sk)))

(defrule reachable+p-sk-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (reachable+p-sk from to graph0)
                  (reachable+p-sk from to graph1)))
  :rule-classes :congruence
  :use ((:instance reachable+p-sk-suff
                   (walk (reachable+p-sk-witness from to graph0))
                   (graph graph1))
        (:instance reachable+p-sk-suff
                   (walk (reachable+p-sk-witness from to graph1))
                   (graph graph0)))
  :enable reachable+p-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Search for a node, expanding nodes from a frontier as @(tsee
;; successors+-search) does. The search succeeds when it takes the node it is
;; looking for from the frontier.

(define reachable+p-search
  (to
   (frontier treeset::setp)
   (expanded treeset::setp)
   (graph graphp))
  :returns (yes/no booleanp)
  :parents (reachable+p)
  (b* (((when (treeset::emptyp frontier))
        nil)
       (node (treeset::min frontier))
       ((when (equal node to))
        t)
       (frontier (treeset::delete node frontier))
       ((when (treeset::in node expanded))
        (reachable+p-search to frontier expanded graph))
       (expanded (treeset::insert node expanded)))
    (reachable+p-search to
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

(defrule reachable+p-search-when-equiv-of-arg2-congruence
  (implies (treeset::equiv frontier0 frontier1)
           (equal (reachable+p-search to frontier0 expanded graph)
                  (reachable+p-search to frontier1 expanded graph)))
  :rule-classes :congruence
  :expand ((reachable+p-search to frontier0 expanded graph)
           (reachable+p-search to frontier1 expanded graph)))

(defrule reachable+p-search-when-equiv-of-arg3-congruence
  (implies (treeset::equiv expanded0 expanded1)
           (equal (reachable+p-search to frontier expanded0 graph)
                  (reachable+p-search to frontier expanded1 graph)))
  :rule-classes :congruence
  :induct t
  :enable reachable+p-search)

(defrule reachable+p-search-when-equiv-of-arg4-congruence
  (implies (equiv graph0 graph1)
           (equal (reachable+p-search to frontier expanded graph0)
                  (reachable+p-search to frontier expanded graph1)))
  :rule-classes :congruence
  :induct t
  :enable reachable+p-search)

;; Until it takes the node it is looking for from the frontier, the search
;; steps as @(tsee successors+-search) does, so it finds the node exactly when
;; that search would expand it.

(defruledl reachable+p-search-becomes-in-of-successors+-search
  (implies (not (treeset::in to expanded))
           (equal (reachable+p-search to frontier expanded graph)
                  (treeset::in to
                               (successors+-search frontier expanded graph))))
  :induct (reachable+p-search to frontier expanded graph)
  :enable (reachable+p-search
           successors+-search))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reachable+p (from to (graph graphp))
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Check if there is a walk of at least one step from one node to
          another in a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the transitive closure of the edge relation, without the
       reflexive closure: a node reaches itself only if it is on a cycle. The
       @('+') in the name follows the usual notation @($R^+$) for the
       transitive closure of a relation @($R$). Logically it is membership in
       @(tsee successors+), and it equals @(tsee reachable+p-sk), which states
       the existence of the walk directly.")
    (xdoc::p
      "The search expands each node at most once and stops when it finds the
       target. Time complexity: @($O((n + m)\\log(n))$) in the worst case,
       where @($n$) is the number of nodes and @($m$) the number of pairs of
       nodes joined by an edge."))
  (mbe :logic (treeset::in to (successors+ from graph))
       :exec (reachable+p-search to
                                 (successors from graph)
                                 (treeset::empty)
                                 graph))
  :guard-hints
  (("Goal"
    :in-theory (enable successors+
                       reachable+p-search-becomes-in-of-successors+-search))))

;;;;;;;;;;;;;;;;;;;;

(defrule reachable+p-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (reachable+p from to graph0)
                  (reachable+p from to graph1)))
  :rule-classes :congruence
  :enable reachable+p)

;; Membership in the nodes reachable from a node is written as reachability.

(defrule in-of-successors+
  (equal (treeset::in to (successors+ from graph))
         (reachable+p from to graph))
  :enable reachable+p)

(theory-invariant (incompatible! (:definition reachable+p)
                                 (:rewrite in-of-successors+)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walks of one step, and joined walks

;; A successor of a node is the end of a one-step walk from it, along the
;; least label of the edges to the successor.

(defrulel reachable+p-sk-when-in-of-successors
  (implies (treeset::in to (successors from graph))
           (reachable+p-sk from to graph))
  :use (:instance reachable+p-sk-suff
                  (walk (walk-snoc (walk from nil)
                                   to
                                   (treeset::min (labels from to graph))))))

;; A walk to a node and a walk from it join into one walk.

(defrulel reachable+p-sk-transitivity
  (implies (and (reachable+p-sk from x graph)
                (reachable+p-sk x to graph))
           (reachable+p-sk from to graph))
  :use ((:instance reachable+p-sk-suff
                   (walk (walk-append (reachable+p-sk-witness from x graph)
                                      (reachable+p-sk-witness x to graph))))
        (:instance reachable+p-sk (to x))
        (:instance reachable+p-sk (from x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness: every node expanded or in the frontier is reachable, so every
;; node the search returns is.

(local
  (define set-all-reachable+p-sk (from (set treeset::setp) graph)
    :returns (yes/no booleanp)
    (or (treeset::emptyp set)
        (and (reachable+p-sk from (treeset::min set) graph)
             (set-all-reachable+p-sk from
                                     (treeset::delete (treeset::min set) set)
                                     graph)))
    :measure (treeset::cardinality set)
    :verify-guards nil))

(defrulel set-all-reachable+p-sk-when-equiv-of-arg2-congruence
  (implies (treeset::equiv set0 set1)
           (equal (set-all-reachable+p-sk from set0 graph)
                  (set-all-reachable+p-sk from set1 graph)))
  :rule-classes :congruence
  :expand ((set-all-reachable+p-sk from set0 graph)
           (set-all-reachable+p-sk from set1 graph)))

(defrulel set-all-reachable+p-sk-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (set-all-reachable+p-sk from set graph0)
                  (set-all-reachable+p-sk from set graph1)))
  :rule-classes :congruence
  :induct t
  :enable set-all-reachable+p-sk)

(defrulel reachable+p-sk-when-set-all-reachable+p-sk-and-in
  (implies (and (set-all-reachable+p-sk from set graph)
                (treeset::in x set))
           (reachable+p-sk from x graph))
  :use (:instance
         (:functional-instance
           treeset::genericp-when-set-all-genericp-and-in
           (treeset::genericp (lambda (x) (reachable+p-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-sk from set graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-sk)

(defrulel set-all-reachable+p-sk-of-insert
  (equal (set-all-reachable+p-sk from (treeset::insert x set) graph)
         (and (reachable+p-sk from x graph)
              (set-all-reachable+p-sk from set graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-insert
           (treeset::genericp (lambda (x) (reachable+p-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-sk from set graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-sk)

(defrulel set-all-reachable+p-sk-of-delete
  (implies (set-all-reachable+p-sk from set graph)
           (set-all-reachable+p-sk from (treeset::delete x set) graph))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-delete
           (treeset::genericp (lambda (x) (reachable+p-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-sk from set graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-sk)

(defrulel set-all-reachable+p-sk-of-union
  (equal (set-all-reachable+p-sk from (treeset::union x y) graph)
         (and (set-all-reachable+p-sk from x graph)
              (set-all-reachable+p-sk from y graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-union
           (treeset::genericp (lambda (x) (reachable+p-sk from x graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-sk from set graph))))
         (treeset::x x)
         (treeset::y y))
  :enable set-all-reachable+p-sk)

;; The successors of the start, and of any reachable node, are reachable.

(defrulel set-all-reachable+p-sk-when-subset-of-successors-of-arg1
  (implies (treeset::subset set (successors from graph))
           (set-all-reachable+p-sk from set graph))
  :induct t
  :enable set-all-reachable+p-sk)

(defruledl set-all-reachable+p-sk-when-subset-of-successors
  (implies (and (reachable+p-sk from x graph)
                (treeset::subset set (successors x graph)))
           (set-all-reachable+p-sk from set graph))
  :induct (set-all-reachable+p-sk from set graph)
  :enable set-all-reachable+p-sk)

(defrulel set-all-reachable+p-sk-of-diff-of-successors
  (implies (reachable+p-sk from x graph)
           (set-all-reachable+p-sk from
                                   (treeset::diff
                                     (successors x graph)
                                     set)
                                   graph))
  :enable set-all-reachable+p-sk-when-subset-of-successors)

(defrulel reachable+p-sk-when-in-of-successors+-search
  (implies (and (treeset::in to (successors+-search frontier expanded graph))
                (set-all-reachable+p-sk from frontier graph)
                (set-all-reachable+p-sk from expanded graph))
           (reachable+p-sk from to graph))
  :induct t
  :enable successors+-search)

(defruledl reachable+p-sk-when-reachable+p
  (implies (reachable+p from to graph)
           (reachable+p-sk from to graph))
  :enable (reachable+p
           successors+)
  :disable in-of-successors+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness: a set containing the successors of the start and the
;; successors of each of its own nodes contains every reachable node. The
;; nodes reachable from the start form such a set.

(defrulel subset-of-successors-when-subset-of-successors-of-set-and-in
  (implies (and (treeset::subset (successors-of-set set graph) y)
                (treeset::in x set))
           (treeset::subset (successors x graph) y))
  :use (:instance treeset::subset-transitivity
                  (x (successors x graph))
                  (y (successors-of-set set graph))
                  (z y))
  :disable treeset::subset-transitivity)

(defrulel in-of-steps-end-when-subset-of-successors-of-set
  (implies (and (treeset::subset (successors-of-set set graph) set)
                (treeset::subset (successors from graph) set)
                (consp steps)
                (treeset::subset (steps-edges from steps) (edges graph)))
           (treeset::in (steps-end from steps) set))
  :induct t
  :enable (steps-end
           steps-edges))

(defruledl in-when-reachable+p-sk-and-subset-of-successors-of-set
  (implies (and (reachable+p-sk from to graph)
                (treeset::subset (successors from graph) set)
                (treeset::subset (successors-of-set set graph) set))
           (treeset::in to set))
  :use (:instance in-of-steps-end-when-subset-of-successors-of-set
                  (steps (walk->steps (reachable+p-sk-witness from to graph))))
  :enable (reachable+p-sk
           walk-in
           walk-end
           walk-edges)
  :disable in-of-steps-end-when-subset-of-successors-of-set)

(defruledl reachable+p-when-reachable+p-sk
  (implies (reachable+p-sk from to graph)
           (reachable+p from to graph))
  :use (:instance in-when-reachable+p-sk-and-subset-of-successors-of-set
                  (set (successors+ from graph))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled reachable+p-becomes-reachable+p-sk
  (equal (reachable+p from to graph)
         (reachable+p-sk from to graph))
  :use (reachable+p-sk-when-reachable+p
        reachable+p-when-reachable+p-sk))

(defruled reachable+p-sk-becomes-reachable+p
  (equal (reachable+p-sk from to graph)
         (reachable+p from to graph))
  :by reachable+p-becomes-reachable+p-sk)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A successor is reachable, along an edge to it.

(defrule reachable+p-when-in-of-successors
  (implies (treeset::in to (successors from graph))
           (reachable+p from to graph))
  :enable reachable+p-becomes-reachable+p-sk)

;; Reachability is transitive.

(defrule reachable+p-transitivity
  (implies (and (reachable+p from x graph)
                (reachable+p x to graph))
           (reachable+p from to graph))
  :enable reachable+p-becomes-reachable+p-sk)

;; A set containing the successors of a node, and the successors of each of
;; its own nodes, contains every node reachable from it.

(defruled in-when-reachable+p-and-subset-of-successors-of-set
  (implies (and (reachable+p from to graph)
                (treeset::subset (successors from graph) set)
                (treeset::subset (successors-of-set set graph) set))
           (treeset::in to set))
  :enable (reachable+p-becomes-reachable+p-sk
           in-when-reachable+p-sk-and-subset-of-successors-of-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A set containing the predecessors of a node, and the predecessors of each
;; of its own nodes, contains every node from which it is reachable. Along a
;; walk, each node is a predecessor of the next, and the last step leaves a
;; predecessor of the end.

(defrulel in-when-subset-of-predecessors-of-set-and-in-of-predecessors
  (implies (and (treeset::subset (predecessors-of-set set graph) set)
                (treeset::in x set)
                (treeset::in from (predecessors x graph)))
           (treeset::in from set))
  :use (:instance treeset::subset-transitivity
                  (x (predecessors x graph))
                  (y (predecessors-of-set set graph))
                  (z set))
  :disable (in-of-predecessors
            treeset::subset-transitivity))

(defruledl in-of-start-when-subset-of-predecessors-of-set
  (implies (and (treeset::subset (predecessors-of-set set graph) set)
                (treeset::subset (predecessors (steps-end from steps) graph)
                                 set)
                (consp steps)
                (treeset::subset (steps-edges from steps) (edges graph)))
           (treeset::in from set))
  :induct (steps-end from steps)
  :enable (steps-end
           steps-edges))

(defruled in-when-reachable+p-and-subset-of-predecessors-of-set
  (implies (and (reachable+p from to graph)
                (treeset::subset (predecessors to graph) set)
                (treeset::subset (predecessors-of-set set graph) set))
           (treeset::in from set))
  :use (:instance in-of-start-when-subset-of-predecessors-of-set
                  (steps (walk->steps (reachable+p-sk-witness from to graph))))
  :enable (reachable+p-becomes-reachable+p-sk
           reachable+p-sk
           walk-in
           walk-end
           walk-edges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness of the predecessor search: every node expanded or in the frontier
;; reaches the node, so every node the search returns does.

(local
  (define set-all-reachable+p-to ((set treeset::setp) to graph)
    :returns (yes/no booleanp)
    (or (treeset::emptyp set)
        (and (reachable+p (treeset::min set) to graph)
             (set-all-reachable+p-to (treeset::delete (treeset::min set) set)
                                     to
                                     graph)))
    :measure (treeset::cardinality set)
    :verify-guards nil))

(defrulel set-all-reachable+p-to-when-equiv-of-arg1-congruence
  (implies (treeset::equiv set0 set1)
           (equal (set-all-reachable+p-to set0 to graph)
                  (set-all-reachable+p-to set1 to graph)))
  :rule-classes :congruence
  :expand ((set-all-reachable+p-to set0 to graph)
           (set-all-reachable+p-to set1 to graph)))

(defrulel set-all-reachable+p-to-when-equiv-of-arg3-congruence
  (implies (equiv graph0 graph1)
           (equal (set-all-reachable+p-to set to graph0)
                  (set-all-reachable+p-to set to graph1)))
  :rule-classes :congruence
  :induct t
  :enable set-all-reachable+p-to)

(defrulel reachable+p-when-set-all-reachable+p-to-and-in
  (implies (and (set-all-reachable+p-to set to graph)
                (treeset::in x set))
           (reachable+p x to graph))
  :use (:instance
         (:functional-instance
           treeset::genericp-when-set-all-genericp-and-in
           (treeset::genericp (lambda (x) (reachable+p x to graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-to set to graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-to)

(defrulel set-all-reachable+p-to-of-insert
  (equal (set-all-reachable+p-to (treeset::insert x set) to graph)
         (and (reachable+p x to graph)
              (set-all-reachable+p-to set to graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-insert
           (treeset::genericp (lambda (x) (reachable+p x to graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-to set to graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-to)

(defrulel set-all-reachable+p-to-of-delete
  (implies (set-all-reachable+p-to set to graph)
           (set-all-reachable+p-to (treeset::delete x set) to graph))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-delete
           (treeset::genericp (lambda (x) (reachable+p x to graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-to set to graph))))
         (treeset::set set)
         (treeset::x x))
  :enable set-all-reachable+p-to)

(defrulel set-all-reachable+p-to-of-union
  (equal (set-all-reachable+p-to (treeset::union x y) to graph)
         (and (set-all-reachable+p-to x to graph)
              (set-all-reachable+p-to y to graph)))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-of-union
           (treeset::genericp (lambda (x) (reachable+p x to graph)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-reachable+p-to set to graph))))
         (treeset::x x)
         (treeset::y y))
  :enable set-all-reachable+p-to)

;; The predecessors of the node, and of any node reaching it, reach it.

(defruledl reachable+p-when-in-of-predecessors
  (implies (treeset::in from (predecessors to graph))
           (reachable+p from to graph)))

(defruledl reachable+p-when-reachable+p-and-in-of-predecessors
  (implies (and (reachable+p x to graph)
                (treeset::in from (predecessors x graph)))
           (reachable+p from to graph))
  :use (:instance reachable+p-transitivity (x x))
  :disable reachable+p-transitivity)

(defrulel set-all-reachable+p-to-when-subset-of-predecessors-of-arg2
  (implies (treeset::subset set (predecessors to graph))
           (set-all-reachable+p-to set to graph))
  :induct t
  :enable (set-all-reachable+p-to
           reachable+p-when-in-of-predecessors)
  :disable in-of-predecessors)

(defruledl set-all-reachable+p-to-when-subset-of-predecessors
  (implies (and (reachable+p x to graph)
                (treeset::subset set (predecessors x graph)))
           (set-all-reachable+p-to set to graph))
  :induct (set-all-reachable+p-to set to graph)
  :enable (set-all-reachable+p-to
           reachable+p-when-reachable+p-and-in-of-predecessors)
  :disable in-of-predecessors)

(defrulel set-all-reachable+p-to-of-diff-of-predecessors
  (implies (reachable+p x to graph)
           (set-all-reachable+p-to (treeset::diff (predecessors x graph) set)
                                   to
                                   graph))
  :enable set-all-reachable+p-to-when-subset-of-predecessors)

(defrulel reachable+p-when-in-of-predecessors+-search
  (implies (and (treeset::in from
                            (predecessors+-search frontier expanded graph))
                (set-all-reachable+p-to frontier to graph)
                (set-all-reachable+p-to expanded to graph))
           (reachable+p from to graph))
  :induct t
  :enable predecessors+-search)

;; Membership in the nodes from which a node is reachable is written as
;; reachability.

(defrule in-of-predecessors+
  (equal (treeset::in from (predecessors+ to graph))
         (reachable+p from to graph))
  :use (:instance in-when-reachable+p-and-subset-of-predecessors-of-set
                  (set (predecessors+ to graph)))
  :enable predecessors+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy reachable-extra-rules
  '(in-when-reachable+p-and-subset-of-successors-of-set
    in-when-reachable+p-and-subset-of-predecessors-of-set))
