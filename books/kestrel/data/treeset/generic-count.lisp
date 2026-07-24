; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; A generic count over treesets: given an element weight (the stub
; GENERIC-COUNT, constrained to a nat), TREE-GENERIC-COUNT is the structural
; fold (usable as a clique member since it recurs on the tree with an
; acl2-count measure) and SET-GENERIC-COUNT is the set-level wrapper (via the
; fix, like CARDINALITY / SET-ALL-ACL2-NUMBERP).  Concrete FTY counts obtain
; their machinery by functional instantiation of GENERIC-COUNT.
;
; This is the numeric-fold analogue of the GENERICP / SET-ALL-GENERICP
; recognizer development in generic-typed.lisp.

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/in-defs")
(include-book "internal/rotate-defs")
(include-book "internal/join-defs")
(include-book "internal/delete-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/rotate"))
(local (include-book "internal/join"))
(local (include-book "internal/delete"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap-order"))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "delete"))

;; TODO (nice-to-have): (local (include-book "internal/insert")) for the
;; insert version of the count lemmas.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic element weight (constrained to a nat), mirroring the genericp stub.

(encapsulate
  (((generic-count *) => *))
  (local (defun generic-count (x) (declare (ignore x)) 0))

  (defrule natp-of-generic-count
    (natp (generic-count x))
    :rule-classes (:rewrite :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Structural tree fold (clique member; acl2-count measure).  Node contributes
;; 1 + weight(element), so the fold = cardinality + sum of weights.

(define tree-generic-count ((tree treep))
  :returns (count natp :rule-classes :type-prescription)
  (if (tree-empty-p tree)
      0
    (+ 1
       (generic-count (tree-element->val (tree->head tree)))
       (tree-generic-count (tree->left tree))
       (tree-generic-count (tree->right tree)))))

(in-theory (disable (:t tree-generic-count)))

(defrule tree-generic-count-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-generic-count tree0)
                  (tree-generic-count tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-generic-count)

;; count = 0 iff empty (each node contributes at least 1); mirrors the
;; tree-nodes-count development, including the forward-chaining direction.
(defruled equal-of-tree-generic-count-and-0-becomes-tree-empty-p
  (equal (equal (tree-generic-count tree) 0)
         (tree-empty-p tree))
  :induct t
  :enable (tree-generic-count tree-empty-p acl2::fix))

(defrule tree-generic-count-when-tree-empty-p-forward-chaining
  (implies (tree-empty-p tree)
           (equal (tree-generic-count tree) 0))
  :rule-classes :forward-chaining
  :enable equal-of-tree-generic-count-and-0-becomes-tree-empty-p)

(defrule tree-empty-p-when-equal-tree-generic-count-and-0-forward-chaining
  (implies (equal (tree-generic-count tree) 0)
           (tree-empty-p tree))
  :rule-classes :forward-chaining
  :enable equal-of-tree-generic-count-and-0-becomes-tree-empty-p)

;; Invariance/behavior through the tree operations (mirror the tree-nodes-count
;; development across internal/rotate, internal/join, internal/delete):

;; A nonempty right subtree implies a nonempty tree, so only that hyp is
;; needed (cf. rotate-right-of-rotate-left-when-not-tree-empty-p-of-tree->right).
(defrule tree-generic-count-of-rotate-left
  (implies (not (tree-empty-p (tree->right tree)))
           (equal (tree-generic-count (rotate-left tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count rotate-left))

(defrule tree-generic-count-of-rotate-right
  (implies (not (tree-empty-p (tree->left tree)))
           (equal (tree-generic-count (rotate-right tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count rotate-right))

(defrule tree-generic-count-of-tree-join
  (equal (tree-generic-count (tree-join left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :induct t
  :enable (tree-generic-count tree-join acl2::fix))

(defrule tree-generic-count-of-tree-join-at
  (equal (tree-generic-count (tree-join-at split left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :enable (tree-generic-count tree-join-at))

(defrule tree-generic-count-of-tree-delete
  (implies (bstp tree)
           (equal (tree-generic-count (tree-delete x tree))
                  (if (tree-in x tree)
                      (- (tree-generic-count tree) (+ 1 (generic-count x)))
                    (tree-generic-count tree))))
  :induct (tree-delete x tree)
  :enable (tree-delete tree-generic-count bstp tree-in data::<<-rules acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Set-level count (thin wrapper on the fix, exactly like set-all-acl2-numberp
;; / cardinality).

(define set-generic-count ((set setp))
  :returns (count natp :rule-classes :type-prescription)
  (tree-generic-count (fix set))
  :guard-hints (("Goal" :in-theory (enable setp))))

(defruled set-generic-count-when-emptyp
  (implies (emptyp set)
           (equal (set-generic-count set) 0))
  :enable (set-generic-count emptyp))

(defrule set-generic-count-when-emptyp-cheap
  (implies (emptyp set)
           (equal (set-generic-count set) 0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-generic-count-when-emptyp)

(defrule set-generic-count-of-empty
  (equal (set-generic-count (empty)) 0)
  :enable set-generic-count-when-emptyp)

(defruled set-generic-count-of-delete
  (equal (set-generic-count (delete x set))
         (if (in x set)
             (- (set-generic-count set) (+ 1 (generic-count x)))
           (set-generic-count set)))
  :enable (set-generic-count delete in fix setp empty))

(defrule set-generic-count-of-delete-when-in
  (implies (in x set)
           (equal (set-generic-count (delete x set))
                  (- (set-generic-count set) (+ 1 (generic-count x)))))
  :use set-generic-count-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The client MEASURE contract: both directions strictly decrease.

;; Both bounds hold for any element in the set (mirroring the
;; <<-of-...-when-in family in min-max.lisp); min is then a corollary (max
;; would hold too, but is not currently needed).

(defrule generic-count-<-set-generic-count-when-in
  (implies (in x set)
           (< (generic-count x)
              (set-generic-count set)))
  :rule-classes :linear
  :use ((:instance set-generic-count-of-delete-when-in)
        (:instance natp-of-set-generic-count (set (delete x set))))
  :disable set-generic-count-of-delete-when-in)

(defrule set-generic-count-of-delete-<-set-generic-count-when-in
  (implies (in x set)
           (< (set-generic-count (delete x set))
              (set-generic-count set)))
  :rule-classes :linear
  :use (:instance set-generic-count-of-delete-when-in)
  :disable set-generic-count-of-delete-when-in)

(defrule generic-count-of-min-<-set-generic-count
  (implies (not (emptyp set))
           (< (generic-count (min set))
              (set-generic-count set)))
  :rule-classes :linear
  :use ((:instance generic-count-<-set-generic-count-when-in (x (min set)))
        (:instance in-of-min))
  :disable (generic-count-<-set-generic-count-when-in in-of-min))

(defrule set-generic-count-of-delete-min-<-set-generic-count
  (implies (not (emptyp set))
           (< (set-generic-count (delete (min set) set))
              (set-generic-count set)))
  :rule-classes :linear
  :use ((:instance set-generic-count-of-delete-<-set-generic-count-when-in
                   (x (min set)))
        (:instance in-of-min))
  :disable (set-generic-count-of-delete-<-set-generic-count-when-in in-of-min))
