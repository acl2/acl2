; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "internal/rotate"))
(local (include-book "internal/join"))
(local (include-book "internal/delete"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap-order"))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "delete"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((generic-count *) => *))

  (local
    (define generic-count (x)
      (declare (ignore x))
      0))

  (defrule natp-of-generic-count-type-prescription
    (natp (generic-count x))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable generic-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-generic-count ((tree treep))
  :returns (count natp :rule-classes :type-prescription)
  (if (tree-empty-p tree)
      0
    (+ 1
       (generic-count (tree-element->val (tree->head tree)))
       (tree-generic-count (tree->left tree))
       (tree-generic-count (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-generic-count)))

(defrule tree-generic-count-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-generic-count tree0)
                  (tree-generic-count tree1)))
  :rule-classes :congruence
  :expand ((tree-generic-count tree0)
           (tree-generic-count tree1)))

(defruled equal-of-tree-generic-count-and-0-becomes-tree-empty-p
  (equal (equal (tree-generic-count tree) 0)
         (tree-empty-p tree))
  :induct t
  :enable (tree-generic-count
           tree-empty-p))

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

(defrule tree-generic-count-of-rotate-left
  (implies (not (tree-empty-p (tree->right tree)))
           (equal (tree-generic-count (rotate-left tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count
           rotate-left))

(defrule tree-generic-count-of-rotate-right
  (implies (not (tree-empty-p (tree->left tree)))
           (equal (tree-generic-count (rotate-right tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count
           rotate-right))

(defrule tree-generic-count-of-tree-join
  (equal (tree-generic-count (tree-join left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :induct t
  :enable (tree-generic-count
           tree-join))

(defrule tree-generic-count-of-tree-join-at
  (equal (tree-generic-count (tree-join-at split left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :enable (tree-generic-count
           tree-join-at))

(defrule tree-generic-count-of-tree-delete
  (implies (bstp tree)
           (equal (tree-generic-count (tree-delete x tree))
                  (if (tree-in x tree)
                      (- (tree-generic-count tree) (+ 1 (generic-count x)))
                    (tree-generic-count tree))))
  :induct t
  :enable (tree-delete
           tree-generic-count
           tree-in
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-generic-count ((set setp))
  :returns (count natp :rule-classes :type-prescription)
  (tree-generic-count (fix set))
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-generic-count)))

(defruled set-generic-count-when-emptyp
  (implies (emptyp set)
           (equal (set-generic-count set) 0))
  :enable (set-generic-count
           emptyp))

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
  :enable (set-generic-count
           delete
           in
           setp
           break-abstraction))

(defrule set-generic-count-of-delete-when-in
  (implies (in x set)
           (equal (set-generic-count (delete x set))
                  (- (set-generic-count set) (+ 1 (generic-count x)))))
  :use set-generic-count-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule generic-count-<-set-generic-count-when-in
  (implies (in x set)
           (< (generic-count x)
              (set-generic-count set)))
  :rule-classes :linear
  :use set-generic-count-of-delete-when-in
  :disable set-generic-count-of-delete-when-in)

(defrule set-generic-count-of-delete-<-set-generic-count-when-in
  (implies (in x set)
           (< (set-generic-count (delete x set))
              (set-generic-count set)))
  :rule-classes :linear
  :use set-generic-count-of-delete-when-in
  :disable set-generic-count-of-delete-when-in)

(defrule generic-count-of-min-<-set-generic-count
  (implies (not (emptyp set))
           (< (generic-count (min set))
              (set-generic-count set)))
  :rule-classes :linear
  :use (:instance generic-count-<-set-generic-count-when-in (x (min set)))
  :disable generic-count-<-set-generic-count-when-in)

(defrule set-generic-count-of-delete-min-<-set-generic-count
  (implies (not (emptyp set))
           (< (set-generic-count (delete (min set) set))
              (set-generic-count set)))
  :rule-classes :linear
  :use (:instance set-generic-count-of-delete-<-set-generic-count-when-in
                  (x (min set)))
  :disable set-generic-count-of-delete-<-set-generic-count-when-in)
