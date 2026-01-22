; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/list-defs" :dir :system)
(include-book "kestrel/data/utilities/oset-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "count-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "union-defs")
(include-book "diff-defs")
(include-book "intersect-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/data/utilities/list" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "count"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "union"))
(local (include-book "diff"))
(local (include-book "intersect"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in-order-acc
  ((tree treep)
   (acc true-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  (if (tree-empty-p tree)
      (data::list-fix acc)
    (tree-in-order-acc (tree->left tree)
                       (cons (tagged-element->elem (tree->head tree))
                             (tree-in-order-acc (tree->right tree)
                                                acc)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-in-order-acc)))

(defrule tree-in-order-acc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-in-order-acc tree0 acc)
                  (tree-in-order-acc tree1 acc)))
  :rule-classes :congruence
  :induct t
  :enable tree-in-order-acc)

(defrule tree-in-order-acc-when-list-equiv-congruence
  (implies (list-equiv acc0 acc1)
           (equal (tree-in-order-acc tree acc0)
                  (tree-in-order-acc tree acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-in-order-acc)

(defrule tree-in-order-acc-of-append
  (implies (true-listp y)
           (equal (tree-in-order-acc tree (append x y))
                  (append (tree-in-order-acc tree x)
                          y)))
  :induct t
  :enable tree-in-order-acc)

(defruled tree-in-order-acc-arg2-becomes-nil
  (equal (tree-in-order-acc tree acc)
         (append (tree-in-order-acc tree nil)
                 (true-list-fix acc)))
  :use (:instance tree-in-order-acc-of-append
                  (x nil)
                  (y (true-list-fix acc)))
  :disable tree-in-order-acc-of-append)

(defruled tree-in-order-acc-arg2-becomes-nil-syntaxp
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (tree-in-order-acc tree acc)
                  (append (tree-in-order-acc tree nil)
                          (true-list-fix acc))))
  :by tree-in-order-acc-arg2-becomes-nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in-order
  ((tree treep))
  :returns (list true-listp :rule-classes :type-prescription)
  :parents (implementation)
  :short "Create an in-order list of values from a tree."
  (mbe :logic (if (tree-empty-p tree)
                  nil
                (append (tree-in-order (tree->left tree))
                        (cons (tagged-element->elem (tree->head tree))
                              (tree-in-order (tree->right tree)))))
       :exec (tree-in-order-acc tree nil))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-in-order)))

(defrule tree-in-order-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-in-order tree0)
                  (tree-in-order tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-in-order)

(defrule tree-in-order-acc-becomes-tree-in-order
  (equal (tree-in-order-acc tree acc)
         (append (tree-in-order tree)
                 (true-list-fix acc)))
  :induct t
  :enable (tree-in-order
           tree-in-order-acc
           tree-in-order-acc-arg2-becomes-nil-syntaxp))

(verify-guards tree-in-order
  :hints (("Goal" :in-theory (enable tree-in-order))))

(defrule consp-of-tree-in-order
  (equal (consp (tree-in-order tree))
         (and (tree-in-order tree) t)))

(defrule tree-in-order-under-iff
  (iff (tree-in-order tree)
       (not (tree-empty-p tree)))
  :induct t
  :enable tree-in-order)

(defrule car-of-tree-in-order
  (equal (car (tree-in-order tree))
         (tree-leftmost tree))
  :induct t
  :expand ((tree-in-order tree))
  :enable (tree-leftmost
           irr-tagged-element))

(defrule car-of-last-of-tree-in-order
  (equal (car (last (tree-in-order tree)))
         (tree-rightmost tree))
  :induct t
  :expand ((tree-in-order tree))
  :enable (tree-rightmost
           irr-tagged-element))

(defruled tree-in-order-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-in-order tree)
                  nil))
  :enable tree-in-order)

(defrule tree-in-order-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-in-order tree)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-in-order-when-tree-empty-p)

(defrule len-of-tree-in-order
  (equal (len (tree-in-order tree))
         (tree-nodes-count tree))
  :induct t
  :enable (tree-in-order
           tree-nodes-count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule osetp-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (set::setp (tree-in-order tree)))
  :induct t
  :hints ('(:cases ((tree-empty-p (tree->right tree)))))
  :enable (tree-in-order
           data::osetp-of-append
           data::osetp-of-cons))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl expand-in-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (set::in x (tree-in-order tree))
                  (and (not (tree-empty-p tree))
                       (or (equal x (tagged-element->elem (tree->head tree)))
                           (set::in x (tree-in-order (tree->left tree)))
                           (set::in x (tree-in-order (tree->right tree))))
                       t)))
  ;; TODO: Improve proof. Right now, this rule needs to be both used and
  ;; enabled, which is obviously fragile.
  :use osetp-of-tree-in-order-when-bstp
  :enable (set::in-to-member
           tree-in-order))

(defruled tree-in-order-definition-when-bstp
  (implies (bstp tree)
           (equal (tree-in-order tree)
                  (if (tree-empty-p tree)
                      nil
                    (set::insert
                      (tagged-element->elem (tree->head tree))
                      (set::union (tree-in-order (tree->left tree))
                                  (tree-in-order (tree->right tree)))))))
  :rule-classes :definition
  :enable (set::double-containment-no-backchain-limit
           set::pick-a-point-subset-strategy)

  :prep-lemmas
  ((defrule lemma0
     (implies (and (not (tree-empty-p tree))
                   (bstp tree)
                   (set::in x (tree-in-order tree)))
              (set::in x
                       (set::insert
                         (tagged-element->elem (tree->head tree))
                         (set::union (tree-in-order (tree->left tree))
                                     (tree-in-order (tree->right tree))))))
     :use expand-in-of-tree-in-order-when-bstp
     :enable tree-in-order)

   (defrule lemma1
     (implies (and (not (tree-empty-p tree))
                   (bstp tree)
                   (set::in x (set::insert
                                (tagged-element->elem (tree->head tree))
                                (set::union (tree-in-order (tree->left tree))
                                            (tree-in-order (tree->right tree))))))
              (set::in x (tree-in-order tree)))
     :use expand-in-of-tree-in-order-when-bstp
     :enable tree-in-order)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (set::in x (tree-in-order tree))
                  (tree-in x tree)))
  :induct t
  :enable (tree-in
           tree-in-order-definition-when-bstp))

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-tree-in-order-when-bstp
  (implies (bstp tree)
           (equal (set::cardinality (tree-in-order tree))
                  (tree-nodes-count tree)))
  :enable data::cardinality-becomes-len-when-osetp)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-order-of-tree-insert
  (implies (bstp tree)
           (equal (tree-in-order (mv-nth 1 (tree-insert x hash tree)))
                  (set::insert x (tree-in-order tree))))
  :use (:instance osetp-of-tree-in-order-when-bstp
                  (tree (mv-nth 1 (tree-insert x hash tree))))
  :enable set::expensive-rules
  :disable osetp-of-tree-in-order-when-bstp)

(defrule tree-in-order-of-tree-delete
  (implies (bstp tree)
           (equal (tree-in-order (tree-delete x tree))
                  (set::delete x (tree-in-order tree))))
  :use (:instance osetp-of-tree-in-order-when-bstp
                  (tree (tree-delete x tree)))
  :enable set::expensive-rules
  :disable osetp-of-tree-in-order-when-bstp)

(defrule tree-in-order-of-tree-union
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in-order (tree-union x y))
                  (set::union (tree-in-order x)
                              (tree-in-order y))))
  :use (:instance osetp-of-tree-in-order-when-bstp
                  (tree (tree-union x y)))
  :enable set::expensive-rules
  :disable osetp-of-tree-in-order-when-bstp)

(defrule tree-in-order-of-tree-diff
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in-order (tree-diff x y))
                  (set::difference (tree-in-order x)
                                   (tree-in-order y))))
  :use (:instance osetp-of-tree-in-order-when-bstp
                  (tree (tree-diff x y)))
  :enable set::expensive-rules
  :disable osetp-of-tree-in-order-when-bstp)

(defrule tree-in-order-of-tree-intersect
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in-order (tree-intersect x y))
                  (set::intersect (tree-in-order x)
                                  (tree-in-order y))))
  :use (:instance osetp-of-tree-in-order-when-bstp
                  (tree (tree-intersect x y)))
  :enable set::expensive-rules
  :disable osetp-of-tree-in-order-when-bstp)
