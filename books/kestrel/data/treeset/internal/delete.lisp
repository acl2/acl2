; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "count-defs")
(include-book "in-defs")
(include-book "join-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "in"))
(local (include-book "join"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-delete
  (x
   (tree treep))
  :parents (implementation)
  :short "Remove a value from the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The tree is expected to be a binary search tree. If it is not, the
      element @('x') intended to be deleted might outside the search path and
      thus remain in the tree.")
   (xdoc::p
     "After deletion, the tree is rebalanced with respect to the @(tsee
      heapp) property."))
  :returns (tree$ treep)
  (cond ((tree-empty-p tree)
         nil)
        ((equal x (tagged-element->elem (tree->head tree)))
         (mbe :logic (tree-join-at (tagged-element->elem (tree->head tree))
                                   (tree->left tree)
                                   (tree->right tree))
              :exec (tree-join (tree->left tree)
                               (tree->right tree))))
        ((<< x (tagged-element->elem (tree->head tree)))
         ;; TODO: Return a flag indicating whether or not the subtree we
         ;; recursed on changed.
         (tree-node (tree->head tree)
                    (tree-delete x (tree->left tree))
                    (tree->right tree)))
        (t (tree-node (tree->head tree)
                      (tree->left tree)
                      (tree-delete x (tree->right tree)))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-delete)))

(defrule tree-delete-type-prescription
  (or (consp (tree-delete x tree))
      (equal (tree-delete x tree) nil))
  :rule-classes :type-prescription
  :use treep-of-tree-delete
  :disable treep-of-tree-delete)

(defrule tree-delete-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-delete x tree0)
                  (tree-delete x tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-delete)

(defrule tree-empty-p-of-tree-delete-when-tree-empty-p
  (implies (tree-empty-p tree)
           (tree-empty-p (tree-delete x tree)))
  :enable tree-delete)

(defrule tree-in-of-tree-delete
  (implies (bstp tree)
           (equal (tree-in x (tree-delete y tree))
                  (and (not (equal x y))
                       (tree-in x tree))))
  :induct t
  :enable (tree-delete
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-delete
  (implies (<<-all-l tree y)
           (<<-all-l (tree-delete x tree) y))
  :induct t
  :enable (<<-all-l
           tree-delete))

(defrule <<-all-l-when-not-<<-all-l-of-tree-delete-forward-chaining
  (implies (not (<<-all-l (tree-delete y tree) x))
           (not (<<-all-l tree x)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-r-of-arg1-and-tree-delete
  (implies (<<-all-r x tree)
           (<<-all-r x (tree-delete y tree)))
  :induct t
  :enable (<<-all-r
           tree-delete))

(defrule <<-all-r-when-not-<<-all-r-of-arg1-and-tree-delete-forward-chaining
  (implies (not (<<-all-r x (tree-delete y tree)))
           (not (<<-all-r x tree)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-delete-when-bstp
  (implies (bstp tree)
           (bstp (tree-delete x tree)))
  :induct t
  :enable (tree-delete
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-delete
  (implies (heap<-all-l tree x)
           (heap<-all-l (tree-delete y tree) x))
  :induct t
  :enable (heap<-all-l
           tree-delete))

(defrule heap<-all-l-when-not-heap<-all-l-of-tree-delete-forward-chaining
  (implies (not (heap<-all-l (tree-delete y tree) x))
           (not (heap<-all-l tree x)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-delete
  (implies (and (heapp tree)
                (bstp tree))
           (heapp (tree-delete x tree)))
  :induct t
  :enable tree-delete)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-tree-delete
  (implies (bstp tree)
           (equal (tree-nodes-count (tree-delete x tree))
                  (if (tree-in x tree)
                      (- (tree-nodes-count tree) 1)
                    (tree-nodes-count tree))))
  :induct t
  :enable (tree-delete
           tree-nodes-count
           bstp
           data::<<-rules
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-delete
  ((x acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-delete x tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((= x (tagged-element->elem (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::acl2-number-<< x (tagged-element->elem (tree->head tree)))
              (tree-node (tree->head tree)
                         (tree-delete x (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (tree-delete x (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           tree-all-acl2-numberp
                                           tree-join-at))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-delete
  ((x symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-delete x tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((eq x (tagged-element->elem (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::symbol-<< x (tagged-element->elem (tree->head tree)))
              (tree-node (tree->head tree)
                         (tree-delete x (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (tree-delete x (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           tree-all-symbolp
                                           tree-join-at))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-delete
  ((x eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-delete x tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((eql x (tagged-element->elem (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::eqlable-<< x (tagged-element->elem (tree->head tree)))
              (tree-node (tree->head tree)
                         (tree-delete x (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (tree-delete x (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           tree-all-eqlablep
                                           tree-join-at))))
