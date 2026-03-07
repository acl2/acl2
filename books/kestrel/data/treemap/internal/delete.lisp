; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/delete-defs" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "count-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "join-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "join"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-delete
  (key
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
        ((equal key (tree-element->key (tree->head tree)))
         (mbe :logic (tree-join-at (tree-element->key (tree->head tree))
                                   (tree->left tree)
                                   (tree->right tree))
              :exec (tree-join (tree->left tree)
                               (tree->right tree))))
        ((<< key (tree-element->key (tree->head tree)))
         ;; TODO: Return a flag indicating whether or not the subtree we
         ;; recursed on changed.
         (tree-node (tree->head tree)
                    (tree-delete key (tree->left tree))
                    (tree->right tree)))
        (t (tree-node (tree->head tree)
                      (tree->left tree)
                      (tree-delete key (tree->right tree)))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-delete)))

(defrule tree-delete-type-prescription
  (or (consp (tree-delete key tree))
      (equal (tree-delete key tree) nil))
  :rule-classes :type-prescription
  :use treep-of-tree-delete
  :disable treep-of-tree-delete)

(defrule tree-delete-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-delete key tree0)
                  (tree-delete key tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-delete)

;; Remove?
;; (defrule tree-empty-p-of-tree-delete-when-tree-empty-p
;;   (implies (tree-empty-p tree)
;;            (tree-empty-p (tree-delete key tree)))
;;   :enable tree-delete)

(defrule tree-delete-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-delete key tree)
                  nil))
  :enable tree-delete)

(defrule tree-key-set-of-tree-delete
  (implies (bstp tree)
           (equal (tree-key-set (tree-delete key tree))
                  (treeset::delete key (tree-key-set tree))))
  :induct t
  :enable (tree-delete
           tree-key-set
           treeset::union-of-arg1-and-delete-when-not-in-arg1))

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
           (bstp (tree-delete key tree)))
  :induct t
  :enable (tree-delete
           bstp
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-delete
  (implies (bstp tree)
           (equal (tree-lookup key0 (tree-delete key1 tree))
                  (if (equal key0 key1)
                      nil
                    (tree-lookup key0 tree))))
  :induct t
  :enable (tree-delete
           tree-lookup))

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
           (equal (tree-nodes-count (tree-delete key tree))
                  (if (treeset::in key (tree-key-set tree))
                      (- (tree-nodes-count tree) 1)
                    (tree-nodes-count tree))))
  :induct t
  :enable (tree-delete
           tree-nodes-count
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-delete
  ((key acl2-numberp)
   (tree acl2-number-treep))
  (mbe :logic (tree-delete key tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((= key (tree-element->key (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::acl2-number-<< key (tree-element->key (tree->head tree)))
              (tree-node (tree->head tree)
                         (acl2-number-tree-delete key (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (acl2-number-tree-delete key (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           acl2-number-tree-delete
                                           tree-keys-acl2-numberp
                                           tree-join-at))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-delete
  ((key symbolp)
   (tree symbol-treep))
  (mbe :logic (tree-delete key tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((eq key (tree-element->key (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::symbol-<< key (tree-element->key (tree->head tree)))
              (tree-node (tree->head tree)
                         (symbol-tree-delete key (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (symbol-tree-delete key (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           symbol-tree-delete
                                           tree-keys-symbolp
                                           tree-join-at))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-delete
  ((key eqlablep)
   (tree eqlable-treep))
  (mbe :logic (tree-delete key tree)
       :exec
       (cond ((tree-empty-p tree)
              nil)
             ((eql key (tree-element->key (tree->head tree)))
              (tree-join (tree->left tree)
                         (tree->right tree)))
             ((data::eqlable-<< key (tree-element->key (tree->head tree)))
              (tree-node (tree->head tree)
                         (eqlable-tree-delete key (tree->left tree))
                         (tree->right tree)))
             (t (tree-node (tree->head tree)
                           (tree->left tree)
                           (eqlable-tree-delete key (tree->right tree))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-delete
                                           eqlable-tree-delete
                                           tree-keys-eqlablep
                                           tree-join-at))))
