; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "count-defs")
(include-book "in-defs")
(include-book "min-max-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "count"))
(local (include-book "in"))
(local (include-book "min-max"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rotations
  :parents (implementation)
  :short "Left and right tree rotations."
  ;;      x         left rotation →         y
  ;;    ↙   ↘       ← right rotation      ↙   ↘
  ;;  a       y                         x       c
  ;;        ↙   ↘                     ↙   ↘
  ;;      b       c                 a       b
  :long
  (xdoc::topstring
    (xdoc::p
      "Rotations preserve the binary search tree property while rotating up the
       head of one or the other subtrees."))
  :set-as-default-parent t

  (define rotate-left
    ((tree treep))
    :short "Perform a left tree rotation."
    :long
    (xdoc::topstring
     (xdoc::p
       "When the right subtree is empty (contrary to the guard), we logically
        just return the tree."))
    :guard (not (tree-empty-p (tree->right tree)))
    :returns (tree$ treep)
    (if (mbt (not (tree-empty-p (tree->right tree))))
        (tree-node (tree->head (tree->right tree))
                   (tree-node (tree->head tree)
                              (tree->left tree)
                              (tree->left (tree->right tree)))
                   (tree->right (tree->right tree)))
      (tree-fix tree))
    :inline t)

  (define rotate-right
    ((tree treep))
    :short "Perform a right tree rotation."
    :long
    (xdoc::topstring
     (xdoc::p
       "When the left subtree is empty (contrary to the guard), we logically
        just return the tree."))
    :guard (not (tree-empty-p (tree->left tree)))
    :returns (tree$ treep)
    (if (mbt (not (tree-empty-p (tree->left tree))))
        (tree-node (tree->head (tree->left tree))
                   (tree->left (tree->left tree))
                   (tree-node (tree->head tree)
                              (tree->right (tree->left tree))
                              (tree->right tree)))
      (tree-fix tree))
    :inline t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rotate-left-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (rotate-left x)
                  (rotate-left y)))
  :rule-classes :congruence
  :enable (tree-equiv
           rotate-left))

(defrule rotate-right-when-tree-equiv-congruence
  (implies (tree-equiv x y)
           (equal (rotate-right x)
                  (rotate-right y)))
  :rule-classes :congruence
  :enable (tree-equiv
           rotate-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rotate-left-of-rotate-right-when-not-tree-empty-p-of-tree->left
  (implies (not (tree-empty-p (tree->left tree)))
           (equal (rotate-left (rotate-right tree))
                  tree))
  :enable (rotate-left
           rotate-right))

(defrule rotate-right-of-rotate-left-when-not-tree-empty-p-of-tree->right
  (implies (not (tree-empty-p (tree->right tree)))
           (equal (rotate-right (rotate-left tree))
                  tree))
  :enable (rotate-right
           rotate-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-rotate-left
  (equal (tree-empty-p (rotate-left tree))
         (tree-empty-p tree))
  :enable rotate-left)

(defrule tree-empty-p-of-rotate-right
  (equal (tree-empty-p (rotate-right tree))
         (tree-empty-p tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-rotate-left
  (equal (tree-in x (rotate-left tree))
         (tree-in x tree))
  :enable rotate-left)

(defrule tree-in-of-rotate-right
  (equal (tree-in x (rotate-right tree))
         (tree-in x tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree->head-of-rotate-left
  (equal (tree->head (rotate-left tree))
         (if (tree-empty-p (tree->right tree))
             (tree->head tree)
           (tree->head (tree->right tree))))
  :enable rotate-left)

(defrule tree->head-of-rotate-right
  (equal (tree->head (rotate-right tree))
         (if (tree-empty-p (tree->left tree))
             (tree->head tree)
           (tree->head (tree->left tree))))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree->left-of-rotate-left
  (equal (tree->left (rotate-left tree))
         (if (tree-empty-p (tree->right tree))
             (tree->left tree)
           (tree-node (tree->head tree)
                      (tree->left tree)
                      (tree->left (tree->right tree)))))
  :enable rotate-left)

(defrule tree->left-of-rotate-right
  (equal (tree->left (rotate-right tree))
         (if (tree-empty-p (tree->left tree))
             (tree->left tree)
           (tree->left (tree->left tree))))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree->right-of-rotate-left
  (equal (tree->right (rotate-left tree))
         (if (tree-empty-p (tree->right tree))
             (tree->right tree)
           (tree->right (tree->right tree))))
  :enable rotate-left)

(defrule tree->right-of-rotate-right
  (equal (tree->right (rotate-right tree))
         (if (tree-empty-p (tree->left tree))
             (tree->right tree)
           (tree-node (tree->head tree)
                      (tree->right (tree->left tree))
                      (tree->right tree))))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-rotate-left
  (equal (<<-all-l (rotate-left tree) x)
         (<<-all-l tree x))
  :enable rotate-left)

(defrule <<-all-l-of-rotate-right
  (equal (<<-all-l (rotate-right tree) x)
         (<<-all-l tree x))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-r-of-arg1-and-rotate-left
  (equal (<<-all-r x (rotate-left tree))
         (<<-all-r x tree))
  :enable rotate-left)

(defrule <<-all-r-of-arg1-and-rotate-right
  (equal (<<-all-r x (rotate-right tree))
         (<<-all-r x tree))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-rotate-left
  (equal (heap<-all-l (rotate-left tree) x)
         (heap<-all-l tree x))
  :enable rotate-left)

(defrule heap<-all-l-of-rotate-right
  (equal (heap<-all-l (rotate-right tree) x)
         (heap<-all-l tree x))
  :enable rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-rotate-left
  (equal (bstp (rotate-left tree))
         (bstp tree))
  :enable (rotate-left
           <<-all-extra-rules))

(defrule bstp-of-rotate-right
  (equal (bstp (rotate-right tree))
         (bstp tree))
  :enable (rotate-right
           <<-all-extra-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-rotate-left
  (equal (heapp (rotate-left tree))
         (if (tree-empty-p (tree->right tree))
             (heapp tree)
           (and (heapp (tree->left tree))
                (heapp (tree->left (tree->right tree)))
                (heapp (tree->right (tree->right tree)))
                (heap< (tagged-element->elem (tree->head tree))
                       (tagged-element->elem (tree->head (tree->right tree))))
                (heap<-all-l (tree->left tree)
                             (tagged-element->elem (tree->head tree)))
                (heap<-all-l (tree->left (tree->right tree))
                             (tagged-element->elem (tree->head tree)))
                (heap<-all-l (tree->left (tree->right tree))
                             (tagged-element->elem (tree->head (tree->right tree))))
                (heap<-all-l (tree->right (tree->right tree))
                             (tagged-element->elem (tree->head (tree->right tree)))))))
  :enable (rotate-left
           heap<-all-l-extra-rules))

(defrule heapp-of-rotate-left-when-not-tree-empty-p-of-tree->right
  (implies (not (tree-empty-p (tree->right tree)))
           (equal (heapp (rotate-left tree))
                  (and (heapp (tree->left tree))
                       (heapp (tree->left (tree->right tree)))
                       (heapp (tree->right (tree->right tree)))
                       (heap< (tagged-element->elem (tree->head tree))
                              (tagged-element->elem (tree->head (tree->right tree))))
                       (heap<-all-l (tree->left tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->left (tree->right tree))
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->left (tree->right tree))
                                    (tagged-element->elem (tree->head (tree->right tree))))
                       (heap<-all-l (tree->right (tree->right tree))
                                    (tagged-element->elem (tree->head (tree->right tree)))))))
  :enable heapp-of-rotate-left)

;;;;;;;;;;;;;;;;;;;;

(defruled heapp-of-rotate-right
  (equal (heapp (rotate-right tree))
         (if (tree-empty-p (tree->left tree))
             (heapp tree)
           (and (heapp (tree->right tree))
                (heapp (tree->left (tree->left tree)))
                (heapp (tree->right (tree->left tree)))
                (heap< (tagged-element->elem (tree->head tree))
                       (tagged-element->elem (tree->head (tree->left tree))))
                (heap<-all-l (tree->right tree)
                             (tagged-element->elem (tree->head tree)))
                (heap<-all-l (tree->right (tree->left tree))
                             (tagged-element->elem (tree->head tree)))
                (heap<-all-l (tree->left (tree->left tree))
                             (tagged-element->elem (tree->head (tree->left tree))))
                (heap<-all-l (tree->right (tree->left tree))
                             (tagged-element->elem (tree->head (tree->left tree)))))))
  :enable (rotate-right
           heap<-all-l-extra-rules))

(defrule heapp-of-rotate-right-when-not-tree-empty-p-of-tree->left
  (implies (not (tree-empty-p (tree->left tree)))
           (equal (heapp (rotate-right tree))
                  (and (heapp (tree->right tree))
                       (heapp (tree->left (tree->left tree)))
                       (heapp (tree->right (tree->left tree)))
                       (heap< (tagged-element->elem (tree->head tree))
                              (tagged-element->elem (tree->head (tree->left tree))))
                       (heap<-all-l (tree->right tree)
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->right (tree->left tree))
                                    (tagged-element->elem (tree->head tree)))
                       (heap<-all-l (tree->left (tree->left tree))
                                    (tagged-element->elem (tree->head (tree->left tree))))
                       (heap<-all-l (tree->right (tree->left tree))
                                    (tagged-element->elem (tree->head (tree->left tree)))))))
  :enable heapp-of-rotate-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-nodes-count-of-rotate-left
  (equal (tree-nodes-count (rotate-left tree))
         (tree-nodes-count tree))
  :enable (tree-nodes-count
           rotate-left))

(defrule tree-nodes-count-of-rotate-right
  (equal (tree-nodes-count (rotate-right tree))
         (tree-nodes-count tree))
  :enable (tree-nodes-count
           rotate-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-min-of-rotate-left
  (equal (tree-min (rotate-left tree))
         (tree-min tree))
  :enable (rotate-left
           tree-min))

(defrule tree-min-of-rotate-right
  (equal (tree-min (rotate-right tree))
         (tree-min tree))
  :enable (rotate-right
           tree-min))
