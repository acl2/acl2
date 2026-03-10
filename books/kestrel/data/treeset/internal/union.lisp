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

(include-book "tree-defs")
(include-book "in-defs")
(include-book "count-defs")
(include-book "insert-defs")
(include-book "split-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "count"))
(local (include-book "insert"))
(local (include-book "split"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-union
  ((x treep)
   (y treep))
  :parents (implementation)
  :short "Take the union of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a union if the input trees are not binary search
      trees."))
  :returns (tree treep)
  (cond ((tree-empty-p x)
         (tree-fix y))
        ((tree-empty-p y)
         (tree-fix x))
        ((heap<-with-tagged-element (tree->head x) (tree->head y))
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head y)) x)
           (declare (ignore in))
           (tree-node (tree->head y)
                      (tree-union left (tree->left y))
                      (tree-union right (tree->right y)))))
        (t
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head x)) y)
           (declare (ignore in))
           (tree-node (tree->head x)
                      (tree-union (tree->left x) left)
                      (tree-union (tree->right x) right)))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-union-type-prescription
  (or (consp (tree-union x y))
      (equal (tree-union x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-union)

(defrule tree-union-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-union x0 z)
                  (tree-union x1 z)))
  :rule-classes :congruence
  :induct t
  :enable tree-union)

(defrule tree-union-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-union x y0)
                  (tree-union x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-union)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-union
  (equal (tree-empty-p (tree-union x y))
         (and (tree-empty-p x)
              (tree-empty-p y)))
  :induct t
  :enable tree-union)

(defrule tree-in-of-tree-union
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in a (tree-union x y))
                  (or (tree-in a x)
                      (tree-in a y))))
  :induct t
  :enable (tree-union
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-union
  (equal (<<-all-l (tree-union x y) z)
         (and (<<-all-l x z)
              (<<-all-l y z)))
  :induct t
  :enable (tree-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

(defrule <<-all-r-of-arg1-tree-union
  (equal (<<-all-r x (tree-union y z))
         (and (<<-all-r x y)
              (<<-all-r x z)))
  :induct t
  :enable (tree-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-union-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (bstp (tree-union x y)))
  :induct t
  :enable tree-union)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-union
  (equal (heap<-all-l (tree-union x y) z)
         (and (heap<-all-l x z)
              (heap<-all-l y z)))
  :induct t
  :enable (tree-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-union-when-heapp
  (implies (and (heapp x)
                (heapp y))
           (heapp (tree-union x y)))
  :induct t
  :hints ('(:cases ((equal (tagged-element->elem (tree->head x))
                           (tagged-element->elem (tree->head y))))))
  :enable (tree-union
           heap<-all-l-extra-rules
           tree-split-extra-rules
           heap<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-union
  ((x acl2-number-treep)
   (y acl2-number-treep))
  (mbe :logic (tree-union x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tagged-element (tree->head x) (tree->head y))
              (mv-let (in left right)
                      (acl2-number-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (tree-node (tree->head y)
                           (acl2-number-tree-union left (tree->left y))
                           (acl2-number-tree-union right (tree->right y)))))
             (t
              (mv-let (in left right)
                      (acl2-number-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (declare (ignore in))
                (tree-node (tree->head x)
                           (acl2-number-tree-union (tree->left x) left)
                           (acl2-number-tree-union (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-union
                                           acl2-number-tree-union
                                           tree-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-union
  ((x symbol-treep)
   (y symbol-treep))
  (mbe :logic (tree-union x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tagged-element (tree->head x) (tree->head y))
              (mv-let (in left right)
                      (symbol-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (tree-node (tree->head y)
                           (symbol-tree-union left (tree->left y))
                           (symbol-tree-union right (tree->right y)))))
             (t
              (mv-let (in left right)
                      (symbol-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (declare (ignore in))
                (tree-node (tree->head x)
                           (symbol-tree-union (tree->left x) left)
                           (symbol-tree-union (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-union
                                           symbol-tree-union
                                           tree-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-union
  ((x eqlable-treep)
   (y eqlable-treep))
  (mbe :logic (tree-union x y)
       :exec
       (cond ((tree-empty-p x)
              y)
             ((tree-empty-p y)
              x)
             ((heap<-with-tagged-element (tree->head x) (tree->head y))
              (mv-let (in left right)
                      (eqlable-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (tree-node (tree->head y)
                           (eqlable-tree-union left (tree->left y))
                           (eqlable-tree-union right (tree->right y)))))
             (t
              (mv-let (in left right)
                      (eqlable-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (declare (ignore in))
                (tree-node (tree->head x)
                           (eqlable-tree-union (tree->left x) left)
                           (eqlable-tree-union (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-union
                                           eqlable-tree-union
                                           tree-all-eqlablep))))
