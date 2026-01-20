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
(include-book "heap-order-defs")
(include-book "in-defs")
(include-book "join-defs")
(include-book "split-defs")
(include-book "subset-defs")
(include-book "union-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "heap-order"))
(local (include-book "in"))
(local (include-book "join"))
(local (include-book "split"))
(local (include-book "union"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-diff
  ((x treep)
   (y treep))
  :parents (implementation)
  :short "Take the difference of two treaps."
  :returns (tree treep)
  (cond ((or (tree-empty-p x)
             (tree-empty-p y))
         (tree-fix x))
        ((mbe :logic (heap< (tagged-element->elem (tree->head x))
                            (tagged-element->elem (tree->head y)))
              :exec (heap<-with-hashes (tagged-element->elem (tree->head x))
                                       (tagged-element->elem (tree->head y))
                                       (tagged-element->hash (tree->head x))
                                       (tagged-element->hash (tree->head y))))
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head y)) x)
           (declare (ignore in))
           (let ((left (tree-diff left (tree->left y)))
                 (right (tree-diff right (tree->right y))))
             (mbe :logic (tree-join-at (tagged-element->elem (tree->head y))
                                       left right)
                  :exec (tree-join left right)))))
        (t
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head x)) y)
           (let ((left (tree-diff (tree->left x) left))
                 (right (tree-diff (tree->right x) right)))
             (if in
                 (mbe :logic (tree-join-at (tagged-element->elem (tree->head x))
                                           left right)
                      :exec (tree-join left right))
               (tree-node (tree->head x) left right))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-diff)))

(defrule tree-diff-type-prescription
  (or (consp (tree-diff x y))
      (equal (tree-diff x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-diff)

(defrule tree-diff-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-diff x0 z)
                  (tree-diff x1 z)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

(defrule tree-diff-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-diff x y0)
                  (tree-diff x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-diff-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (tree-empty-p (tree-diff x y)))
  :enable tree-diff)

(defruled tree-diff-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (equal (tree-diff x y)
                  nil))
  :enable tree-diff)

(defrule tree-diff-when-tree-empty-p-of-arg1-cheap
  (implies (tree-empty-p x)
           (equal (tree-diff x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-diff-when-tree-empty-p-of-arg1)

(defrule tree-empty-p-of-tree-diff-when-tree-empty-p-of-arg2
  (implies (tree-empty-p y)
           (equal (tree-diff x y)
                  (tree-fix x)))
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-of-tree-diff
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in a (tree-diff x y))
                  (and (tree-in a x)
                       (not (tree-in a y)))))
  :induct t
  :enable (tree-diff
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-diff-when-<<-all-l-of-arg1
  (implies (<<-all-l x a)
           (<<-all-l (tree-diff x y) a))
  :induct t
  :enable tree-diff)

(defrule <<-all-r-of-arg1-and-tree-diff-when-bst-<-all-r-of-arg1-and-arg2
  (implies (<<-all-r a x)
           (<<-all-r a (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-diff-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (bstp (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-diff
  (implies (heap<-all-l x a)
           (heap<-all-l (tree-diff x y) a))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-diff-when-bstp-and-heapp
  (implies (and (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (heapp (tree-diff x y)))
  :induct t
  :enable tree-diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-acl2-numberp-of-tree-diff
  (implies (tree-all-acl2-numberp x)
           (tree-all-acl2-numberp (tree-diff x y)))
  :induct t
  :enable (tree-diff
           tree-all-acl2-numberp
           tree-join-at))

(defrule tree-all-symbolp-of-tree-diff
  (implies (tree-all-symbolp x)
           (tree-all-symbolp (tree-diff x y)))
  :induct t
  :enable (tree-diff
           tree-all-symbolp
           tree-join-at))

(defrule tree-all-eqlablep-of-tree-diff
  (implies (tree-all-eqlablep x)
           (tree-all-eqlablep (tree-diff x y)))
  :induct t
  :enable (tree-diff
           tree-all-eqlablep
           tree-join-at))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-diff
  ((x acl2-number-treep)
   (y acl2-number-treep))
  (mbe :logic (tree-diff x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              x)
             ((mbe :logic (heap< (tagged-element->elem (tree->head x))
                                 (tagged-element->elem (tree->head y)))
                   :exec (heap<-with-hashes
                           (tagged-element->elem (tree->head x))
                           (tagged-element->elem (tree->head y))
                           (tagged-element->hash (tree->head x))
                           (tagged-element->hash (tree->head y))))
              (mv-let (in left right)
                      (acl2-number-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (let ((left (acl2-number-tree-diff left (tree->left y)))
                      (right (acl2-number-tree-diff right (tree->right y))))
                  (tree-join left right))))
             (t
              (mv-let (in left right)
                      (acl2-number-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-diff (tree->left x) left))
                      (right (tree-diff (tree->right x) right)))
                  (if in
                      (tree-join left right)
                    (tree-node (tree->head x) left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-diff
                                           acl2-number-tree-diff
                                           tree-all-acl2-numberp
                                           tree-join-at))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-diff
  ((x symbol-treep)
   (y symbol-treep))
  (mbe :logic (tree-diff x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              x)
             ((mbe :logic (heap< (tagged-element->elem (tree->head x))
                                 (tagged-element->elem (tree->head y)))
                   :exec (heap<-with-hashes
                           (tagged-element->elem (tree->head x))
                           (tagged-element->elem (tree->head y))
                           (tagged-element->hash (tree->head x))
                           (tagged-element->hash (tree->head y))))
              (mv-let (in left right)
                      (symbol-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (let ((left (symbol-tree-diff left (tree->left y)))
                      (right (symbol-tree-diff right (tree->right y))))
                  (tree-join left right))))
             (t
              (mv-let (in left right)
                      (symbol-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-diff (tree->left x) left))
                      (right (tree-diff (tree->right x) right)))
                  (if in
                      (tree-join left right)
                    (tree-node (tree->head x) left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-diff
                                           symbol-tree-diff
                                           tree-all-symbolp
                                           tree-join-at))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-diff
  ((x eqlable-treep)
   (y eqlable-treep))
  (mbe :logic (tree-diff x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              x)
             ((mbe :logic (heap< (tagged-element->elem (tree->head x))
                                 (tagged-element->elem (tree->head y)))
                   :exec (heap<-with-hashes
                           (tagged-element->elem (tree->head x))
                           (tagged-element->elem (tree->head y))
                           (tagged-element->hash (tree->head x))
                           (tagged-element->hash (tree->head y))))
              (mv-let (in left right)
                      (eqlable-tree-split
                        (tagged-element->elem (tree->head y)) x)
                (declare (ignore in))
                (let ((left (eqlable-tree-diff left (tree->left y)))
                      (right (eqlable-tree-diff right (tree->right y))))
                  (tree-join left right))))
             (t
              (mv-let (in left right)
                      (eqlable-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-diff (tree->left x) left))
                      (right (tree-diff (tree->right x) right)))
                  (if in
                      (tree-join left right)
                    (tree-node (tree->head x) left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-diff
                                           eqlable-tree-diff
                                           tree-all-eqlablep
                                           tree-join-at))))
