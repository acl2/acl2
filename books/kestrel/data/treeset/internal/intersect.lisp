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
(include-book "join-defs")
(include-book "split-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../hash"))
(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap-order"))
(local (include-book "heap"))
(local (include-book "in"))
(local (include-book "join"))
(local (include-book "split"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-intersect
  ((x treep)
   (y treep))
  :parents (implementation)
  :short "Take the intersection of two treaps."
  :long
  (xdoc::topstring
   (xdoc::p
     "The result might not be a intersection if the input trees are not binary search
      trees."))
  :returns (tree treep)
  (cond ((or (tree-empty-p x)
             (tree-empty-p y))
         nil)
        ((mbe :logic (heap< (tagged-element->elem (tree->head x))
                            (tagged-element->elem (tree->head y)))
              :exec (heap<-with-hashes (tagged-element->elem (tree->head x))
                                       (tagged-element->elem (tree->head y))
                                       (tagged-element->hash (tree->head x))
                                       (tagged-element->hash (tree->head y))))
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head y)) x)
           (let ((left (tree-intersect left (tree->left y)))
                 (right (tree-intersect right (tree->right y))))
             (if in
                 (tree-node (tree->head y) left right)
               (mbe :logic (tree-join-at (tagged-element->elem (tree->head y))
                                         left right)
                    :exec (tree-join left right))))))
        (t
         (mv-let (in left right)
                 (tree-split (tagged-element->elem (tree->head x)) y)
           (let ((left (tree-intersect (tree->left x) left))
                 (right (tree-intersect (tree->right x) right)))
             (if in
                 (tree-node (tree->head x) left right)
               (mbe :logic (tree-join-at (tagged-element->elem (tree->head x))
                                         left right)
                    :exec (tree-join left right)))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-join-at))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-intersect)))

(defrule tree-intersect-type-prescription
  (or (consp (tree-intersect x y))
      (equal (tree-intersect x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-intersect)

(defrule tree-intersect-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-intersect x0 z)
                  (tree-intersect x1 z)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

(defrule tree-intersect-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-intersect x y0)
                  (tree-intersect x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-intersect-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (tree-empty-p (tree-intersect x y)))
  :enable tree-intersect)

(defrule tree-empty-p-of-tree-intersect-when-tree-empty-p-of-arg2
  (implies (tree-empty-p y)
           (tree-empty-p (tree-intersect x y)))
  :enable tree-intersect)

(defrule not-tree-intersect-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (not (tree-intersect x y)))
  :enable tree-intersect)

(defrule not-tree-intersect-when-tree-empty-p-of-arg2
  (implies (tree-empty-p y)
           (not (tree-intersect x y)))
  :enable tree-intersect)

(defrule tree-in-of-tree-intersect
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-in a (tree-intersect x y))
                  (and (tree-in a x)
                       (tree-in a y))))
  :induct t
  :enable (tree-intersect
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-intersect
  (implies (and (<<-all-l x z)
                (<<-all-l y z))
           (<<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule <<-all-r-of-arg1-and-tree-intersect
  (implies (and (<<-all-r x y)
                (<<-all-r x z))
           (<<-all-r x (tree-intersect y z)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-intersect-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (bstp (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-intersect
  (implies (and (heap<-all-l x z)
                (heap<-all-l y z))
           (heap<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-intersect-when-bstp-and-heapp
  (implies (and (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (heapp (tree-intersect x y)))
  :induct t
  :enable (tree-intersect
           tree->head-when-heapp-and-tree-in-tree->head-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO GJ
;; (And consider sk rules)
;; (defrule tree-all-acl2-numberp-of-tree-intersect-when-tree-all-acl2-numberp-of-arg1
;;   (implies (tree-all-acl2-numberp x)
;;            (tree-all-acl2-numberp (tree-intersect x y)))
;;   :induct t
;;   :enable (tree-intersect
;;            tree-all-acl2-numberp
;;            tree-join-at))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-intersect
  ((x acl2-number-treep)
   (y acl2-number-treep))
  (mbe :logic (tree-intersect x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              nil)
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
                (let ((left (tree-intersect left (tree->left y)))
                      (right (tree-intersect right (tree->right y))))
                  (if in
                      (tree-node (tree->head y) left right)
                    (tree-join left right)))))
             (t
              (mv-let (in left right)
                      (acl2-number-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-intersect (tree->left x) left))
                      (right (tree-intersect (tree->right x) right)))
                  (if in
                      (tree-node (tree->head x) left right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-join-at
                                           tree-intersect
                                           tree-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-intersect
  ((x symbol-treep)
   (y symbol-treep))
  (mbe :logic (tree-intersect x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              nil)
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
                (let ((left (tree-intersect left (tree->left y)))
                      (right (tree-intersect right (tree->right y))))
                  (if in
                      (tree-node (tree->head y) left right)
                    (tree-join left right)))))
             (t
              (mv-let (in left right)
                      (symbol-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-intersect (tree->left x) left))
                      (right (tree-intersect (tree->right x) right)))
                  (if in
                      (tree-node (tree->head x) left right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-join-at
                                           tree-intersect
                                           tree-all-symbolp))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-intersect
  ((x eqlable-treep)
   (y eqlable-treep))
  (mbe :logic (tree-intersect x y)
       :exec
       (cond ((or (tree-empty-p x)
                  (tree-empty-p y))
              nil)
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
                (let ((left (tree-intersect left (tree->left y)))
                      (right (tree-intersect right (tree->right y))))
                  (if in
                      (tree-node (tree->head y) left right)
                    (tree-join left right)))))
             (t
              (mv-let (in left right)
                      (eqlable-tree-split
                        (tagged-element->elem (tree->head x)) y)
                (let ((left (tree-intersect (tree->left x) left))
                      (right (tree-intersect (tree->right x) right)))
                  (if in
                      (tree-node (tree->head x) left right)
                    (tree-join left right)))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-join-at
                                           tree-intersect
                                           tree-all-eqlablep))))
