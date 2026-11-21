; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)

(include-book "kestrel/data/tmap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/bst-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/heap-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/join-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))

(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/bst" :dir :system))
(local (include-book "kestrel/data/tmap/internal/heap" :dir :system))
(local (include-book "kestrel/data/tmap/internal/keys" :dir :system))
(local (include-book "kestrel/data/tmap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/internal/join" :dir :system))
(local (include-book "kestrel/data/tmap/internal/split" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl tree-element-of-tree-element->key-and-tree-element->val
  (implies (tmap::tree-element-p elem)
           (equal (tmap::tree-element hash
                                      (tmap::tree-element->key elem)
                                      (tmap::tree-element->val elem))
                  elem))
  :use tmap::tree-element-elim)

(defruledl cons-of-hash-and-tree-search-assoc
  (implies (tmap::tree-search-assoc key tree)
           (equal (cons (tset::hash key)
                        (tmap::tree-search-assoc key tree))
                  (tmap::tree-element
                    hash key (cdr (tmap::tree-search-assoc key tree)))))
  :enable tmap::tree-element)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keep each key of both trees with the lesser of its two values, and drop
;; every other key. The tree whose head comes first in heap order is the one
;; kept on top: the other tree is split at that head's key, and the halves are
;; intersected with the head's subtrees. When the head already holds the
;; lesser value, its node is reused.

(define tree-intersect ((x tmap::treep)
                        (y tmap::treep))
  :guard (and (tree-all-vals-posp x)
              (tree-all-vals-posp y))
  :returns (tree tmap::treep)
  (cond ((or (tmap::tree-empty-p x)
             (tmap::tree-empty-p y))
         nil)
        ((tmap::heap<-with-tree-element (tmap::tree->head x)
                                        (tmap::tree->head y))
         (mv-let (assoc left right)
                 (tmap::tree-split
                   (tmap::tree-element->key (tmap::tree->head y))
                   x)
           (let ((left (tree-intersect left (tmap::tree->left y)))
                 (right (tree-intersect right (tmap::tree->right y))))
             (if assoc
                 (mbe :logic
                      (tmap::tree-node
                        (tmap::tree-element
                          (tmap::tree-element->hash (tmap::tree->head y))
                          (tmap::tree-element->key (tmap::tree->head y))
                          (acl2::min (cdr assoc)
                                     (tmap::tree-element->val
                                       (tmap::tree->head y))))
                        left
                        right)
                      :exec
                      (if (<= (tmap::tree-element->val
                                (tmap::tree->head y))
                              (cdr assoc))
                          (tmap::tree-node-with-hint
                            (tmap::tree->head y) left right y)
                        (tmap::tree-node
                          (cons (tmap::tree-element->hash
                                  (tmap::tree->head y))
                                assoc)
                          left
                          right)))
               (mbe :logic (tmap::tree-join-at
                             (tmap::tree-element->key (tmap::tree->head y))
                             left
                             right)
                    :exec (tmap::tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (tmap::tree-split
                   (tmap::tree-element->key (tmap::tree->head x))
                   y)
           (let ((left (tree-intersect (tmap::tree->left x) left))
                 (right (tree-intersect (tmap::tree->right x) right)))
             (if assoc
                 (mbe :logic
                      (tmap::tree-node
                        (tmap::tree-element
                          (tmap::tree-element->hash (tmap::tree->head x))
                          (tmap::tree-element->key (tmap::tree->head x))
                          (acl2::min (tmap::tree-element->val
                                       (tmap::tree->head x))
                                     (cdr assoc)))
                        left
                        right)
                      :exec
                      (if (<= (tmap::tree-element->val
                                (tmap::tree->head x))
                              (cdr assoc))
                          (tmap::tree-node-with-hint
                            (tmap::tree->head x) left right x)
                        (tmap::tree-node
                          (cons (tmap::tree-element->hash
                                  (tmap::tree->head x))
                                assoc)
                          left
                          right)))
               (mbe :logic (tmap::tree-join-at
                             (tmap::tree-element->key (tmap::tree->head x))
                             left
                             right)
                    :exec (tmap::tree-join left right)))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp
                                           acl2::rationalp-when-posp
                                           acl2::min-when-<=-1
                                           acl2::min-when-<=-2
                                           tmap::tree-join-at
                                           tree-element-of-tree-element->key-and-tree-element->val
                                           cons-of-hash-and-tree-search-assoc))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-intersect-when-tree-equiv-of-arg1-congruence
  (implies (tmap::tree-equiv x0 x1)
           (equal (tree-intersect x0 y)
                  (tree-intersect x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

(defrule tree-intersect-when-tree-equiv-of-arg2-congruence
  (implies (tmap::tree-equiv y0 y1)
           (equal (tree-intersect x y0)
                  (tree-intersect x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-of-tree-intersect
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (equal (tset::in key (tmap::tree-key-set (tree-intersect x y)))
                  (and (tset::in key (tmap::tree-key-set x))
                       (tset::in key (tmap::tree-key-set y)))))
  :induct t
  :enable (tree-intersect
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-intersect
  (implies (and (tmap::<<-all-l x z)
                (tmap::<<-all-l y z))
           (tmap::<<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule <<-all-r-of-arg1-and-tree-intersect
  (implies (and (tmap::<<-all-r z x)
                (tmap::<<-all-r z y))
           (tmap::<<-all-r z (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

(defrule bstp-of-tree-intersect-when-bstp
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (tmap::bstp (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-intersect
  (implies (and (tmap::bstp x)
                (tmap::bstp y))
           (equal (tmap::tree-lookup key (tree-intersect x y))
                  (if (and (tset::in key (tmap::tree-key-set x))
                           (tset::in key (tmap::tree-key-set y)))
                      (acl2::min (tmap::tree-lookup key x)
                                 (tmap::tree-lookup key y))
                    nil)))
  :induct t
  :enable (tree-intersect
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-intersect
  (implies (and (tmap::heap<-all-l x z)
                (tmap::heap<-all-l y z))
           (tmap::heap<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule heapp-of-tree-intersect-when-bstp-and-heapp
  (implies (and (tmap::bstp x)
                (tmap::bstp y)
                (tmap::heapp x)
                (tmap::heapp y))
           (tmap::heapp (tree-intersect x y)))
  :induct t
  :hints ('(:cases ((equal (tmap::tree-element->key (tmap::tree->head x))
                           (tmap::tree-element->key (tmap::tree->head y))))))
  :enable (tree-intersect
           tmap::heap<-all-l-extra-rules
           tmap::tree-split-extra-rules
           tmap::heap<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-posp-of-tree-intersect
  (implies (and (tree-all-vals-posp x)
                (tree-all-vals-posp y))
           (tree-all-vals-posp (tree-intersect x y)))
  :induct t
  :enable (tree-intersect
           tree-all-vals-posp
           acl2::min))
