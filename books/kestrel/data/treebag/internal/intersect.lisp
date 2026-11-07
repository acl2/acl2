; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/bst-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/heap-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/join-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/bst" :dir :system))
(local (include-book "kestrel/data/treemap/internal/heap" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/internal/join" :dir :system))
(local (include-book "kestrel/data/treemap/internal/split" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl tree-element-of-tree-element->key-and-tree-element->val
  (implies (treemap::tree-element-p elem)
           (equal (treemap::tree-element hash
                                         (treemap::tree-element->key elem)
                                         (treemap::tree-element->val elem))
                  elem))
  :use treemap::tree-element-elim)

(defruledl cons-of-hash-and-tree-search-assoc
  (implies (treemap::tree-search-assoc key tree)
           (equal (cons (treeset::hash key)
                        (treemap::tree-search-assoc key tree))
                  (treemap::tree-element
                    hash key (cdr (treemap::tree-search-assoc key tree)))))
  :enable treemap::tree-element)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keep each key of both trees with the lesser of its two values, and drop
;; every other key. The tree whose head comes first in heap order is the one
;; kept on top: the other tree is split at that head's key, and the halves are
;; intersected with the head's subtrees. When the head already holds the
;; lesser value, its node is reused.

(define tree-intersect ((x treemap::treep)
                        (y treemap::treep))
  :guard (and (tree-all-vals-posp x)
              (tree-all-vals-posp y))
  :returns (tree treemap::treep)
  (cond ((or (treemap::tree-empty-p x)
             (treemap::tree-empty-p y))
         nil)
        ((treemap::heap<-with-tree-element (treemap::tree->head x)
                                           (treemap::tree->head y))
         (mv-let (assoc left right)
                 (treemap::tree-split
                   (treemap::tree-element->key (treemap::tree->head y))
                   x)
           (let ((left (tree-intersect left (treemap::tree->left y)))
                 (right (tree-intersect right (treemap::tree->right y))))
             (if assoc
                 (mbe :logic
                      (treemap::tree-node
                        (treemap::tree-element
                          (treemap::tree-element->hash (treemap::tree->head y))
                          (treemap::tree-element->key (treemap::tree->head y))
                          (acl2::min (cdr assoc)
                                     (treemap::tree-element->val
                                       (treemap::tree->head y))))
                        left
                        right)
                      :exec
                      (if (<= (treemap::tree-element->val
                                (treemap::tree->head y))
                              (cdr assoc))
                          (treemap::tree-node-with-hint
                            (treemap::tree->head y) left right y)
                        (treemap::tree-node
                          (cons (treemap::tree-element->hash
                                  (treemap::tree->head y))
                                assoc)
                          left
                          right)))
               (mbe :logic (treemap::tree-join-at
                             (treemap::tree-element->key (treemap::tree->head y))
                             left
                             right)
                    :exec (treemap::tree-join left right))))))
        (t
         (mv-let (assoc left right)
                 (treemap::tree-split
                   (treemap::tree-element->key (treemap::tree->head x))
                   y)
           (let ((left (tree-intersect (treemap::tree->left x) left))
                 (right (tree-intersect (treemap::tree->right x) right)))
             (if assoc
                 (mbe :logic
                      (treemap::tree-node
                        (treemap::tree-element
                          (treemap::tree-element->hash (treemap::tree->head x))
                          (treemap::tree-element->key (treemap::tree->head x))
                          (acl2::min (treemap::tree-element->val
                                       (treemap::tree->head x))
                                     (cdr assoc)))
                        left
                        right)
                      :exec
                      (if (<= (treemap::tree-element->val
                                (treemap::tree->head x))
                              (cdr assoc))
                          (treemap::tree-node-with-hint
                            (treemap::tree->head x) left right x)
                        (treemap::tree-node
                          (cons (treemap::tree-element->hash
                                  (treemap::tree->head x))
                                assoc)
                          left
                          right)))
               (mbe :logic (treemap::tree-join-at
                             (treemap::tree-element->key (treemap::tree->head x))
                             left
                             right)
                    :exec (treemap::tree-join left right)))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp
                                           acl2::rationalp-when-posp
                                           acl2::min-when-<=-1
                                           acl2::min-when-<=-2
                                           treemap::tree-join-at
                                           tree-element-of-tree-element->key-and-tree-element->val
                                           cons-of-hash-and-tree-search-assoc))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-intersect-when-tree-equiv-of-arg1-congruence
  (implies (treemap::tree-equiv x0 x1)
           (equal (tree-intersect x0 y)
                  (tree-intersect x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

(defrule tree-intersect-when-tree-equiv-of-arg2-congruence
  (implies (treemap::tree-equiv y0 y1)
           (equal (tree-intersect x y0)
                  (tree-intersect x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-of-tree-intersect
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (equal (treeset::in key (treemap::tree-key-set (tree-intersect x y)))
                  (and (treeset::in key (treemap::tree-key-set x))
                       (treeset::in key (treemap::tree-key-set y)))))
  :induct t
  :enable (tree-intersect
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-intersect
  (implies (and (treemap::<<-all-l x z)
                (treemap::<<-all-l y z))
           (treemap::<<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule <<-all-r-of-arg1-and-tree-intersect
  (implies (and (treemap::<<-all-r z x)
                (treemap::<<-all-r z y))
           (treemap::<<-all-r z (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

(defrule bstp-of-tree-intersect-when-bstp
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (treemap::bstp (tree-intersect x y)))
  :induct t
  :enable tree-intersect)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-intersect
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (equal (treemap::tree-lookup key (tree-intersect x y))
                  (if (and (treeset::in key (treemap::tree-key-set x))
                           (treeset::in key (treemap::tree-key-set y)))
                      (acl2::min (treemap::tree-lookup key x)
                                 (treemap::tree-lookup key y))
                    nil)))
  :induct t
  :enable (tree-intersect
           treemap::tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-intersect
  (implies (and (treemap::heap<-all-l x z)
                (treemap::heap<-all-l y z))
           (treemap::heap<-all-l (tree-intersect x y) z))
  :induct t
  :enable tree-intersect)

(defrule heapp-of-tree-intersect-when-bstp-and-heapp
  (implies (and (treemap::bstp x)
                (treemap::bstp y)
                (treemap::heapp x)
                (treemap::heapp y))
           (treemap::heapp (tree-intersect x y)))
  :induct t
  :hints ('(:cases ((equal (treemap::tree-element->key (treemap::tree->head x))
                           (treemap::tree-element->key (treemap::tree->head y))))))
  :enable (tree-intersect
           treemap::heap<-all-l-extra-rules
           treemap::tree-split-extra-rules
           treemap::heap<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-posp-of-tree-intersect
  (implies (and (tree-all-vals-posp x)
                (tree-all-vals-posp y))
           (tree-all-vals-posp (tree-intersect x y)))
  :induct t
  :enable (tree-intersect
           tree-all-vals-posp
           acl2::min))
