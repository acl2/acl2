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
(include-book "kestrel/data/treemap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/bst" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/internal/split" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check that every key of one tree is a key of the other with at least the
;; same value. The second tree is split at the key of the first tree's head,
;; and each half is compared against the subtree of the first holding the same
;; keys.

(define tree-subbag-p ((x treemap::treep)
                       (y treemap::treep))
  :guard (and (tree-all-vals-posp x)
              (tree-all-vals-posp y))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (treemap::tree-empty-p x)
      (mv-let (assoc left right)
              (treemap::tree-split
                (treemap::tree-element->key (treemap::tree->head x))
                y)
        (and assoc
             (<= (treemap::tree-element->val (treemap::tree->head x))
                 (cdr assoc))
             (tree-subbag-p (treemap::tree->left x) left)
             (tree-subbag-p (treemap::tree->right x) right))))
  :measure (acl2-count x)
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp
                                           acl2::rationalp-when-posp))))

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-tree-key-set-when-tree-subbag-p
  (implies (and (tree-subbag-p x y)
                (treeset::in key (treemap::tree-key-set x))
                (treemap::bstp x)
                (treemap::bstp y))
           (treeset::in key (treemap::tree-key-set y)))
  :induct t
  :enable tree-subbag-p)

(defruled tree-lookup-<=-tree-lookup-when-tree-subbag-p
  (implies (and (tree-subbag-p x y)
                (treeset::in key (treemap::tree-key-set x))
                (treemap::bstp x)
                (treemap::bstp y))
           (<= (treemap::tree-lookup key x)
               (treemap::tree-lookup key y)))
  :induct t
  :enable tree-subbag-p)

;;;;;;;;;;;;;;;;;;;;

;; A key at which the check fails, when it fails.

(define tree-subbag-p-witness ((x treemap::treep)
                               (y treemap::treep))
  (if (treemap::tree-empty-p x)
      nil
    (mv-let (assoc left right)
            (treemap::tree-split
              (treemap::tree-element->key (treemap::tree->head x))
              y)
      (cond ((not (and assoc
                       (<= (treemap::tree-element->val (treemap::tree->head x))
                           (cdr assoc))))
             (treemap::tree-element->key (treemap::tree->head x)))
            ((not (tree-subbag-p (treemap::tree->left x) left))
             (tree-subbag-p-witness (treemap::tree->left x) left))
            (t (tree-subbag-p-witness (treemap::tree->right x) right)))))
  :measure (acl2-count x)
  :verify-guards nil)

(defruledl tree-subbag-p-when-holds-at-witness
  (implies (and (treemap::bstp x)
                (treemap::bstp y)
                (let ((key (tree-subbag-p-witness x y)))
                  (implies (treeset::in key (treemap::tree-key-set x))
                           (and (treeset::in key (treemap::tree-key-set y))
                                (<= (treemap::tree-lookup key x)
                                    (treemap::tree-lookup key y))))))
           (tree-subbag-p x y))
  :induct (tree-subbag-p-witness x y)
  :enable (tree-subbag-p
           tree-subbag-p-witness))

(defruled tree-subbag-p-pick-a-point
  (implies (and (treemap::bstp x)
                (treemap::bstp y))
           (equal (tree-subbag-p x y)
                  (let ((key (tree-subbag-p-witness x y)))
                    (implies (treeset::in key (treemap::tree-key-set x))
                             (and (treeset::in key (treemap::tree-key-set y))
                                  (<= (treemap::tree-lookup key x)
                                      (treemap::tree-lookup key y)))))))
  :cases ((tree-subbag-p x y))
  :enable (in-of-tree-key-set-when-tree-subbag-p
           tree-lookup-<=-tree-lookup-when-tree-subbag-p
           tree-subbag-p-when-holds-at-witness))
