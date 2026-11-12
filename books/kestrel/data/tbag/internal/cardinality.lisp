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
(include-book "kestrel/data/tmap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/rotate-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/join-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/update-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/delete-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/bst" :dir :system))
(local (include-book "kestrel/data/tmap/internal/heap" :dir :system))
(local (include-book "kestrel/data/tmap/internal/keys" :dir :system))
(local (include-book "kestrel/data/tmap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/internal/rotate" :dir :system))
(local (include-book "kestrel/data/tmap/internal/join" :dir :system))
(local (include-book "kestrel/data/tmap/internal/update" :dir :system))
(local (include-book "kestrel/data/tmap/internal/delete" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The cardinality of a bag's tree: the sum of the multiplicities at its nodes.

(define tree-cardinality ((tree tmap::treep))
  :type-prescription :none
  :guard (tree-all-vals-posp tree)
  :returns (cardinality natp :rule-classes :type-prescription)
  (if (tmap::tree-empty-p tree)
      0
    (+ (lnfix (tmap::tree-element->val (tmap::tree->head tree)))
       (tree-cardinality (tmap::tree->left tree))
       (tree-cardinality (tmap::tree->right tree))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-cardinality-when-tree-equiv-congruence
  (implies (tmap::tree-equiv tree0 tree1)
           (equal (tree-cardinality tree0)
                  (tree-cardinality tree1)))
  :rule-classes :congruence
  :expand ((tree-cardinality tree0)
           (tree-cardinality tree1)))

(defruled tree-cardinality-when-tree-empty-p
  (implies (tmap::tree-empty-p tree)
           (equal (tree-cardinality tree)
                  0))
  :enable tree-cardinality)

(defruled tree-cardinality-when-not-tree-empty-p
  (implies (not (tmap::tree-empty-p tree))
           (equal (tree-cardinality tree)
                  (+ (nfix (tmap::tree-element->val (tmap::tree->head tree)))
                     (tree-cardinality (tmap::tree->left tree))
                     (tree-cardinality (tmap::tree->right tree)))))
  :enable tree-cardinality)

(defruled equal-of-tree-cardinality-and-0-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (equal (equal (tree-cardinality tree) 0)
                  (tmap::tree-empty-p tree)))
  :induct t
  :enable (tree-cardinality
           tree-all-vals-posp
           nfix))

(defrule tree-lookup-<=-tree-cardinality-linear
  (implies (and (tree-all-vals-posp tree)
                (tset::in key (tmap::tree-key-set tree)))
           (<= (tmap::tree-lookup key tree)
               (tree-cardinality tree)))
  :rule-classes :linear
  :induct (tmap::tree-lookup key tree)
  :enable (tmap::tree-lookup
           tree-cardinality-when-not-tree-empty-p
           tree-all-vals-posp
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rebalancing moves nodes around without changing which are present.

(defrule tree-cardinality-of-rotate-left
  (implies (not (tmap::tree-empty-p (tmap::tree->right tree)))
           (equal (tree-cardinality (tmap::rotate-left tree))
                  (tree-cardinality tree)))
  :enable tree-cardinality)

(defrule tree-cardinality-of-rotate-right
  (implies (not (tmap::tree-empty-p (tmap::tree->left tree)))
           (equal (tree-cardinality (tmap::rotate-right tree))
                  (tree-cardinality tree)))
  :enable tree-cardinality)

(defrule tree-cardinality-of-tree-join
  (equal (tree-cardinality (tmap::tree-join left right))
         (+ (tree-cardinality left)
            (tree-cardinality right)))
  :induct t
  :enable (tree-cardinality
           tmap::tree-join))

(defrule tree-cardinality-of-tree-join-at
  (equal (tree-cardinality (tmap::tree-join-at split left right))
         (+ (tree-cardinality left)
            (tree-cardinality right)))
  :enable tmap::tree-join-at)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-cardinality-of-tree-delete
  (implies (and (tmap::bstp tree)
                (tree-all-vals-posp tree))
           (equal (tree-cardinality (tmap::tree-delete key tree))
                  (if (tset::in key (tmap::tree-key-set tree))
                      (- (tree-cardinality tree)
                         (tmap::tree-lookup key tree))
                    (tree-cardinality tree))))
  :induct (tmap::tree-delete key tree)
  :enable (tmap::tree-delete
           tree-cardinality
           tree-all-vals-posp
           nfix))

(defrule tree-cardinality-of-tree-update
  (implies (and (tmap::bstp tree)
                (tree-all-vals-posp tree))
           (equal (tree-cardinality (tmap::tree-update key val tree))
                  (+ (nfix val)
                     (if (tset::in key (tmap::tree-key-set tree))
                         (- (tree-cardinality tree)
                            (tmap::tree-lookup key tree))
                       (tree-cardinality tree)))))
  :induct (tmap::tree-update key val tree)
  :enable (tmap::tree-update
           tree-cardinality
           tree-all-vals-posp
           nfix))
