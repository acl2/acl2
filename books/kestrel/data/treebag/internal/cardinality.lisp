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
(include-book "kestrel/data/treemap/internal/rotate-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/join-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/update-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/delete-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/bst" :dir :system))
(local (include-book "kestrel/data/treemap/internal/heap" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/internal/rotate" :dir :system))
(local (include-book "kestrel/data/treemap/internal/join" :dir :system))
(local (include-book "kestrel/data/treemap/internal/update" :dir :system))
(local (include-book "kestrel/data/treemap/internal/delete" :dir :system))

(local (include-book "map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The cardinality of a bag's tree: the sum of the multiplicities at its nodes.

(define tree-cardinality ((tree treemap::treep))
  :guard (tree-all-vals-posp tree)
  :returns (cardinality natp :rule-classes :type-prescription)
  (if (treemap::tree-empty-p tree)
      0
    (+ (lnfix (treemap::tree-element->val (treemap::tree->head tree)))
       (tree-cardinality (treemap::tree->left tree))
       (tree-cardinality (treemap::tree->right tree))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-posp))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-cardinality-when-tree-equiv-congruence
  (implies (treemap::tree-equiv tree0 tree1)
           (equal (tree-cardinality tree0)
                  (tree-cardinality tree1)))
  :rule-classes :congruence
  :expand ((tree-cardinality tree0)
           (tree-cardinality tree1)))

(defruled tree-cardinality-when-tree-empty-p
  (implies (treemap::tree-empty-p tree)
           (equal (tree-cardinality tree)
                  0))
  :enable tree-cardinality)

(defruled tree-cardinality-when-not-tree-empty-p
  (implies (not (treemap::tree-empty-p tree))
           (equal (tree-cardinality tree)
                  (+ (nfix (treemap::tree-element->val (treemap::tree->head tree)))
                     (tree-cardinality (treemap::tree->left tree))
                     (tree-cardinality (treemap::tree->right tree)))))
  :enable tree-cardinality)

(defruled equal-of-tree-cardinality-and-0-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (equal (equal (tree-cardinality tree) 0)
                  (treemap::tree-empty-p tree)))
  :induct t
  :enable (tree-cardinality
           tree-all-vals-posp
           nfix))

(defrule tree-lookup-<=-tree-cardinality-linear
  (implies (and (tree-all-vals-posp tree)
                (treeset::in key (treemap::tree-key-set tree)))
           (<= (treemap::tree-lookup key tree)
               (tree-cardinality tree)))
  :rule-classes :linear
  :induct (treemap::tree-lookup key tree)
  :enable (treemap::tree-lookup
           tree-cardinality-when-not-tree-empty-p
           tree-all-vals-posp
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rebalancing moves nodes around without changing which are present.

(defrule tree-cardinality-of-rotate-left
  (implies (not (treemap::tree-empty-p (treemap::tree->right tree)))
           (equal (tree-cardinality (treemap::rotate-left tree))
                  (tree-cardinality tree)))
  :enable tree-cardinality)

(defrule tree-cardinality-of-rotate-right
  (implies (not (treemap::tree-empty-p (treemap::tree->left tree)))
           (equal (tree-cardinality (treemap::rotate-right tree))
                  (tree-cardinality tree)))
  :enable tree-cardinality)

(defrule tree-cardinality-of-tree-join
  (equal (tree-cardinality (treemap::tree-join left right))
         (+ (tree-cardinality left)
            (tree-cardinality right)))
  :induct t
  :enable (tree-cardinality
           treemap::tree-join))

(defrule tree-cardinality-of-tree-join-at
  (equal (tree-cardinality (treemap::tree-join-at split left right))
         (+ (tree-cardinality left)
            (tree-cardinality right)))
  :enable treemap::tree-join-at)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-cardinality-of-tree-delete
  (implies (and (treemap::bstp tree)
                (tree-all-vals-posp tree))
           (equal (tree-cardinality (treemap::tree-delete key tree))
                  (if (treeset::in key (treemap::tree-key-set tree))
                      (- (tree-cardinality tree)
                         (treemap::tree-lookup key tree))
                    (tree-cardinality tree))))
  :induct (treemap::tree-delete key tree)
  :enable (treemap::tree-delete
           tree-cardinality
           tree-all-vals-posp
           nfix))

(defrule tree-cardinality-of-tree-update
  (implies (and (treemap::bstp tree)
                (tree-all-vals-posp tree))
           (equal (tree-cardinality (treemap::tree-update key val tree))
                  (+ (nfix val)
                     (if (treeset::in key (treemap::tree-key-set tree))
                         (- (tree-cardinality tree)
                            (treemap::tree-lookup key tree))
                       (tree-cardinality tree)))))
  :induct (treemap::tree-update key val tree)
  :enable (treemap::tree-update
           tree-cardinality
           tree-all-vals-posp
           nfix))
