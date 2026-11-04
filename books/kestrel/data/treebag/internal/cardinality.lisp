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
(include-book "kestrel/data/treemap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/lookup-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))

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
           nfix
           acl2::fix))

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
