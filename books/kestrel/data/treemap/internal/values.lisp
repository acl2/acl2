; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: It may be slightly faster to MBE-in a version that avoids union by
;; using an accumulator.
(define tree-val-set ((tree treep))
  :returns (set treeset::setp)
  (if (tree-empty-p tree)
      (treeset::empty)
    (treeset::insert
      (tree-element->val (tree->head tree))
      (treeset::union (tree-val-set (tree->left tree))
                      (tree-val-set (tree->right tree)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

;; The executable rule is disabled because it often produces `nil` when it
;; should produce `emptyp`.
(in-theory (disable (:t tree-val-set) (:e tree-val-set)))

(defrule tree-val-set-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-val-set tree0)
                  (tree-val-set tree1)))
  :rule-classes :congruence
  :expand ((tree-val-set tree0)
           (tree-val-set tree1)))

(defrule emptyp-of-tree-val-set
  (equal (treeset::emptyp (tree-val-set tree))
         (tree-empty-p tree))
  :expand ((tree-val-set tree)))

(defruled tree-val-set-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-val-set tree)
                  (treeset::empty)))
  :enable tree-val-set)

(defrule tree-val-set-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-val-set tree)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-val-set-when-tree-empty-p)

(defrule tree-val-set-of-tree-node
  (equal (tree-val-set (tree-node head left right))
         (treeset::insert
           (tree-element->val head)
           (treeset::union (tree-val-set left)
                           (tree-val-set right))))
  :enable tree-val-set)

(defruled in-of-tree-val-set
  (equal (treeset::in val (tree-val-set tree))
         (and (not (tree-empty-p tree))
              (or (equal val (tree-element->val (tree->head tree)))
                  (treeset::in val (tree-val-set (tree->left tree)))
                  (treeset::in val (tree-val-set (tree->right tree))))))
  :enable tree-val-set)

(defruled in-of-tree-val-set-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (treeset::in val (tree-val-set tree))
                  (or (equal val (tree-element->val (tree->head tree)))
                      (treeset::in val (tree-val-set (tree->left tree)))
                      (treeset::in val (tree-val-set (tree->right tree))))))
  :by in-of-tree-val-set)

(defrule in-of-tree-val-set-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (treeset::in val (tree-val-set tree))
                  (or (equal val (tree-element->val (tree->head tree)))
                      (treeset::in val (tree-val-set (tree->left tree)))
                      (treeset::in val (tree-val-set (tree->right tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by in-of-tree-val-set-when-not-tree-empty-p)

(defrule in-of-tree->head-and-tree-val-set
  (equal (treeset::in (tree-element->val (tree->head tree))
                      (tree-val-set tree))
         (not (tree-empty-p tree))))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-tree-val-set-tree->left-and-tree-val-set
  (treeset::subset (tree-val-set (tree->left tree))
                   (tree-val-set tree))
  :expand ((tree-val-set tree))
  :enable treeset::pick-a-point-polar)

(defrule in-of-tree-val-set-when-in-of-tree-val-set-tree->left-forward-chaining
  (implies (treeset::in val (tree-val-set (tree->left tree)))
           (treeset::in val (tree-val-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-val-set-tree->left-when-not-in-of-tree-val-set-cheap
  (implies (not (treeset::in val (tree-val-set tree)))
           (not (treeset::in val (tree-val-set (tree->left tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defrule subset-of-tree-val-set-tree->right-and-tree-val-set
  (treeset::subset (tree-val-set (tree->right tree))
                   (tree-val-set tree))
  :expand ((tree-val-set tree))
  :enable treeset::pick-a-point-polar)

(defrule in-of-tree-val-set-when-in-of-tree-val-set-tree->right-forward-chaining
  (implies (treeset::in val (tree-val-set (tree->right tree)))
           (treeset::in val (tree-val-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-val-set-tree->right-when-not-in-of-tree-val-set-cheap
  (implies (not (treeset::in val (tree-val-set tree)))
           (not (treeset::in val (tree-val-set (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-lookup-and-tree-val-set
  (implies (treeset::in key (tree-key-set map))
           (treeset::in (tree-lookup key map)
                        (tree-val-set map)))
  :induct t
  :enable (tree-lookup
           tree-key-set
           tree-val-set))

(defruled tree-lookup-when-not-in-tree-val-set
  (implies (and (not (treeset::in val (tree-val-set tree)))
                (or (treeset::in key (tree-key-set tree))
                    (not (equal val nil))))
           (not (equal (tree-lookup key tree)
                       val))))

(defrule tree-lookup-when-not-in-tree-val-set-forward-chaining
  (implies (and (not (treeset::in val (tree-val-set tree)))
                (or (treeset::in key (tree-key-set tree))
                    (not (equal val nil))))
           (not (equal (tree-lookup key tree)
                       val)))
  :rule-classes ((:forward-chaining :trigger-terms ((tree-lookup key tree))))
  :by tree-lookup-when-not-in-tree-val-set)

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-tree-val-set-when-bstp-linear
  (implies (bstp tree)
           (<= (treeset::cardinality (tree-val-set tree))
               (treeset::cardinality (tree-key-set tree))))
  :rule-classes :linear
  :induct t
  :enable (tree-val-set
           tree-key-set
           treeset::cardinality-of-insert
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: value list (possibly with duplicates)
;;   Not a high priority. If a user wants, they can always call from-omap and
;;   get the value list of that. It would even be in the expected order.
