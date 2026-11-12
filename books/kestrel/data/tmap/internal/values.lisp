; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/union-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: It may be slightly faster to MBE-in a version that avoids union by
;; using an accumulator.
(define tree-val-set ((tree treep))
  :type-prescription :none
  :returns (set tset::setp)
  (if (tree-empty-p tree)
      (tset::empty)
    (tset::insert
      (tree-element->val (tree->head tree))
      (tset::union (tree-val-set (tree->left tree))
                   (tree-val-set (tree->right tree)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

;; The executable rule is disabled because it often produces `nil` when it
;; should produce `emptyp`.
(in-theory (disable (:e tree-val-set)))

(defrule tree-val-set-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-val-set tree0)
                  (tree-val-set tree1)))
  :rule-classes :congruence
  :expand ((tree-val-set tree0)
           (tree-val-set tree1)))

(defrule emptyp-of-tree-val-set
  (equal (tset::emptyp (tree-val-set tree))
         (tree-empty-p tree))
  :expand ((tree-val-set tree)))

(defruled tree-val-set-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-val-set tree)
                  (tset::empty)))
  :enable tree-val-set)

(defrule tree-val-set-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-val-set tree)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-val-set-when-tree-empty-p)

(defrule tree-val-set-of-tree-node
  (equal (tree-val-set (tree-node head left right))
         (tset::insert
           (tree-element->val head)
           (tset::union (tree-val-set left)
                        (tree-val-set right))))
  :enable tree-val-set)

(defruled in-of-tree-val-set
  (equal (tset::in val (tree-val-set tree))
         (and (not (tree-empty-p tree))
              (or (equal val (tree-element->val (tree->head tree)))
                  (tset::in val (tree-val-set (tree->left tree)))
                  (tset::in val (tree-val-set (tree->right tree))))))
  :enable tree-val-set)

(defruled in-of-tree-val-set-when-not-tree-empty-p
  (implies (not (tree-empty-p tree))
           (equal (tset::in val (tree-val-set tree))
                  (or (equal val (tree-element->val (tree->head tree)))
                      (tset::in val (tree-val-set (tree->left tree)))
                      (tset::in val (tree-val-set (tree->right tree))))))
  :by in-of-tree-val-set)

(defrule in-of-tree-val-set-when-not-tree-empty-p-cheap
  (implies (not (tree-empty-p tree))
           (equal (tset::in val (tree-val-set tree))
                  (or (equal val (tree-element->val (tree->head tree)))
                      (tset::in val (tree-val-set (tree->left tree)))
                      (tset::in val (tree-val-set (tree->right tree))))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by in-of-tree-val-set-when-not-tree-empty-p)

(defrule in-of-tree->head-and-tree-val-set
  (equal (tset::in (tree-element->val (tree->head tree))
                   (tree-val-set tree))
         (not (tree-empty-p tree))))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-tree-val-set-tree->left-and-tree-val-set
  (tset::subset (tree-val-set (tree->left tree))
                (tree-val-set tree))
  :expand ((tree-val-set tree))
  :enable tset::pick-a-point-polar)

(defrule in-of-tree-val-set-when-in-of-tree-val-set-tree->left-forward-chaining
  (implies (tset::in val (tree-val-set (tree->left tree)))
           (tset::in val (tree-val-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-val-set-tree->left-when-not-in-of-tree-val-set-cheap
  (implies (not (tset::in val (tree-val-set tree)))
           (not (tset::in val (tree-val-set (tree->left tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defrule subset-of-tree-val-set-tree->right-and-tree-val-set
  (tset::subset (tree-val-set (tree->right tree))
                (tree-val-set tree))
  :expand ((tree-val-set tree))
  :enable tset::pick-a-point-polar)

(defrule in-of-tree-val-set-when-in-of-tree-val-set-tree->right-forward-chaining
  (implies (tset::in val (tree-val-set (tree->right tree)))
           (tset::in val (tree-val-set tree)))
  :rule-classes :forward-chaining)

(defrule in-of-tree-val-set-tree->right-when-not-in-of-tree-val-set-cheap
  (implies (not (tset::in val (tree-val-set tree)))
           (not (tset::in val (tree-val-set (tree->right tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-lookup-and-tree-val-set
  (implies (tset::in key (tree-key-set map))
           (tset::in (tree-lookup key map)
                     (tree-val-set map)))
  :induct t
  :enable (tree-lookup
           tree-key-set
           tree-val-set))

(defruled tree-lookup-when-not-in-tree-val-set
  (implies (and (not (tset::in val (tree-val-set tree)))
                (or (tset::in key (tree-key-set tree))
                    (not (equal val nil))))
           (not (equal (tree-lookup key tree)
                       val))))

(defrule tree-lookup-when-not-in-tree-val-set-forward-chaining
  (implies (and (not (tset::in val (tree-val-set tree)))
                (or (tset::in key (tree-key-set tree))
                    (not (equal val nil))))
           (not (equal (tree-lookup key tree)
                       val)))
  :rule-classes ((:forward-chaining :trigger-terms ((tree-lookup key tree))))
  :by tree-lookup-when-not-in-tree-val-set)

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-tree-val-set-when-bstp-linear
  (implies (bstp tree)
           (<= (tset::cardinality (tree-val-set tree))
               (tset::cardinality (tree-key-set tree))))
  :rule-classes :linear
  :induct t
  :enable (tree-val-set
           tree-key-set
           tset::cardinality-of-insert
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: value list (possibly with duplicates)
;;   Not a high priority. If a user wants, they can always call from-omap and
;;   get the value list of that. It would even be in the expected order.
