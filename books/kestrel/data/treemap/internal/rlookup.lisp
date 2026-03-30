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
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "values-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "values"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: this can be O(n) (instead of O(n log(m)) as it is now, where m is the
;;   number of matching keys, m <= n).
;;   The optimal version would create an oset (doing a sort of filtering
;;   in-order traversal) then call an optimized O(n) from-oset.
;;   - Perhaps not a high priority. m is unlikely to be large.
(define tree-rlookup
  (val
   (tree treep))
  :returns (keys treeset::setp)
  :parents (implementation)
  :short "Lookup all keys in the tree mapping to a value."
  (if (tree-empty-p tree)
      (treeset::empty)
    (let ((keys (treeset::union (tree-rlookup val (tree->left tree))
                                (tree-rlookup val (tree->right tree)))))
      (if (equal val (tree-element->val (tree->head tree)))
          (treeset::insert (tree-element->key (tree->head tree)) keys)
        keys)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-rlookup)))

(defrule tree-rlookup-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-rlookup val tree0)
                  (tree-rlookup val tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-rlookup)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-rlookup-of-tree-node
  (equal (tree-rlookup val (tree-node head left right))
         (if (equal val (tree-element->val head))
             (treeset::insert (tree-element->key head)
                              (treeset::union (tree-rlookup val left)
                                              (tree-rlookup val right)))
           (treeset::union (tree-rlookup val left)
                           (tree-rlookup val right))))
  :enable tree-rlookup)

(defruled tree-rlookup-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-rlookup val tree)
                  (treeset::empty)))
  :enable tree-rlookup)

(defrule tree-rlookup-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-rlookup val tree)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-rlookup-when-tree-empty-p)

(defrule tree-rlookup-of-arg1-and-nil
  (equal (tree-rlookup val nil)
         (treeset::empty))
  :enable tree-rlookup-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-rlookup-when-in-of-tree-rlookup-tree->left
  (implies (treeset::in key (tree-rlookup val (tree->left tree)))
           (treeset::in key (tree-rlookup val tree)))
  :enable tree-rlookup)

(defrule subset-of-tree-rlookup-tree->left
  (treeset::subset (tree-rlookup val (tree->left tree))
                   (tree-rlookup val tree))
  :enable treeset::pick-a-point)

(defrule in-of-tree-rlookup-when-in-of-tree-rlookup-tree->right
  (implies (treeset::in key (tree-rlookup val (tree->right tree)))
           (treeset::in key (tree-rlookup val tree)))
  :enable tree-rlookup)

(defrule subset-of-tree-rlookup-tree->right
  (treeset::subset (tree-rlookup val (tree->right tree))
                   (tree-rlookup val tree))
  :enable treeset::pick-a-point)

(defruled in-of-tree-key-set-when-in-of-tree-rlookup
  (implies (treeset::in key (tree-rlookup val tree))
           (treeset::in key (tree-key-set tree)))
  :induct t
  :enable tree-rlookup)

(defrule in-of-tree-key-set-when-in-of-tree-rlookup-forward-chaining
  (implies (treeset::in key (tree-rlookup val tree))
           (treeset::in key (tree-key-set tree)))
  :rule-classes :forward-chaining
  :by in-of-tree-key-set-when-in-of-tree-rlookup)

(defrule subset-of-tree-rlookup-tree-and-tree-key-set
  (treeset::subset (tree-rlookup val tree)
                   (tree-key-set tree))
  :enable treeset::pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-rlookup
  (implies (bstp tree)
           (equal (treeset::in key (tree-rlookup val tree))
                  (and (treeset::in key (tree-key-set tree))
                       (equal (tree-lookup key tree) val))))
  :induct t
  :enable tree-rlookup)

(defrule emptyp-of-tree-rlookup
  (equal (treeset::emptyp (tree-rlookup val tree))
         (not (treeset::in val (tree-val-set tree))))
  :induct t
  :enable tree-rlookup)
