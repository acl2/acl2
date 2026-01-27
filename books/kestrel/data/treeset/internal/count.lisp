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

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(include-book "tree-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-nodes-count-acc
  ((tree treep)
   (acc natp))
  :returns (count natp :rule-classes :type-prescription)
  (if (tree-empty-p tree)
      (lnfix acc)
    (tree-nodes-count-acc (tree->left tree)
                          (tree-nodes-count-acc (tree->right tree)
                                                (+ 1 (lnfix acc))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-nodes-count-acc)))

(defrule tree-nodes-count-acc-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-nodes-count-acc tree0 acc)
                  (tree-nodes-count-acc tree1 acc)))
  :rule-classes :congruence
  :induct t
  :enable tree-nodes-count-acc)

(defrule tree-nodes-count-acc-when-nat-equiv-congruence
  (implies (data::nat-equiv acc0 acc1)
           (equal (tree-nodes-count-acc tree acc0)
                  (tree-nodes-count-acc tree acc1)))
  :rule-classes :congruence
  :induct t
  :enable tree-nodes-count-acc)

(defruledl tree-nodes-count-acc-of-arg1-and-+
  (implies (and (natp acc0)
                (natp acc1))
           (equal (tree-nodes-count-acc tree (+ acc0 acc1))
                  (+ (tree-nodes-count-acc tree acc0)
                     acc1)))
  :induct t
  :enable tree-nodes-count-acc)

(defrulel tree-nodes-count-acc-when-acc-not-0-syntaxp
  (implies (syntaxp (not (equal acc ''0)))
           (equal (tree-nodes-count-acc tree acc)
                  (+ (tree-nodes-count-acc tree 0)
                     (nfix acc))))
  :use ((:instance tree-nodes-count-acc-of-arg1-and-+
                   (acc0 0)
                   (acc1 (nfix acc))))
  :enable (acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-nodes-count ((tree treep))
  :parents (implementation)
  :short "The number of elements in a tree."
  :returns (count natp :rule-classes :type-prescription)
  (mbe :logic (if (tree-empty-p tree)
                  0
                (+ 1
                   (tree-nodes-count (tree->left tree))
                   (tree-nodes-count (tree->right tree))))
       :exec (tree-nodes-count-acc tree 0))
  :inline t
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-nodes-count)))

(defrule tree-nodes-count-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-nodes-count tree0)
                  (tree-nodes-count tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-nodes-count)

(defrule tree-nodes-count-acc-becomes-tree-nodes-count
  (equal (tree-nodes-count-acc tree acc)
         (+ (tree-nodes-count tree)
            (nfix acc)))
  :induct t
  :enable (tree-nodes-count
           tree-nodes-count-acc))

(verify-guards tree-nodes-count$inline
  :hints (("Goal" :in-theory (enable tree-nodes-count
                                     acl2::fix))))

(defruled equal-of-tree-nodes-count-and-0-becomes-tree-empty-p
  (equal (equal (tree-nodes-count tree)
                0)
         (tree-empty-p tree))
  :induct t
  :enable (tree-nodes-count
           tree-empty-p
           acl2::fix))

(defrule tree-nodes-count-when-tree-emptyp-forward-chaining
  (implies (tree-empty-p tree)
           (equal (tree-nodes-count tree)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-tree-nodes-count-and-0-becomes-tree-empty-p)

(defrule tree-empty-p-when-equal-tree-nodes-count-and-0-forward-chaining
  (implies (equal (tree-nodes-count tree)
                  0)
           (tree-empty-p tree))
  :rule-classes :forward-chaining
  :enable equal-of-tree-nodes-count-and-0-becomes-tree-empty-p)
