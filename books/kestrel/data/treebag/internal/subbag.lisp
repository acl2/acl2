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

(include-book "../bag-defs")
(include-book "../count-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))

(local (include-book "../bag"))
(local (include-book "../count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compare the counts of each key of a tree in two bags. The tree only
;; enumerates the keys: run over the first bag's own tree, it visits every
;; element of that bag.
;;
;; This reads two counts per element, which costs O(m(log(m) + log(n))) time
;; for bags of m and n distinct elements. A faster execution is possible:
;; split the second bag's tree at each key of the first and recurse on the
;; halves, as treemap::fast-tree-submap-p does, in O(m log(n/m)) time.

(define tree-subbag-p ((tree treemap::treep)
                       (sub bagp)
                       (sup bagp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (treemap::tree-empty-p tree)
      (let ((x (treemap::tree-element->key (treemap::tree->head tree))))
        (and (<= (count x sub) (count x sup))
             (tree-subbag-p (treemap::tree->left tree) sub sup)
             (tree-subbag-p (treemap::tree->right tree) sub sup)))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-subbag-p-when-equiv-of-arg2-congruence
  (implies (equiv sub0 sub1)
           (equal (tree-subbag-p tree sub0 sup)
                  (tree-subbag-p tree sub1 sup)))
  :rule-classes :congruence
  :induct t
  :enable tree-subbag-p)

(defrule tree-subbag-p-when-equiv-of-arg3-congruence
  (implies (equiv sup0 sup1)
           (equal (tree-subbag-p tree sub sup0)
                  (tree-subbag-p tree sub sup1)))
  :rule-classes :congruence
  :induct t
  :enable tree-subbag-p)

(defruled count-<=-count-when-tree-subbag-p
  (implies (and (tree-subbag-p tree sub sup)
                (treeset::in x (treemap::tree-key-set (double-rewrite tree))))
           (<= (count x sub)
               (count x sup)))
  :induct t
  :enable tree-subbag-p)
