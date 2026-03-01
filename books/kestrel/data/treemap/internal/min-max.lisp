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

(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-leftmost ((tree treep))
  :guard (not (tree-empty-p tree))
  (if (tree-empty-p (tree->left tree))
      (tree-element->key+val (tree->head tree))
    (tree-leftmost (tree->left tree))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-leftmost)))

(defrule tree-leftmost-type-prescription
  (consp (tree-leftmost tree))
  :rule-classes :type-prescription
  :induct t
  :enable tree-leftmost)

(defrule tree-leftmost-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-leftmost tree0)
                  (tree-leftmost tree1)))
  :rule-classes :congruence
  :expand ((tree-leftmost tree0)
           (tree-leftmost tree1)))

(defruled tree-leftmost-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-leftmost tree)
                  (cons nil nil)))
  :enable (tree-leftmost
           irr-tree-element))

(defrule tree-leftmost-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-leftmost tree)
                  (cons nil nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-leftmost-when-tree-empty-p)

(defrule in-of-tree-leftmost-when-not-tree-empty-p
  (equal (treeset::in (car (tree-leftmost tree)) (tree-key-set tree))
         (not (tree-empty-p tree)))
  :induct t
  :enable tree-leftmost)

(defrule <<-of-tree-leftmost-when-<<-all-l
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (<< (car (tree-leftmost tree)) x))
  :enable <<-when-<<-all-l-and-in-of-tree-key-set)

(defrule <<-of-arg1-and-tree-leftmost-when-<<-all-r
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (<< x (car (tree-leftmost tree))))
  :enable <<-when-<<-all-r-and-in-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;

(defruled cdr-of-tree-leftmost
  (implies (bstp tree)
           (equal (cdr (tree-leftmost tree))
                  (tree-lookup (car (tree-leftmost tree)) tree)))
  :induct t
  :enable (tree-leftmost
           irr-tree-element))

(defruled car-of-tree-leftmost-becomes-min
  (implies (and (bstp tree)
                (heapp tree))
           (equal (car (tree-leftmost tree))
                  (treeset::min (tree-key-set tree))))
  :induct t
  :enable (tree-leftmost
           irr-tree-element))

(defrule tree-leftmost-becomes-min
  (implies (and (bstp tree)
                (heapp tree))
           (equal (tree-leftmost tree)
                  (cons (treeset::min (tree-key-set tree))
                        (tree-lookup (treeset::min (tree-key-set tree)) tree))))
  :enable (car-of-tree-leftmost-becomes-min
           cdr-of-tree-leftmost))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-rightmost ((tree treep))
  :guard (not (tree-empty-p tree))
  (if (tree-empty-p (tree->right tree))
      (tree-element->key+val (tree->head tree))
    (tree-rightmost (tree->right tree))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-rightmost)))

(defrule tree-rightmost-type-prescription
  (consp (tree-rightmost tree))
  :rule-classes :type-prescription
  :induct t
  :enable tree-rightmost)

(defrule tree-rightmost-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-rightmost tree0)
                  (tree-rightmost tree1)))
  :rule-classes :congruence
  :expand ((tree-rightmost tree0)
           (tree-rightmost tree1)))

(defruled tree-rightmost-when-tree-empty-p
  (implies (tree-empty-p tree)
           (equal (tree-rightmost tree)
                  (cons nil nil)))
  :enable (tree-rightmost
           irr-tree-element))

(defrule tree-rightmost-when-tree-empty-p-cheap
  (implies (tree-empty-p tree)
           (equal (tree-rightmost tree)
                  (cons nil nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-rightmost-when-tree-empty-p)

(defrule in-of-tree-rightmost-when-not-tree-empty-p
  (equal (treeset::in (car (tree-rightmost tree)) (tree-key-set tree))
         (not (tree-empty-p tree)))
  :induct t
  :enable tree-rightmost)

(defrule <<-of-tree-rightmost-when-<<-all-l
  (implies (and (<<-all-l tree x)
                (not (tree-empty-p tree)))
           (<< (car (tree-rightmost tree)) x))
  :enable <<-when-<<-all-l-and-in-of-tree-key-set)

(defrule <<-of-arg1-and-tree-rightmost-when-<<-all-r
  (implies (and (<<-all-r x tree)
                (not (tree-empty-p tree)))
           (<< x (car (tree-rightmost tree))))
  :enable <<-when-<<-all-r-and-in-of-tree-key-set)

;;;;;;;;;;;;;;;;;;;;

(defruled cdr-of-tree-rightmost
  (implies (bstp tree)
           (equal (cdr (tree-rightmost tree))
                  (tree-lookup (car (tree-rightmost tree)) tree)))
  :induct t
  :enable (tree-rightmost
           irr-tree-element))

(defruled car-of-tree-rightmost-becomes-max
  (implies (and (bstp tree)
                (heapp tree))
           (equal (car (tree-rightmost tree))
                  (treeset::max (tree-key-set tree))))
  :induct t
  :enable (tree-rightmost
           irr-tree-element))

(defrule tree-rightmost-becomes-max
  (implies (and (bstp tree)
                (heapp tree))
           (equal (tree-rightmost tree)
                  (cons (treeset::max (tree-key-set tree))
                        (tree-lookup (treeset::max (tree-key-set tree)) tree))))
  :enable (car-of-tree-rightmost-becomes-max
           cdr-of-tree-rightmost))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
