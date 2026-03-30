; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "submap-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Informal sketch:
;;   Assume the submaps are non-empty (the proof is straightforward otherwise).
;;   The head of x is the largest element wrt heap<. Same for y.
;;   If the head of x is not the head of y, that implies there exists
;;   an element of y that s greater than the head of x.
;;   But, by the submap hypothesis, this member must also be in x.
;;   This leads to a contradiction, since the head of x is maximal.
;;   Thus the heads must be the same.
(defrulel tree-element->key-of-tree->head-when-tree-submap-p-tree-submap-p
  (implies (and (tree-submap-p x y)
                (syntaxp (<< y x))
                (tree-submap-p y x)
                (heapp x)
                (heapp y))
           (equal (tree-element->key (tree->head x))
                  (tree-element->key (tree->head y))))
  :cases ((tree-empty-p x)
          (tree-empty-p y))
  :use ((:instance heap<-of-tree->head-and-arg2-when-in-arg2-of-tree-key-set
                   (key (tree-element->key (tree->head x)))
                   (tree y))
        ;; TODO: why are :use hints these necessary?
        (:instance treeset::in-when-subset-and-in
                   (a (tree-element->key (tree->head y)))
                   (x (tree-key-set y))
                   (y (tree-key-set x)))
        (:instance treeset::in-when-subset-and-in
                   (a (tree-element->key (tree->head x)))
                   (x (tree-key-set x))
                   (y (tree-key-set y))))
  :disable (heap<-of-tree->head-and-arg2-when-in-arg2-of-tree-key-set
            treeset::in-when-in-and-subset
            treeset::in-when-subset-and-in))

;;;;;;;;;;;;;;;;;;;;

(defrulel tree-element->val-of-tree->head-when-tree-submap-p-tree-submap-p
  (implies (and (tree-submap-p x y)
                (syntaxp (<< y x))
                (tree-submap-p y x)
                (heapp x)
                (heapp y))
           (equal (tree-element->val (tree->head x))
                  (tree-element->val (tree->head y))))
  :use ((:instance tree-lookup-when-tree-submap-p-and-in-of-tree-key-set
                   (key (tree-element->key (tree->head x)))))
  :enable tree-lookup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl equal-when-treep
  (implies (and (treep x)
                (treep y))
           (equal (equal x y)
                  (if (tree-empty-p x)
                      (tree-empty-p y)
                    (and (not (tree-empty-p y))
                         (equal (tree-element->key (tree->head x))
                                (tree-element->key (tree->head y)))
                         (equal (tree-element->val (tree->head x))
                                (tree-element->val (tree->head y)))
                         (equal (tree->left x)
                                (tree->left y))
                         (equal (tree->right x)
                                (tree->right y))))))
  :enable (treep
           tree-empty-p
           tree->head
           tree->left
           tree->right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-tree->left-when-in-and-<<-all
  (implies (and (<<-all-r (tree-element->key (tree->head y))
                          (tree->right y))
                (<<-all-l (tree->left x)
                          (tree-element->key (tree->head y)))
                (treeset::in key (tree-key-set (tree->left x)))
                (treeset::in key (tree-key-set y)))
           (treeset::in key (tree-key-set (tree->left y))))
  :enable tree-key-set)

(defrule tree-submap-p-of-tree->left-tree->left-when-tree-submap-p-and-<<-all-l
  (implies (and (tree-submap-p x y)
                (bstp x)
                (bstp y)
                (<<-all-l (tree->left x)
                          (tree-element->key (tree->head y))))
           (tree-submap-p (tree->left x) (tree->left y)))
  :use ((:instance tree-lookup-when->>-of-tree->head
                   (key (tree-submap-p-sk-witness (tree->left x)
                                                  (tree->left y)))
                   (tree y)))
  :enable tree-submap-p-pick-a-point-polar
  :disable tree-lookup-when->>-of-tree->head)

(defrule tree-submap-p-of-tree->left-tree->left-when-tree-submap-p-and-equal-tree->head-tree->head
  (implies (and (tree-submap-p x y)
                (bstp x)
                (bstp y)
                (equal (tree-element->key (tree->head x))
                       (tree-element->key (tree->head y))))
           (tree-submap-p (tree->left x) (tree->left y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-tree-key-set-tree->right-when-in-and-<<-all
  (implies (and (<<-all-l (tree->left y)
                          (tree-element->key (tree->head y)))
                (<<-all-r (tree-element->key (tree->head y))
                          (tree->right x))
                (treeset::in key (tree-key-set (tree->right x)))
                (treeset::in key (tree-key-set y)))
           (treeset::in key (tree-key-set (tree->right y))))
  :enable tree-key-set)

(defrule tree-submap-p-of-tree->right-tree->right-when-tree-submap-p-and-<<-all-r
  (implies (and (tree-submap-p x y)
                (bstp x)
                (bstp y)
                (<<-all-r (tree-element->key (tree->head y))
                          (tree->right x)))
           (tree-submap-p (tree->right x) (tree->right y)))
  :use ((:instance tree-lookup-when-<<-of-tree->head
                   (key (tree-submap-p-sk-witness (tree->right x)
                                                  (tree->right y)))
                   (tree y)))
  :enable tree-submap-p-pick-a-point-polar
  :disable tree-lookup-when-<<-of-tree->head)

(defrule tree-submap-p-of-tree->right-tree->right-when-tree-submap-p-and-equal-tree->head-tree->head
  (implies (and (tree-submap-p x y)
                (bstp x)
                (bstp y)
                (equal (tree-element->key (tree->head x))
                       (tree-element->key (tree->head y))))
           (tree-submap-p (tree->right x) (tree->right y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Informal sketch:
;;   Induct over the tree structure of x and y simultaneously.
;;   By tree-element->key-of-tree->head-when-tree-submap-p-tree-submap-p,
;;   their heads are equal (this depends on the heapp hypotheses).
;;   The left children are submaps of one another,
;;   and the right children are submaps of one another.
;;   This follows from the bstp property
;;   (All left elements must be smaller than the shared head.
;;   All right elements must be greater).
(defrule tree-submap-p-antisymmetry-weak
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y)
                (tree-submap-p x y)
                (tree-submap-p y x))
           (equal x y))
  :rule-classes nil
  :induct (tree-bi-induct x y)
  :restrict ((equal-when-treep
               ((x x)
                (y y))))
  :enable equal-when-treep)

(defruled tree-submap-p-antisymmetry
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (and (tree-submap-p x y)
                       (tree-submap-p y x))
                  (equal x y)))
  :use tree-submap-p-antisymmetry-weak)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-double-containment-no-backchain-limit
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (equal x y)
                  (and (tree-submap-p x y)
                       (tree-submap-p y x))))
  :by tree-submap-p-antisymmetry)

(defruled tree-double-containment
  (implies (and (treep x)
                (treep y)
                (bstp x)
                (bstp y)
                (heapp x)
                (heapp y))
           (equal (equal x y)
                  (and (tree-submap-p x y)
                       (tree-submap-p y x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :by tree-double-containment-no-backchain-limit)
