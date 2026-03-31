; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/subset-defs" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "split-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/generic-typed" :dir :system))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "split"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-submap-p
  ((x treep)
   (y treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (implementation)
  :short "Check if one tree is a submap of the other."
  :guard (bstp y)
  (or (tree-empty-p x)
      (and (mbe :logic
                (and (treeset::in (tree-element->key (tree->head x))
                                  (tree-key-set y))
                     (equal (tree-lookup (tree-element->key (tree->head x)) y)
                            (tree-element->val (tree->head x))))
                :exec
                (let ((assoc (tree-search-assoc
                               (tree-element->key (tree->head x))
                               y)))
                  (and assoc
                       (equal (tree-element->val (tree->head x))
                              (cdr assoc)))))
           (tree-submap-p (tree->left x) y)
           (tree-submap-p (tree->right x) y))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-submap-p)))

(defrule tree-submap-p-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-submap-p x0 y)
                  (tree-submap-p x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-submap-p)

(defrule tree-submap-p-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-submap-p x y0)
                  (tree-submap-p x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-submap-p)

(defrule tree-submap-p-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (tree-submap-p x y))
  :enable tree-submap-p)

(defrule tree-submap-p-when-tree-empty-p-of-arg2
  (implies (tree-empty-p y)
           (equal (tree-submap-p x y)
                  (tree-empty-p x)))
  :enable tree-submap-p)

(defruled subset-of-tree-key-set-tree-key-set
  (implies (tree-submap-p x y)
           (treeset::subset (tree-key-set x) (tree-key-set y)))
  :enable treeset::pick-a-point-polar
  :prep-lemmas
  ((defrule tree-assoc-when-in-of-tree-key-set-and-tree-submap-p
     (implies (and (treeset::in key (tree-key-set x))
                   (tree-submap-p x y))
              (treeset::in key (tree-key-set y)))
     :induct t
     :enable tree-submap-p)))

(defrule subset-of-tree-key-set-tree-key-set-forward-chaining
  (implies (tree-submap-p x y)
           (treeset::subset (tree-key-set x) (tree-key-set y)))
  :rule-classes :forward-chaining
  :by subset-of-tree-key-set-tree-key-set)

(defruled tree-lookup-when-in-of-tree-key-set-and-tree-submap-p
  (implies (and (treeset::in key (tree-key-set x))
                (tree-submap-p x y))
           (equal (tree-lookup key y)
                  (tree-lookup key x)))
  :induct t
  :enable tree-submap-p)

;; TODO: disable by default?
(defrule tree-lookup-when-in-of-tree-key-set-and-proper-tree-submap-p
  (implies (and (treeset::in key (tree-key-set x))
                (tree-submap-p x y)
                ;; This hypothesis is not logically necessary.
                ;; It is used to prevent rewrite looping.
                (not (tree-submap-p y x)))
           (equal (tree-lookup key y)
                  (tree-lookup key x)))
  :by tree-lookup-when-in-of-tree-key-set-and-tree-submap-p)

(defruled tree-lookup-when-tree-submap-p-and-in-of-tree-key-set
  (implies (and (tree-submap-p x y)
                (treeset::in key (tree-key-set x)))
           (equal (tree-lookup key y)
                  (tree-lookup key x)))
  :by tree-lookup-when-in-of-tree-key-set-and-tree-submap-p)

;; TODO: disable by default?
(defrule tree-lookup-when-proper-tree-submap-p-and-in-of-tree-key-set
  (implies (and (tree-submap-p x y)
                (treeset::in key (tree-key-set x))
                ;; This hypothesis is not logically necessary.
                ;; It is used to prevent rewrite looping.
                (not (tree-submap-p y x)))
           (equal (tree-lookup key y)
                  (tree-lookup key x)))
  :by tree-lookup-when-tree-submap-p-and-in-of-tree-key-set)

(defrule tree-lookup-when-in-of-tree-key-set-and-tree-submap-p-forward-chaining
  (implies (and (treeset::in key (tree-key-set x))
                (tree-submap-p x y))
           (equal (tree-lookup key y)
                  (tree-lookup key x)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((treeset::in key (tree-key-set x))
                                  (tree-submap-p x y))))
  :by tree-lookup-when-in-of-tree-key-set-and-tree-submap-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-submap-p-when-tree-submap-p-of-arg1-and-tree->left
  (implies (and (tree-submap-p x (tree->left y))
                (bstp y))
           (tree-submap-p x y))
  :induct t
  :enable tree-submap-p)

(defrule tree-submap-p-when-tree-submap-p-of-arg1-and-tree->left-forward-chaining
  (implies (and (tree-submap-p x (tree->left y))
                (bstp y))
           (tree-submap-p x y))
  :rule-classes :forward-chaining
  :by tree-submap-p-when-tree-submap-p-of-arg1-and-tree->left)

(defruled tree-submap-p-when-tree-submap-p-of-arg1-and-tree->right
  (implies (and (tree-submap-p x (tree->right y))
                (bstp y))
           (tree-submap-p x y))
  :induct t
  :enable tree-submap-p)

(defrule tree-submap-p-when-tree-submap-p-of-arg1-and-tree->right-forward-chaining
  (implies (and (tree-submap-p x (tree->right y))
                (bstp y))
           (tree-submap-p x y))
  :rule-classes :forward-chaining
  :by tree-submap-p-when-tree-submap-p-of-arg1-and-tree->right)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-submap-p-of-tree->left-when-tree-submap-p
  (implies (tree-submap-p x y)
           (tree-submap-p (tree->left x) y))
  :enable tree-submap-p)

(defrule tree-submap-p-of-tree->left-when-tree-submap-p-cheap
  (implies (tree-submap-p x y)
           (tree-submap-p (tree->left x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-submap-p-of-tree->left-when-tree-submap-p)

(defruled tree-submap-p-of-tree->right-when-tree-submap-p
  (implies (tree-submap-p x y)
           (tree-submap-p (tree->right x) y))
  :enable tree-submap-p)

(defrule tree-submap-p-of-tree->right-when-tree-submap-p-cheap
  (implies (tree-submap-p x y)
           (tree-submap-p (tree->right x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-submap-p-of-tree->right-when-tree-submap-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-submap-p-of-arg1-and-tree->left-of-arg1
  (implies (bstp x)
           (equal (tree-submap-p x (tree->left x))
                  (tree-empty-p x)))
  :enable tree-submap-p)

(defrule tree-submap-p-of-arg1-and-tree->right-of-arg1
  (implies (bstp x)
           (equal (tree-submap-p x (tree->right x))
                  (tree-empty-p x)))
  :enable tree-submap-p)

;;;;;;;;;;;;;;;;;;;;

;; TODO: Simplify treeset proof
(defrule reflexivity-of-tree-submap-p-when-bstp
  (implies (bstp tree)
           (tree-submap-p tree tree))
  :induct (tree-induct tree)
  :enable (tree-submap-p
           tree-submap-p-when-tree-submap-p-of-arg1-and-tree->left
           tree-submap-p-when-tree-submap-p-of-arg1-and-tree->right))

;; Note: antisymmetry is proved separately in antisymmetry.lisp

(defrule transitivity-of-tree-submap-p
  (implies (and (tree-submap-p x y)
                (tree-submap-p y z))
           (tree-submap-p x z))
  :induct t
  :enable tree-submap-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-submap-p-of-tree->left
  (implies (bstp tree)
           (tree-submap-p (tree->left tree) tree))
  :use reflexivity-of-tree-submap-p-when-bstp
  :disable reflexivity-of-tree-submap-p-when-bstp)

(defrule tree-submap-p-of-tree->right
  (implies (bstp tree)
           (tree-submap-p (tree->right tree) tree))
  :use reflexivity-of-tree-submap-p-when-bstp
  :disable reflexivity-of-tree-submap-p-when-bstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-submap-p-when-not-tree-assoc-of-tree->head
  (implies (and (not (tree-empty-p x))
                (not (treeset::in (tree-element->key (tree->head x))
                                  (tree-key-set y))))
           (not (tree-submap-p x y))))

(defrule tree-submap-p-when-not-tree-assoc-of-tree->head-cheap
  (implies (and (not (treeset::in (tree-element->key (tree->head x))
                                  (tree-key-set y)))
                (not (tree-empty-p x)))
           (not (tree-submap-p x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by tree-submap-p-when-not-tree-assoc-of-tree->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-submap-p-of-arg1-and-tree-split.left
  (implies (and (bstp y)
                (<<-all-l x a))
           (equal (tree-submap-p x (mv-nth 1 (tree-split a y)))
                  (tree-submap-p x y)))
  :induct t
  :enable tree-submap-p)

(defrule tree-submap-p-of-arg1-and-tree-split.right
  (implies (and (bstp y)
                (<<-all-r a x))
           (equal (tree-submap-p x (mv-nth 2 (tree-split a y)))
                  (tree-submap-p x y)))
  :induct t
  :enable tree-submap-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk tree-submap-p-sk (x y)
  :parents (implementation)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (key)
    (non-exec
      (implies (treeset::in key (tree-key-set x))
               (and (treeset::in key (tree-key-set y))
                    (equal (tree-lookup key x)
                           (tree-lookup key y)))))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-submap-p-sk)))

(defrule tree-submap-p-sk-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-submap-p-sk x0 y)
                  (tree-submap-p-sk x1 y)))
  :rule-classes :congruence
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule lemma
     (implies (and (tree-equiv x0 x1)
                   (tree-submap-p-sk x0 y))
              (tree-submap-p-sk x1 y))
     :expand ((tree-submap-p-sk x1 y))
     :enable tree-submap-p-sk-necc)))

(defrule tree-submap-p-sk-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-submap-p-sk x y0)
                  (tree-submap-p-sk x y1)))
  :rule-classes :congruence
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule lemma
     (implies (and (tree-equiv y0 y1)
                   (tree-submap-p-sk x y0))
              (tree-submap-p-sk x y1))
     :expand ((tree-submap-p-sk x y1))
     :enable tree-submap-p-sk-necc)))

(defruled tree-submap-p-sk-of-tree->left
  (implies (and (tree-submap-p-sk x y)
                (bstp x))
           (tree-submap-p-sk (tree->left x) y))
  :expand (tree-submap-p-sk (tree->left x) y)
  :use (:instance tree-submap-p-sk-necc
                  (key (tree-submap-p-sk-witness (tree->left x) y))))

(defruled tree-submap-p-sk-of-tree->right
  (implies (and (tree-submap-p-sk x y)
                (bstp x))
           (tree-submap-p-sk (tree->right x) y))
  :expand (tree-submap-p-sk (tree->right x) y)
  :use (:instance tree-submap-p-sk-necc
                  (key (tree-submap-p-sk-witness (tree->right x) y))))

(defruled tree-submap-p-becomes-tree-submap-p-sk
  (implies (bstp x)
           (equal (tree-submap-p x y)
                  (tree-submap-p-sk x y)))
  :rule-classes :definition
  :use (tree-submap-p-sk-when-tree-submap-p
        tree-submap-p-when-tree-submap-p-sk)

  :prep-lemmas
  ((defruled tree-submap-p-sk-when-tree-submap-p
     (implies (tree-submap-p x y)
              (tree-submap-p-sk x y))
     :enable tree-submap-p-sk)

   (defruled tree-submap-p-when-tree-submap-p-sk
     (implies (and (tree-submap-p-sk x y)
                   (bstp x))
              (tree-submap-p x y))
     :induct t
     :hints ('(:use (:instance tree-submap-p-sk-necc
                               (key (tree-element->key (tree->head x))))))
     :enable (tree-submap-p
              tree-submap-p-sk-of-tree->left
              tree-submap-p-sk-of-tree->right))))

(defruled tree-submap-p-sk-becomes-tree-submap-p
  (implies (bstp x)
           (equal (tree-submap-p-sk x y)
                  (tree-submap-p x y)))
  :rule-classes :definition
  :by tree-submap-p-becomes-tree-submap-p-sk)

(defruled tree-submap-p-pick-a-point
  (implies (bstp x)
           (equal (tree-submap-p x y)
                  (let ((key (tree-submap-p-sk-witness x y)))
                    (implies (treeset::in key (tree-key-set x))
                             (and (treeset::in key (tree-key-set y))
                                  (equal (tree-lookup key x)
                                         (tree-lookup key y)))))))
  :rule-classes :definition
  :use (tree-submap-p-becomes-tree-submap-p-sk
        tree-submap-p-sk))

(defruled tree-submap-p-pick-a-point-polar
  (implies (and (syntaxp (acl2::want-to-weaken (tree-submap-p x y)))
                (bstp x))
           (equal (tree-submap-p x y)
                  (let ((key (tree-submap-p-sk-witness x y)))
                    (implies (treeset::in key (tree-key-set x))
                             (and (treeset::in key (tree-key-set y))
                                  (equal (tree-lookup key x)
                                         (tree-lookup key y)))))))
  :rule-classes :definition
  :by tree-submap-p-pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule tree-sumbap-p-when-<<-all-l-of-head
  (implies (and (bstp x)
                (bstp y)
                (not (tree-empty-p y))
                (<<-all-l x (tree-element->key (tree->head y))))
           (equal (tree-submap-p x y)
                  (tree-submap-p x (tree->left y))))
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule lemma
     (implies (and (bstp x)
                   (bstp y)
                   (not (tree-empty-p y))
                   (<<-all-l x (tree-element->key (tree->head y)))
                   (tree-submap-p x y))
              (tree-submap-p x (tree->left y)))
     ;; TODO: improve proof
     :use ((:instance treeset::in-when-subset-and-in
                      (x (tree-key-set x))
                      (y (tree-key-set y))
                      (a (tree-submap-p-sk-witness x (tree->left y))))
           (:instance tree-lookup-when-tree-submap-p-and-in-of-tree-key-set
                      (key (tree-submap-p-sk-witness x (tree->left y)))))
     :enable tree-submap-p-pick-a-point-polar
     :disable (treeset::in-when-in-and-subset
               treeset::in-when-subset-and-in
               tree-lookup-when-in-of-tree-key-set-and-tree-submap-p-forward-chaining))))

(defrule tree-sumbap-p-when-<<-all-r-of-head
  (implies (and (bstp x)
                (bstp y)
                (not (tree-empty-p y))
                (<<-all-r (tree-element->key (tree->head y)) x))
           (equal (tree-submap-p x y)
                  (tree-submap-p x (tree->right y))))
  :enable acl2::equal-of-booleans-cheap
  :prep-lemmas
  ((defrule lemma
     (implies (and (bstp x)
                   (bstp y)
                   (not (tree-empty-p y))
                   (<<-all-r (tree-element->key (tree->head y)) x)
                   (tree-submap-p x y))
              (tree-submap-p x (tree->right y)))
     ;; TODO: improve proof
     :use ((:instance treeset::in-when-subset-and-in
                      (x (tree-key-set x))
                      (y (tree-key-set y))
                      (a (tree-submap-p-sk-witness x (tree->right y))))
           (:instance tree-lookup-when-tree-submap-p-and-in-of-tree-key-set
                      (key (tree-submap-p-sk-witness x (tree->right y)))))
     :enable tree-submap-p-pick-a-point-polar
     :disable (treeset::in-when-in-and-subset
               treeset::in-when-subset-and-in
               tree-lookup-when-in-of-tree-key-set-and-tree-submap-p-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-tree-submap-p
  ((x treep)
   (y treep))
  :returns (yes/no booleanp)
  :parents (tree-submap-p)
  :short "Fast submap check."
  (cond ((tree-empty-p x) t)
        ((tree-empty-p y) nil)
        (t (mv-let (assoc left right)
                   (tree-split (tree-element->key (tree->head x)) y)
             (and assoc
                  (equal (tree-element->val (tree->head x))
                         (cdr assoc))
                  (fast-tree-submap-p (tree->left x) left)
                  (fast-tree-submap-p (tree->right x) right)))))
  :measure (acl2-count x))

;;;;;;;;;;;;;;;;;;;;

(defrule fast-tree-submap-p-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (fast-tree-submap-p x0 y)
                  (fast-tree-submap-p x1 y)))
  :rule-classes :congruence
  :induct t
  :enable fast-tree-submap-p)

(defrule fast-tree-submap-p-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (fast-tree-submap-p x y0)
                  (fast-tree-submap-p x y1)))
  :rule-classes :congruence
  :induct t
  :enable fast-tree-submap-p)

(defrule fast-tree-submap-p-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (equal (fast-tree-submap-p x y)
                  (tree-submap-p x y)))
  :induct (fast-tree-submap-p x y)
  :enable (fast-tree-submap-p
           tree-submap-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-fast-tree-submap-p
  ((x acl2-number-treep)
   (y acl2-number-treep))
  :guard (bstp y)
  (mbe :logic (fast-tree-submap-p x y)
       :exec
       (cond ((tree-empty-p x) t)
             ((tree-empty-p y) nil)
             (t (mv-let (assoc left right)
                        (acl2-number-tree-split
                          (tree-element->key (tree->head x))
                          y)
                  (and assoc
                       (equal (tree-element->val (tree->head x))
                              (cdr assoc))
                       (acl2-number-fast-tree-submap-p (tree->left x) left)
                       (acl2-number-fast-tree-submap-p (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable fast-tree-submap-p
                                           acl2-number-fast-tree-submap-p
                                           tree-keys-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-fast-tree-submap-p
  ((x symbol-treep)
   (y symbol-treep))
  :guard (bstp y)
  (mbe :logic (fast-tree-submap-p x y)
       :exec
       (cond ((tree-empty-p x) t)
             ((tree-empty-p y) nil)
             (t (mv-let (assoc left right)
                        (symbol-tree-split
                          (tree-element->key (tree->head x))
                          y)
                  (and assoc
                       (equal (tree-element->val (tree->head x))
                              (cdr assoc))
                       (symbol-fast-tree-submap-p (tree->left x) left)
                       (symbol-fast-tree-submap-p (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable fast-tree-submap-p
                                           symbol-fast-tree-submap-p
                                           tree-keys-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-fast-tree-submap-p
  ((x eqlable-treep)
   (y eqlable-treep))
  :guard (bstp y)
  (mbe :logic (fast-tree-submap-p x y)
       :exec
       (cond ((tree-empty-p x) t)
             ((tree-empty-p y) nil)
             (t (mv-let (assoc left right)
                        (eqlable-tree-split
                          (tree-element->key (tree->head x))
                          y)
                  (and assoc
                       (equal (tree-element->val (tree->head x))
                              (cdr assoc))
                       (eqlable-fast-tree-submap-p (tree->left x) left)
                       (eqlable-fast-tree-submap-p (tree->right x) right))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable fast-tree-submap-p
                                           eqlable-fast-tree-submap-p
                                           tree-keys-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-submap-p-extra-rules
  '(tree-submap-p-when-tree-submap-p-of-arg1-and-tree->left
    tree-submap-p-when-tree-submap-p-of-arg1-and-tree->right
    tree-submap-p-of-tree->left-when-tree-submap-p
    tree-submap-p-of-tree->right-when-tree-submap-p
    tree-submap-p-when-not-tree-assoc-of-tree->head))
