; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "tree-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-subset-p
  ((x treep)
   (y treep))
  :parents (implementation)
  :short "Check if one set is a tree-subset-p of the other."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(m))$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n\\log(m/n))$), where
      @($n < m$). This may be implemented similar to @(tsee diff).)"))
  :guard (bstp y)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p x)
      (and (mbe :logic (tree-in (tagged-element->elem (tree->head x)) y)
                :exec (tree-search-in (tagged-element->elem (tree->head x)) y))
           (tree-subset-p (tree->left x) y)
           (tree-subset-p (tree->right x) y))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-subset-p)))

(defrule tree-subset-p-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-subset-p x0 y)
                  (tree-subset-p x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-subset-p)

(defrule tree-subset-p-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-subset-p x y0)
                  (tree-subset-p x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-subset-p)

(defrule tree-subset-p-when-tree-empty-p-of-arg1
  (implies (tree-empty-p x)
           (tree-subset-p x y))
  :enable tree-subset-p)

(defrule tree-subset-p-when-tree-empty-p-of-arg2
  (implies (tree-empty-p y)
           (equal (tree-subset-p x y)
                  (tree-empty-p x)))
  :enable tree-subset-p)

;; TODO: disable by default?
(defrule tree-in-when-tree-in-and-tree-subset-p
  (implies (and (tree-in a x)
                (tree-subset-p x y))
           (tree-in a y))
  :induct t
  :enable tree-subset-p)

;; TODO: disable by default?
(defrule tree-in-when-tree-subset-p-and-tree-in
  (implies (and (tree-subset-p x y)
                (tree-in a x))
           (tree-in a y))
  :by tree-in-when-tree-in-and-tree-subset-p)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
  (implies (tree-subset-p x (tree->left y))
           (tree-subset-p x y))
  :induct t
  :enable tree-subset-p)

(defrule tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left-forward-chaining
  (implies (tree-subset-p x (tree->left y))
           (tree-subset-p x y))
  :rule-classes :forward-chaining
  :by tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left)

(defruled tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right
  (implies (tree-subset-p x (tree->right y))
           (tree-subset-p x y))
  :induct t
  :enable tree-subset-p)

(defrule tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right-forward-chaining
  (implies (tree-subset-p x (tree->right y))
           (tree-subset-p x y))
  :rule-classes :forward-chaining
  :by tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)

;;;;;;;;;;;;;;;;;;;;

(defruled tree-subset-p-of-tree->left-when-when-tree-subset-p
  (implies (tree-subset-p x y)
           (tree-subset-p (tree->left x) y))
  :enable tree-subset-p)

(defrule tree-subset-p-of-tree->left-when-when-tree-subset-p-cheap
  (implies (tree-subset-p x y)
           (tree-subset-p (tree->left x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-subset-p-of-tree->left-when-when-tree-subset-p)

(defruled tree-subset-p-of-tree->right-when-when-tree-subset-p
  (implies (tree-subset-p x y)
           (tree-subset-p (tree->right x) y))
  :enable tree-subset-p)

(defrule tree-subset-p-of-tree->right-when-when-tree-subset-p-cheap
  (implies (tree-subset-p x y)
           (tree-subset-p (tree->right x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-subset-p-of-tree->right-when-when-tree-subset-p)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-subset-p-of-arg1-and-tree->left-of-arg1
  (implies (bstp x)
           (equal (tree-subset-p x (tree->left x))
                  (tree-empty-p x)))
  :enable tree-subset-p)

(defrule tree-subset-p-of-arg1-and-tree->right-of-arg1
  (implies (bstp x)
           (equal (tree-subset-p x (tree->right x))
                  (tree-empty-p x)))
  :enable tree-subset-p)

;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (defrulel tree-subset-p-of-tree->left-tree-subset-p-of-tree->right
    (and (tree-subset-p (tree->left x) x)
         (tree-subset-p (tree->right x) x))
    :induct (tree-induct x)
    :enable (tree-subset-p
             tree-in-when-tree-in-of-tree->left
             tree-in-when-tree-in-of-tree->right))

  (defrule tree-subset-p-of-tree->left
    (tree-subset-p (tree->left x) x))

  (defrule tree-subset-p-of-tree->right
    (tree-subset-p (tree->right x) x)))

(defrule tree-subset-p-reflexivity
  (tree-subset-p x x)
  :enable tree-subset-p)

;; Note: antisymmetry is proved separately in antisymmetry.lisp

(defrule tree-subset-p-transitivity
  (implies (and (tree-subset-p x y)
                (tree-subset-p y z))
           (tree-subset-p x z))
  :induct t
  :enable tree-subset-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled tree-subset-p-when-not-tree-in-of-tree->head
  (implies (and (not (tree-empty-p x))
                (not (tree-in (tagged-element->elem (tree->head x)) y)))
           (not (tree-subset-p x y)))
  :disable tree-in-when-tree-in-and-tree-subset-p
  :use ((:instance tree-in-when-tree-in-and-tree-subset-p
                   (a (tagged-element->elem (tree->head x))))))

(defrule tree-subset-p-when-not-tree-in-of-tree->head-cheap
  (implies (and (not (tree-in (tagged-element->elem (tree->head x)) y))
                (not (tree-empty-p x)))
           (not (tree-subset-p x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :by tree-subset-p-when-not-tree-in-of-tree->head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk tree-subset-p-sk (x y)
  :parents (implementation)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
          (implies (tree-in elem x)
                   (tree-in elem y)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-subset-p-sk)))

(defruled tree-subset-p-sk-of-tree->left
  (implies (tree-subset-p-sk x y)
           (tree-subset-p-sk (tree->left x) y))
  :expand (tree-subset-p-sk (tree->left x) y)
  :use (:instance tree-subset-p-sk-necc
                  (elem (tree-subset-p-sk-witness (tree->left x) y))))

(defruled tree-subset-p-sk-of-tree->right
  (implies (tree-subset-p-sk x y)
           (tree-subset-p-sk (tree->right x) y))
  :expand (tree-subset-p-sk (tree->right x) y)
  :use (:instance tree-subset-p-sk-necc
                  (elem (tree-subset-p-sk-witness (tree->right x) y))))

(defruled tree-subset-p-becomes-tree-subset-p-sk
  (equal (tree-subset-p x y)
         (tree-subset-p-sk x y))
  :rule-classes :definition
  :use (tree-subset-p-sk-when-tree-subset-p
        tree-subset-p-when-tree-subset-p-sk)

  :prep-lemmas
  ((defruled tree-subset-p-sk-when-tree-subset-p
     (implies (tree-subset-p x y)
              (tree-subset-p-sk x y))
     :enable tree-subset-p-sk)

   (defruled tree-subset-p-when-tree-subset-p-sk
     (implies (tree-subset-p-sk x y)
              (tree-subset-p x y))
     :induct t
     :hints ('(:use (:instance tree-subset-p-sk-necc
                               (elem (tagged-element->elem (tree->head x))))))
     :enable (tree-subset-p
              tree-subset-p-sk-of-tree->left
              tree-subset-p-sk-of-tree->right))))

(defruled tree-subset-p-sk-becomes-tree-subset-p
  (equal (tree-subset-p-sk x y)
         (tree-subset-p x y))
  :rule-classes :definition
  :by tree-subset-p-becomes-tree-subset-p-sk)

(defrule tree-subset-p-sk-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-subset-p-sk x0 y)
                  (tree-subset-p-sk x1 y)))
  :rule-classes :congruence
  :enable tree-subset-p-sk-becomes-tree-subset-p)

(defrule tree-subset-p-sk-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-subset-p-sk x y0)
                  (tree-subset-p-sk x y1)))
  :rule-classes :congruence
  :enable tree-subset-p-sk-becomes-tree-subset-p)

(defruled tree-subset-p-pick-a-point
  (equal (tree-subset-p x y)
         (let ((elem (tree-subset-p-sk-witness x y)))
           (implies (tree-in elem x)
                    (tree-in elem y))))
  :rule-classes :definition
  :use (tree-subset-p-becomes-tree-subset-p-sk
        tree-subset-p-sk))

(defruled tree-subset-p-pick-a-point-polar
  (implies (syntaxp (acl2::want-to-weaken (tree-subset-p x y)))
           (equal (tree-subset-p x y)
                  (let ((elem (tree-subset-p-sk-witness x y)))
                    (implies (tree-in elem x)
                             (tree-in elem y)))))
  :rule-classes :definition
  :by tree-subset-p-pick-a-point)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-tree-subset-p
  ((x acl2-number-treep)
   (y acl2-number-treep))
  :guard (bstp y)
  (mbe :logic (tree-subset-p x y)
       :exec
       (or (tree-empty-p x)
           (and (mbe :logic (tree-in (tagged-element->elem (tree->head x)) y)
                     :exec (acl2-number-tree-search-in
                             (tagged-element->elem (tree->head x)) y))
                (acl2-number-tree-subset-p (tree->left x) y)
                (acl2-number-tree-subset-p (tree->right x) y))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-subset-p
                                           acl2-number-tree-subset-p
                                           tree-all-acl2-numberp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-tree-subset-p
  ((x symbol-treep)
   (y symbol-treep))
  :guard (bstp y)
  (mbe :logic (tree-subset-p x y)
       :exec
       (or (tree-empty-p x)
           (and (mbe :logic (tree-in (tagged-element->elem (tree->head x)) y)
                     :exec (symbol-tree-search-in
                             (tagged-element->elem (tree->head x)) y))
                (symbol-tree-subset-p (tree->left x) y)
                (symbol-tree-subset-p (tree->right x) y))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-subset-p
                                           symbol-tree-subset-p
                                           tree-all-symbolp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-tree-subset-p
  ((x eqlable-treep)
   (y eqlable-treep))
  :guard (bstp y)
  (mbe :logic (tree-subset-p x y)
       :exec
       (or (tree-empty-p x)
           (and (mbe :logic (tree-in (tagged-element->elem (tree->head x)) y)
                     :exec (eqlable-tree-search-in
                             (tagged-element->elem (tree->head x)) y))
                (eqlable-tree-subset-p (tree->left x) y)
                (eqlable-tree-subset-p (tree->right x) y))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable tree-subset-p
                                           eqlable-tree-subset-p
                                           tree-all-eqlablep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy tree-subset-p-extra-rules
  '(tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
    tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right
    tree-subset-p-of-tree->left-when-when-tree-subset-p
    tree-subset-p-of-tree->right-when-when-tree-subset-p
    tree-subset-p-when-not-tree-in-of-tree->head))
