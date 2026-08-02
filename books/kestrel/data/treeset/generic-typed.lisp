; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "internal/tree-defs")
(include-book "internal/in-defs")
(include-book "set-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "cardinality-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "iter-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "set"))
(local (include-book "iter"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "cardinality"))
(local (include-book "subset"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "internal/bst"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub genericp (*) => *)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-all-genericp ((set setp))
  :returns (yes/no booleanp)
  (or (emptyp set)
      (and (genericp (min set))
           (set-all-genericp (delete (min set) set))))
  :measure (cardinality set))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-genericp)))

(defrule set-all-genericp-type-prescription
  (booleanp (set-all-genericp set))
  :rule-classes ((:type-prescription :typed-term (set-all-genericp set))))

(defrule set-all-genericp-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (set-all-genericp set0)
                  (set-all-genericp set1)))
  :rule-classes :congruence
  :expand ((set-all-genericp set0)
           (set-all-genericp set1)))

;; TODO: alt definition: head/tail

(defruled set-all-genericp-when-emptyp
  (implies (emptyp set)
           (set-all-genericp set))
  :enable set-all-genericp)

(defrule set-all-genericp-when-emptyp-cheap
  (implies (emptyp set)
           (set-all-genericp set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-genericp-when-emptyp)

(defrule set-all-genericp-of-empty
  (set-all-genericp (empty))
  :enable set-all-genericp-when-emptyp)

(defrule genericp-when-set-all-genericp-and-in
  (implies (and (set-all-genericp set)
                (in x set))
           (genericp x))
  :induct t
  :enable set-all-genericp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk set-all-genericp-sk (set)
  :returns (yes/no booleanp)
  (forall (elem)
    (non-exec
      (implies (in elem set)
               (genericp elem)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t set-all-genericp-sk)))

(defrule set-all-genericp-sk-type-prescription
  (booleanp (set-all-genericp-sk set))
  :rule-classes ((:type-prescription :typed-term (set-all-genericp-sk set))))

(defruledl set-all-genericp-sk-when-set-all-genericp
  (implies (set-all-genericp set)
           (set-all-genericp-sk set))
  :enable set-all-genericp-sk)

(defruledl genericp-of-min-when-set-all-genericp-sk
  (implies (and (set-all-genericp-sk set)
                (not (emptyp set)))
           (genericp (min set)))
  :enable set-all-genericp-sk-necc)

(defruledl set-all-genericp-sk-of-delete
  (implies (set-all-genericp-sk set)
           (set-all-genericp-sk (delete x set)))
  :expand (set-all-genericp-sk (delete x set))
  :enable set-all-genericp-sk-necc)

(defruledl set-all-genericp-when-set-all-genericp-sk
  (implies (set-all-genericp-sk set)
           (set-all-genericp set))
  :induct t
  :enable (set-all-genericp
           genericp-of-min-when-set-all-genericp-sk
           set-all-genericp-sk-of-delete))

(defruled set-all-genericp-becomes-set-all-genericp-sk
  (equal (set-all-genericp set)
         (set-all-genericp-sk set))
  :use (set-all-genericp-sk-when-set-all-genericp
        set-all-genericp-when-set-all-genericp-sk))

(defthy set-all-genericp-pick-a-point
  '(set-all-genericp-becomes-set-all-genericp-sk
    set-all-genericp-sk))

(defruled set-all-genericp-becomes-set-all-genericp-sk-polar
  (implies (syntaxp (acl2::want-to-weaken (set-all-genericp set)))
           (equal (set-all-genericp set)
                  (set-all-genericp-sk set)))
  :by set-all-genericp-becomes-set-all-genericp-sk)

(defthy set-all-genericp-pick-a-point-polar
  '(set-all-genericp-becomes-set-all-genericp-sk-polar
    set-all-genericp-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-all-genericp ((tree treep))
  (or (tree-empty-p tree)
      (and (genericp (tree-element->val (tree->head tree)))
           (tree-all-genericp (tree->left tree))
           (tree-all-genericp (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defrulel genericp-when-tree-all-genericp-and-tree-in
  (implies (and (tree-all-genericp tree)
                (tree-in x tree))
           (genericp x))
  :induct t
  :enable tree-all-genericp)

(defruledl set-all-genericp-sk-when-tree-all-genericp
  (implies (and (tree-all-genericp set)
                (setp set))
           (set-all-genericp-sk set))
  :enable (set-all-genericp-sk
           in))

(defrulel set-all-genericp-sk-of-tree->left
  (implies (and (setp set)
                (set-all-genericp-sk set))
           (set-all-genericp-sk (tree->left set)))
  :expand (set-all-genericp-sk (tree->left set))
  :enable (set-all-genericp-sk-necc
           break-abstraction
           in))

(defrulel set-all-genericp-sk-of-tree->right
  (implies (and (setp set)
                (set-all-genericp-sk set))
           (set-all-genericp-sk (tree->right set)))
  :expand (set-all-genericp-sk (tree->right set))
  :enable (set-all-genericp-sk-necc
           break-abstraction
           in))

(defruledl tree-all-genericp-when-set-all-genericp-sk
  (implies (and (setp set)
                (set-all-genericp-sk set))
           (tree-all-genericp set))
  :induct t
  :hints ('(:use (:instance set-all-genericp-sk-necc
                            (elem (tree-element->val (tree->head set))))))
  :enable (tree-all-genericp
           break-abstraction
           in))

(defruled tree-all-genericp-becomes-tree-all-genericp-sk
  (implies (setp set)
           (equal (tree-all-genericp set)
                  (set-all-genericp-sk set)))
  :use (set-all-genericp-sk-when-tree-all-genericp
        tree-all-genericp-when-set-all-genericp-sk))

(defruled tree-all-genericp-becomes-set-all-genericp
  (implies (setp set)
           (equal (tree-all-genericp set)
                  (set-all-genericp (double-rewrite set))))
  :use (tree-all-genericp-becomes-tree-all-genericp-sk
        set-all-genericp-becomes-set-all-genericp-sk))

(defruled set-all-genericp-becomes-tree-all-genericp
  (equal (set-all-genericp set)
         (tree-all-genericp (fix set)))
  :use (:instance tree-all-genericp-becomes-set-all-genericp
                  (set (fix set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule genericp-of-min-under-iff-when-set-all-genericp
  (implies (and (set-all-genericp set)
                (not (emptyp set)))
           (genericp (min set))))

(defrule genericp-of-max-under-iff-when-set-all-genericp
  (implies (and (set-all-genericp set)
                (not (emptyp set)))
           (genericp (max set))))

(defrule genericp-of-head-under-iff-when-set-all-genericp
  (implies (and (set-all-genericp set)
                (not (emptyp set)))
           (genericp (head set))))

(defrule set-all-genericp-when-subset-and-set-all-genericp
  (implies (and (subset x y)
                (set-all-genericp y))
           (set-all-genericp x))
  :enable set-all-genericp-pick-a-point-polar)

;; The same fact with the hypotheses exchanged: here the containing set is
;; found in the context and the containment itself is left to rewriting, which
;; suits goals whose subset fact is a rule rather than a hypothesis. Left
;; disabled: with both orders enabled every all-elements goal would search the
;; context twice.

(defruled set-all-genericp-when-set-all-genericp-and-subset
  (implies (and (set-all-genericp y)
                (subset x y))
           (set-all-genericp x))
  :by set-all-genericp-when-subset-and-set-all-genericp)

(defrule set-all-genericp-of-insert
  (equal (set-all-genericp (insert x set))
         (and (genericp x)
              (set-all-genericp set)))
  :enable (set-all-genericp-pick-a-point-polar
           acl2::equal-of-booleans-cheap))

(defrule set-all-genericp-of-delete
  (implies (set-all-genericp set)
           (set-all-genericp (delete x set)))
  :enable set-all-genericp-pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check, run with an @(see iterator) instead of by repeatedly taking
;; the minimum. The guard rules out a rewound iterator, which has no element to
;; read; @(tsee iter-min) never produces one and @(tsee next) never reaches one, so
;; a forward walk stays within it.

(define iter-all-genericp ((iter iterp))
  :guard (not (before-firstp iter))
  (or (after-lastp iter)
      (and (genericp (value iter))
           (iter-all-genericp (next iter))))
  :measure (nexts iter))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-all-genericp)))

(defrule iter-all-genericp-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (iter-all-genericp iter0)
                  (iter-all-genericp iter1)))
  :rule-classes :congruence
  :expand ((iter-all-genericp iter0)
           (iter-all-genericp iter1)))

;; If every element of the set is generic then so is every value a walk
;; produces, since each value it reads is an element. This is the direction a
;; caller needs in order to conclude that a walk succeeds.

(defruledl genericp-of-value-when-set-all-genericp
  (implies (and (set-all-genericp (from-iter iter))
                (has-valuep iter))
           (genericp (value iter)))
  :enable set-all-genericp-pick-a-point
  :use (:instance set-all-genericp-sk-necc
                  (elem (value iter))
                  (set (from-iter iter))))

(defruled iter-all-genericp-when-set-all-genericp
  (implies (and (set-all-genericp (from-iter iter))
                (not (before-firstp iter)))
           (iter-all-genericp iter))
  :induct (iter-all-genericp iter)
  :enable (iter-all-genericp
           genericp-of-value-when-set-all-genericp))

(defrule iter-all-genericp-when-after-lastp
  (implies (after-lastp iter)
           (iter-all-genericp iter))
  :enable iter-all-genericp)

;; The converse holds only of a walk that starts at the beginning. An iterator
;; part way along has already passed some elements and will never read them, so
;; it can succeed over a set that is not all generic. The correspondence is
;; therefore stated at @(tsee iter-min), where nothing has been passed yet.
;;
;; The proof is an induction along the walk, run on the public step laws: a
;; step reads the least of what lies ahead, so every element ahead of a
;; succeeding walk is eventually read. At @(tsee iter-min) nothing is behind,
;; so that covers the whole set.

(defruledl genericp-when-in-of-after
  (implies (and (in x (after iter))
                (iter-all-genericp iter))
           (genericp x))
  :induct (iter-all-genericp iter)
  :expand ((iter-all-genericp iter)
           (iter-all-genericp (next iter)))
  :enable (iter-all-genericp
           not-emptyp-when-in))

;; The first value a walk reads is the minimum, and reading it succeeds over a
;; nonempty set.

(defruledl genericp-of-min-when-iter-all-genericp-of-iter-min
  (implies (and (iter-all-genericp (iter-min set))
                (not (emptyp set)))
           (genericp (min set)))
  :expand ((iter-all-genericp (iter-min set))))

;; Any element is either that minimum or lies ahead of the fresh iterator,
;; since nothing is behind it.

(defruledl genericp-when-in-and-iter-all-genericp-of-iter-min
  (implies (and (in x set)
                (iter-all-genericp (iter-min set)))
           (genericp x))
  :use ((:instance in-of-from-iter-when-has-valuep
                   (iter (iter-min set))))
  :enable (genericp-when-in-of-after
           genericp-of-min-when-iter-all-genericp-of-iter-min
           not-emptyp-when-in)
  :disable in-of-from-iter-when-has-valuep)

;; So a walk that starts at the beginning reads every element, and the two
;; checks agree.

(defruled set-all-genericp-when-iter-all-genericp-of-iter-min
  (implies (iter-all-genericp (iter-min set))
           (set-all-genericp set))
  :enable (set-all-genericp-pick-a-point
           genericp-when-in-and-iter-all-genericp-of-iter-min))

;; The stub in the body means the recursion is not visibly boolean, so this has
;; to be said rather than read off the type prescription.

(defrule booleanp-of-iter-all-genericp
  (booleanp (iter-all-genericp iter))
  :rule-classes (:rewrite :type-prescription)
  :induct (iter-all-genericp iter)
  :enable iter-all-genericp)

(defrule iter-all-genericp-of-iter-min
  (equal (iter-all-genericp (iter-min set))
         (set-all-genericp set))
  :enable set-all-genericp-when-iter-all-genericp-of-iter-min
  :use (:instance iter-all-genericp-when-set-all-genericp
                  (iter (iter-min set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local
    (define set-all-acl2-numberp-alt (set)
      (or (emptyp set)
          (and (acl2-numberp (min set))
               (set-all-acl2-numberp-alt (delete (min set) set))))
      :measure (cardinality set)
      :verify-guards nil))

  (defrulel tree-all-acl2-numberp-becomes-set-all-acl2-numberp-alt
    (implies (setp set)
             (equal (tree-all-acl2-numberp set)
                    (set-all-acl2-numberp-alt set)))
    :use (:functional-instance
           tree-all-genericp-becomes-set-all-genericp
           (genericp acl2-numberp)
           (set-all-genericp set-all-acl2-numberp-alt)
           (tree-all-genericp tree-all-acl2-numberp))
    :enable (set-all-acl2-numberp-alt
             tree-all-acl2-numberp))

  (defruled set-all-acl2-numberp-alt-definition
    (equal (set-all-acl2-numberp set)
           (or (emptyp set)
               (and (acl2-numberp (min set))
                    (set-all-acl2-numberp (delete (min set) set)))))
    :rule-classes :definition
    :enable (set-all-acl2-numberp
             set-all-acl2-numberp-alt
             tree-all-acl2-numberp-becomes-set-all-acl2-numberp-alt)))

;;;;;;;;;;;;;;;;;;;;

(defruled set-all-acl2-numberp-when-emptyp
  (implies (emptyp set)
           (set-all-acl2-numberp set))
  :use (:functional-instance set-all-genericp-when-emptyp
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp))
  :enable set-all-acl2-numberp-alt-definition)

(defrule set-all-acl2-numberp-when-emptyp-cheap
  (implies (emptyp set)
           (set-all-acl2-numberp set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-acl2-numberp-when-emptyp)

(defrule set-all-acl2-numberp-of-empty
  (set-all-acl2-numberp (empty))
  :use (:functional-instance set-all-genericp-of-empty
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule acl2-numberp-when-set-all-acl2-numberp-and-in
  (implies (and (set-all-acl2-numberp set)
                (in x set))
           (acl2-numberp x))
  :use (:functional-instance genericp-when-set-all-genericp-and-in
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule acl2-numberp-of-min-under-iff-when-set-all-acl2-numberp
  (implies (and (set-all-acl2-numberp set)
                (not (emptyp set)))
           (acl2-numberp (min set)))
  :use (:functional-instance genericp-of-min-under-iff-when-set-all-genericp
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule acl2-numberp-of-max-under-iff-when-set-all-acl2-numberp
  (implies (and (set-all-acl2-numberp set)
                (not (emptyp set)))
           (acl2-numberp (max set)))
  :use (:functional-instance genericp-of-max-under-iff-when-set-all-genericp
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule acl2-numberp-of-head-under-iff-when-set-all-acl2-numberp
  (implies (and (set-all-acl2-numberp set)
                (not (emptyp set)))
           (acl2-numberp (head set)))
  :use (:functional-instance genericp-of-head-under-iff-when-set-all-genericp
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule set-all-acl2-numberp-when-subset-and-set-all-acl2-numberp
  (implies (and (subset x y)
                (set-all-acl2-numberp y))
           (set-all-acl2-numberp x))
  :use (:functional-instance set-all-genericp-when-subset-and-set-all-genericp
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule set-all-acl2-numberp-of-insert
  (equal (set-all-acl2-numberp (insert x set))
         (and (acl2-numberp x)
              (set-all-acl2-numberp set)))
  :use (:functional-instance set-all-genericp-of-insert
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

(defrule set-all-acl2-numberp-of-delete
  (implies (set-all-acl2-numberp set)
           (set-all-acl2-numberp (delete x set)))
  :use (:functional-instance set-all-genericp-of-delete
                             (genericp acl2-numberp)
                             (set-all-genericp set-all-acl2-numberp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local
    (define set-all-symbolp-alt (set)
      (or (emptyp set)
          (and (symbolp (min set))
               (set-all-symbolp-alt (delete (min set) set))))
      :measure (cardinality set)
      :verify-guards nil))

  (defrulel tree-all-symbolp-becomes-set-all-symbolp-alt
    (implies (setp set)
             (equal (tree-all-symbolp set)
                    (set-all-symbolp-alt set)))
    :use (:functional-instance
           tree-all-genericp-becomes-set-all-genericp
           (genericp symbolp)
           (set-all-genericp set-all-symbolp-alt)
           (tree-all-genericp tree-all-symbolp))
    :enable (set-all-symbolp-alt
             tree-all-symbolp))

  (defruled set-all-symbolp-alt-definition
    (equal (set-all-symbolp set)
           (or (emptyp set)
               (and (symbolp (min set))
                    (set-all-symbolp (delete (min set) set)))))
    :rule-classes :definition
    :enable (set-all-symbolp
             set-all-symbolp-alt
             tree-all-symbolp-becomes-set-all-symbolp-alt)))

;;;;;;;;;;;;;;;;;;;;

(defruled set-all-symbolp-when-emptyp
  (implies (emptyp set)
           (set-all-symbolp set))
  :use (:functional-instance set-all-genericp-when-emptyp
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp))
  :enable set-all-symbolp-alt-definition)

(defrule set-all-symbolp-when-emptyp-cheap
  (implies (emptyp set)
           (set-all-symbolp set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-symbolp-when-emptyp)

(defrule set-all-symbolp-of-empty
  (set-all-symbolp (empty))
  :use (:functional-instance set-all-genericp-of-empty
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule symbolp-when-set-all-symbolp-and-in
  (implies (and (set-all-symbolp set)
                (in x set))
           (symbolp x))
  :use (:functional-instance genericp-when-set-all-genericp-and-in
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule symbolp-of-min-under-iff-when-set-all-symbolp
  (implies (and (set-all-symbolp set)
                (not (emptyp set)))
           (symbolp (min set)))
  :use (:functional-instance genericp-of-min-under-iff-when-set-all-genericp
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule symbolp-of-max-under-iff-when-set-all-symbolp
  (implies (and (set-all-symbolp set)
                (not (emptyp set)))
           (symbolp (max set)))
  :use (:functional-instance genericp-of-max-under-iff-when-set-all-genericp
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule symbolp-of-head-under-iff-when-set-all-symbolp
  (implies (and (set-all-symbolp set)
                (not (emptyp set)))
           (symbolp (head set)))
  :use (:functional-instance genericp-of-head-under-iff-when-set-all-genericp
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule set-all-symbolp-when-subset-and-set-all-symbolp
  (implies (and (subset x y)
                (set-all-symbolp y))
           (set-all-symbolp x))
  :use (:functional-instance set-all-genericp-when-subset-and-set-all-genericp
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule set-all-symbolp-of-insert
  (equal (set-all-symbolp (insert x set))
         (and (symbolp x)
              (set-all-symbolp set)))
  :use (:functional-instance set-all-genericp-of-insert
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

(defrule set-all-symbolp-of-delete
  (implies (set-all-symbolp set)
           (set-all-symbolp (delete x set)))
  :use (:functional-instance set-all-genericp-of-delete
                             (genericp symbolp)
                             (set-all-genericp set-all-symbolp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local
    (define set-all-eqlablep-alt (set)
      (or (emptyp set)
          (and (eqlablep (min set))
               (set-all-eqlablep-alt (delete (min set) set))))
      :measure (cardinality set)
      :verify-guards nil))

  (defrulel tree-all-eqlablep-becomes-set-all-eqlablep-alt
    (implies (setp set)
             (equal (tree-all-eqlablep set)
                    (set-all-eqlablep-alt set)))
    :use (:functional-instance
           tree-all-genericp-becomes-set-all-genericp
           (genericp eqlablep)
           (set-all-genericp set-all-eqlablep-alt)
           (tree-all-genericp tree-all-eqlablep))
    :enable (set-all-eqlablep-alt
             tree-all-eqlablep))

  (defruled set-all-eqlablep-alt-definition
    (equal (set-all-eqlablep set)
           (or (emptyp set)
               (and (eqlablep (min set))
                    (set-all-eqlablep (delete (min set) set)))))
    :rule-classes :definition
    :enable (set-all-eqlablep
             set-all-eqlablep-alt
             tree-all-eqlablep-becomes-set-all-eqlablep-alt)))

;;;;;;;;;;;;;;;;;;;;

(defruled set-all-eqlablep-when-emptyp
  (implies (emptyp set)
           (set-all-eqlablep set))
  :use (:functional-instance set-all-genericp-when-emptyp
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep))
  :enable set-all-eqlablep-alt-definition)

(defrule set-all-eqlablep-when-emptyp-cheap
  (implies (emptyp set)
           (set-all-eqlablep set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-eqlablep-when-emptyp)

(defrule set-all-eqlablep-of-empty
  (set-all-eqlablep (empty))
  :use (:functional-instance set-all-genericp-of-empty
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule eqlablep-when-set-all-eqlablep-and-in
  (implies (and (set-all-eqlablep set)
                (in x set))
           (eqlablep x))
  :use (:functional-instance genericp-when-set-all-genericp-and-in
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule eqlablep-of-min-under-iff-when-set-all-eqlablep
  (implies (and (set-all-eqlablep set)
                (not (emptyp set)))
           (eqlablep (min set)))
  :use (:functional-instance genericp-of-min-under-iff-when-set-all-genericp
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule eqlablep-of-max-under-iff-when-set-all-eqlablep
  (implies (and (set-all-eqlablep set)
                (not (emptyp set)))
           (eqlablep (max set)))
  :use (:functional-instance genericp-of-max-under-iff-when-set-all-genericp
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule eqlablep-of-head-under-iff-when-set-all-eqlablep
  (implies (and (set-all-eqlablep set)
                (not (emptyp set)))
           (eqlablep (head set)))
  :use (:functional-instance genericp-of-head-under-iff-when-set-all-genericp
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule set-all-eqlablep-when-subset-and-set-all-eqlablep
  (implies (and (subset x y)
                (set-all-eqlablep y))
           (set-all-eqlablep x))
  :use (:functional-instance set-all-genericp-when-subset-and-set-all-genericp
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule set-all-eqlablep-of-insert
  (equal (set-all-eqlablep (insert x set))
         (and (eqlablep x)
              (set-all-eqlablep set)))
  :use (:functional-instance set-all-genericp-of-insert
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule set-all-eqlablep-of-delete
  (implies (set-all-eqlablep set)
           (set-all-eqlablep (delete x set)))
  :use (:functional-instance set-all-genericp-of-delete
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))
