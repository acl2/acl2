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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in"))
(local (include-book "set"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "cardinality"))
(local (include-book "subset"))
(local (include-book "insert"))
(local (include-book "delete"))

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
          (implies (in elem set)
                   (genericp elem)))
  :verify-guards nil)

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
      (and (genericp (tagged-element->elem (tree->head tree)))
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
                            (elem (tagged-element->elem (tree->head set))))))
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

(defrule set-all-genericp-of-insert
  (implies (set-all-genericp set)
           (equal (set-all-genericp (insert x set))
                  (and (genericp x) t)))
  :enable set-all-genericp-pick-a-point-polar)

(defrule set-all-genericp-of-delete
  (implies (set-all-genericp set)
           (set-all-genericp (delete x set)))
  :enable set-all-genericp-pick-a-point-polar)

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
  (implies (set-all-acl2-numberp set)
           (equal (set-all-acl2-numberp (insert x set))
                  (and (acl2-numberp x) t)))
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
  (implies (set-all-symbolp set)
           (equal (set-all-symbolp (insert x set))
                  (and (symbolp x) t)))
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
  (implies (set-all-eqlablep set)
           (equal (set-all-eqlablep (insert x set))
                  (and (eqlablep x) t)))
  :use (:functional-instance set-all-genericp-of-insert
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))

(defrule set-all-eqlablep-of-delete
  (implies (set-all-eqlablep set)
           (set-all-eqlablep (delete x set)))
  :use (:functional-instance set-all-genericp-of-delete
                             (genericp eqlablep)
                             (set-all-genericp set-all-eqlablep)))
