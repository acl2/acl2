; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")
(include-book "in-defs")
(include-book "subset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "set"))
(local (include-book "in"))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc extensionality
  :parents (treeset)
  :short "Extensional equality of @(see treeset)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "This definition is equivalent to @(see treeset) equality. It is often
       useful to prove equality by rewriting to this quantifier-based form.
       To do so, just enable the @('extensionality') rule.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk ext-equal (x y)
  :parents (extensionality)
  :returns (yes/no booleanp)
  (forall (elem)
          (equal (in elem x)
                 (in elem y)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t ext-equal)))

(defrule ext-equal-type-prescription
  (booleanp (ext-equal x y))
  :rule-classes ((:type-prescription :typed-term (ext-equal x y))))

(defrule ext-equal-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (ext-equal x0 y)
                  (ext-equal x1 y)))
  :rule-classes :congruence
  :use (lemma
        (:instance lemma
                   (x0 x1)
                   (x1 x0)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (equiv x0 x1)
                   (ext-equal x0 y))
              (ext-equal x1 y))
     :expand (ext-equal x1 y)
     :enable ext-equal-necc)))

(defrule ext-equal-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (ext-equal x y0)
                  (ext-equal x y1)))
  :rule-classes :congruence
  :use (lemma
        (:instance lemma
                   (y0 y1)
                   (y1 y0)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (equiv y0 y1)
                   (ext-equal x y0))
              (ext-equal x y1))
     :expand (ext-equal x y1)
     :enable ext-equal-necc)))

(defrule reflexivity-of-ext-equal
  (ext-equal x x)
  :enable ext-equal)

(defruled symmetry-of-ext-equal-weak
  (implies (ext-equal x y)
           (ext-equal y x))
  :expand (ext-equal y x)
  :enable ext-equal-necc)

(defrule symmetry-of-ext-equal
  (equal (ext-equal y x)
         (ext-equal x y))
  :use (symmetry-of-ext-equal-weak
        (:instance symmetry-of-ext-equal-weak
                   (x y)
                   (y x))))

(defruledl subset-when-ext-equal
  (implies (ext-equal x y)
           (subset x y))
  :enable (subset-becomes-subset-sk
           subset-sk
           ext-equal-necc))

(defruled ext-equal-becomes-equiv
  (equal (ext-equal x y)
         (equiv x y))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (ext-equal x y)
              (equiv x y))
     :enable (equiv
              double-containment
              subset-when-ext-equal))))

(defruled equiv-becomes-ext-equal
  (equal (equiv x y)
         (ext-equal x y))
  :by ext-equal-becomes-equiv)

(defrule transitivity-of-ext-equal
  (implies (and (ext-equal x y)
                (ext-equal y z))
           (ext-equal x z))
  :enable ext-equal-becomes-equiv)

(defequiv ext-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled extensionality-no-backchain-limit
  (implies (and (setp x)
                (setp y))
           (equal (equal x y)
                  (let ((arbitrary-elem (ext-equal-witness x y)))
                    (equal (in arbitrary-elem x)
                           (in arbitrary-elem y)))))
  :enable (ext-equal
           equiv)
  :use ext-equal-becomes-equiv)

(defruled extensionality
  (implies (and (setp x)
                (setp y))
           (equal (equal x y)
                  (let ((arbitrary-elem (ext-equal-witness x y)))
                    (equal (in arbitrary-elem x)
                           (in arbitrary-elem y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
  :by extensionality-no-backchain-limit)
