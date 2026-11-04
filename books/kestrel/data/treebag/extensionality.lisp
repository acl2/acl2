; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "bag-defs")
(include-book "count-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "bag"))
(local (include-book "count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc extensionality
  :parents (treebag)
  :short "Extensional equality of @(see treebag)s."
  :long
  (xdoc::topstring
    (xdoc::p
      "This definition is equivalent to @(see treebag) equality. It is often
       useful to prove equality by rewriting to this quantifier-based form.
       To do so, just enable the @('extensionality') rule.")
    (xdoc::p
      "A bag is determined by its multiplicities alone, with no side condition
       on which elements are present: an element absent from the bag and an
       element of multiplicity zero are the same thing, since @(tsee count)
       reads zero for an absent element and no element is bound to zero. This
       is the one place the representation invariant is visible from outside,
       and it is what lets a single quantifier do the work that @(see
       treemap::extensionality) needs two for.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A lookup in the underlying treemap, read through count. An element is bound
;; exactly when its count is positive, since no element is bound to zero.

(defruledl lookup-of-fix-becomes-count
  (equal (treemap::lookup k (fix bag) :default d)
         (if (posp (count k bag))
             (count k bag)
           d))
  :enable (count
           break-abstraction
           treemap::lookup-with-default-becomes-lookup-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk ext-equal (x y)
  :parents (extensionality)
  :returns (yes/no booleanp)
  (forall (elem)
    (non-exec
      (equal (count elem x)
             (count elem y)))))

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

(defrule transitivity-of-ext-equal
  (implies (and (ext-equal x y)
                (ext-equal y z))
           (ext-equal x z))
  :expand (ext-equal x z)
  :enable ext-equal-necc)

(defequiv ext-equal)

(defrulel count-when-ext-equal-congruence
  (implies (ext-equal x y)
           (equal (count elem x)
                  (count elem y)))
  :rule-classes :congruence
  :by ext-equal-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel ext-equal-refines-equiv
  (implies (ext-equal x y)
           (equiv x y))
  :rule-classes :refinement
  :enable (equiv
           break-abstraction
           treemap::extensionality
           lookup-of-fix-becomes-count))

(defruled ext-equal-becomes-equiv
  (equal (ext-equal x y)
         (equiv x y))
  :cases ((ext-equal x y)))

(defruled equiv-becomes-ext-equal
  (equal (equiv x y)
         (ext-equal x y))
  :by ext-equal-becomes-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled extensionality-no-backchain-limit
  (implies (and (bagp x)
                (bagp y))
           (equal (equal x y)
                  (equal (count (ext-equal-witness x y) x)
                         (count (ext-equal-witness x y) y))))
  :enable (ext-equal
           equiv)
  :use ext-equal-becomes-equiv)

(defruled extensionality-no-backchain-limit-polar
  (implies (and (syntaxp (acl2::want-to-weaken (equal x y)))
                (bagp x)
                (bagp y))
           (equal (equal x y)
                  (equal (count (ext-equal-witness x y) x)
                         (count (ext-equal-witness x y) y))))
  :by extensionality-no-backchain-limit)

(defruled extensionality
  (implies (and (bagp x)
                (bagp y))
           (equal (equal x y)
                  (equal (count (ext-equal-witness x y) x)
                         (count (ext-equal-witness x y) y))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
  :by extensionality-no-backchain-limit)

(defruled extensionality-polar
  (implies (and (syntaxp (acl2::want-to-weaken (equal x y)))
                (bagp x)
                (bagp y))
           (equal (equal x y)
                  (equal (count (ext-equal-witness x y) x)
                         (count (ext-equal-witness x y) y))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 1)))
  :by extensionality-no-backchain-limit)
