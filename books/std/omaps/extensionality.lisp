; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "core")
(include-book "with-fixing-theorems")
(include-book "assoc")
(include-book "submap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk ext-equal ((x mapp) (y mapp))
  :parents (omaps)
  :short "Extensional equality of @(see omaps)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This definition is equivalent to omap equality."))
  (forall (key)
          (equal (assoc key x)
                 (assoc key y)))
  :skolem-name ext-equal-witness)

;;;;;;;;;;;;;;;;;;;;

(defrule ext-equal-when-mequiv-of-arg1-congruence
  (implies (mequiv x0 x1)
           (equal (ext-equal x0 y)
                  (ext-equal x1 y)))
  :rule-classes :congruence
  :use (lemma
        (:instance lemma
                   (x0 x1)
                   (x1 x0)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (mequiv x0 x1)
                   (ext-equal x0 y))
              (ext-equal x1 y))
     :expand (ext-equal x1 y)
     :enable ext-equal-necc)))

(defrule ext-equal-when-mequiv-of-arg2-congruence
  (implies (mequiv y0 y1)
           (equal (ext-equal x y0)
                  (ext-equal x y1)))
  :rule-classes :congruence
  :use (lemma
        (:instance lemma
                   (y0 y1)
                   (y1 y0)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (mequiv y0 y1)
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

(defruledl submap-when-ext-equal
  (implies (ext-equal x y)
           (submap x y))
  :enable (submap-to-submap-sk
           submap-sk
           ext-equal-necc))

(defruled ext-equal-becomes-equal
  (equal (ext-equal x y)
         (equal (mfix x) (mfix y)))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (ext-equal x y)
              (equal (mfix x) (mfix y)))
     :enable (double-containment
              submap-when-ext-equal))))

(defruled equal-becomes-ext-equal-when-mapp
  (implies (and (mapp x)
                (mapp y))
           (equal (equal x y)
                  (ext-equal x y)))
  :enable ext-equal-becomes-equal)

(defrule transitivity-of-ext-equal
  (implies (and (ext-equal x y)
                (ext-equal y z))
           (ext-equal x z))
  :enable ext-equal-becomes-equal)

(defequiv ext-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection extensionality
  :parents (omaps)
  :short "Prove omap equality by extensionality."
  :long
  (xdoc::topstring
   (xdoc::p
    "This rule rewrites an equality of omaps into an equality of
     @(tsee assoc) on an arbitrary element. The right-hand side is the
     expansion of @('(ext-equal x y)')."))

  (defruled extensionality
    (implies (and (mapp x)
                  (mapp y))
             (equal (equal x y)
                    (let ((arbitrary-key (ext-equal-witness x y)))
                      (equal (assoc arbitrary-key x)
                             (assoc arbitrary-key y)))))
    :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
    :enable ext-equal
    :use equal-becomes-ext-equal-when-mapp))
