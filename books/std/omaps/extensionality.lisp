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
    "This definition is equivalent to omap equality. There are not many rules
     about @('ext-equal'), because it is typically either rewritten to
     @('equal') or to its definition."))
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
     :use (:instance ext-equal-necc
                     (key (ext-equal-witness x1 y))
                     (x x0)))))

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
     :use (:instance ext-equal-necc
                     (key (ext-equal-witness x y1))
                     (y y0)))))

(defrule ext-equal-reflexive
  (ext-equal x x)
  :enable ext-equal)

(defruledl submap-when-ext-equal
  (implies (ext-equal x y)
           (submap x y))
  :enable (submap-to-submap-sk
           submap-sk)
  :use (:instance ext-equal-necc
                  (key (submap-witness x y))))

(defruledl submap-when-ext-equal-2
  (implies (ext-equal y x)
           (submap x y))
  :enable (submap-to-submap-sk
           submap-sk)
  :use (:instance ext-equal-necc
                  (key (submap-witness x y))
                  (x y)
                  (y x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ext-equal-becomes-equal
  (equal (ext-equal x y)
         (equal (mfix x) (mfix y)))
  :use (lemma0 lemma1)

  :prep-lemmas
  ((defruled lemma0
     (implies (ext-equal x y)
              (equal (mfix x) (mfix y)))
     :enable (double-containment
               submap-when-ext-equal
               submap-when-ext-equal-2))

   (defruled lemma1
     (implies (equal (mfix x) (mfix y))
              (ext-equal x y)))))

;;;;;;;;;;;;;;;;;;;;

(defruled equal-becomes-ext-equal-when-mapp
  (implies (and (mapp x)
                (mapp y))
           (equal (equal x y)
                  (ext-equal x y)))
  :enable ext-equal-becomes-equal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection extensionality
  :parents (omaps)
  :short "Prove omap equality by extensionality."
  :long
  (xdoc::topstring
   (xdoc::p
    "This rule rewrites an equality of omaps into an equality of
     @(tsee assoc) on an arbitrary element. The right-hand side is the
     expansion of @('(ext-equal x y'))."))

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
