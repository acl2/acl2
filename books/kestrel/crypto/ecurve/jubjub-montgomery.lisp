; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "jubjub")
(include-book "birational-montgomery-twisted-edwards")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub-montgomery
  :parents (jubjub)
  :short "The Montgomery form of the Jubjub curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "jubjub" "Jubjub curve")
    "is a twisted Edwards curve.
     However, because of the "
    (xdoc::seetopic "birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    ", there is also a Montgomery form of Jubjub.
     Here we define it, using our general mapping,
     and show some properties of it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-montgomery-curve ()
  :returns (curve montgomery-p)
  :short "The Jubjub curve in Montgomery form."
  (twisted-edwards-to-montgomery (jubjub-curve))
  ///

  (defrule montgomery-primep-of-jubjub-montgomery-curve
    (montgomery-primep (jubjub-montgomery-curve))
    :enable montgomery-primep
    :disable ((:e montgomery-primep)))

  (in-theory (disable (:e jubjub-montgomery-curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule not-pfield-squarep-of-jubjub-montgomery-a-square-minus-4
  :short "Theorem related to the exceptional points in the birational mapping."
  :long
  (xdoc::topstring
   (xdoc::p
    "Theorem @(tsee montgomery-only-point-with-y-0-when-aa-minus-4-non-square),
     limits certain exceptional points in the birational mapping
     under a certain condition on the Montgomery curve.
     Here we show that Jubjub, in Montgomery form,
     satisfies that condition, i.e. that @($A^2 - 4$) is not a square."))
  (b* ((a (montgomery->a (jubjub-montgomery-curve)))
       (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
    (not (pfield-squarep a^2-4 (jubjub-q))))
  :enable (weak-euler-criterion-contrapositive)
  :use (mod-expt-lemma not-zero-lemma)
  :disable ((:e expt))

  :prep-books ((include-book "prime-field-squares-euler-criterion"))

  :prep-lemmas

  ((defruled mod-expt-fast-lemma
     (b* ((a (montgomery->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal (acl2::mod-expt-fast a^2-4
                                        (/ (1- (jubjub-q)) 2)
                                        (jubjub-q))
                   1)))
     :enable ((:e jubjub-montgomery-curve))
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))

   (defruled mod-expt-lemma
     (b* ((a (montgomery->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal (mod (expt a^2-4
                              (/ (1- (jubjub-q)) 2))
                        (jubjub-q))
                   1)))
     :use (mod-expt-fast-lemma
           (:instance acl2::mod-expt-fast
            (a (sub (mul (montgomery->a (jubjub-montgomery-curve))
                         (montgomery->a (jubjub-montgomery-curve))
                         (jubjub-q))
                    4
                    (jubjub-q)))
            (i (/ (1- (jubjub-q)) 2))
            (n (jubjub-q))))
     :disable ((:e expt)))

   (defruled not-zero-lemma
     (b* ((a (montgomery->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal a^2-4 0)))
     :enable ((:e jubjub-montgomery-curve)))))
