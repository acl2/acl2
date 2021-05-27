; Elliptic Curve Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "jubjub")

(include-book "kestrel/crypto/ecurve/montgomery" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub-montgomery
  :parents (jubjub)
  :short "The Montgomery form of the Jubjub curve [ZPS:A.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "jubjub" "Jubjub curve")
    " @($\\mathbb{J}$) [ZPS:5.4.8.3] is a twisted Edwards curve.
     However, because of the "
    (xdoc::seetopic "ecurve::birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    ", there is also a Montgomery form of Jubjub
     @($\\mathbb{M}$) [ZPS:A.2].
     Here we define it, using our general mapping,
     and show some properties of it.
     This mapping uses a scaling factor,
     which ensures that the resulting Montgomery @($B$) is 1."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-montgomery-a ()
  :returns (a (fep a (jubjub-q))
              :hints (("Goal" :in-theory (enable fep jubjub-q))))
  :short "The Jubjub coefficient @($A_\\mathbb{M}$) [ZPS:A.2]."
  40962
  ///

  (defrule jubjub-montgomery-a-not-plus-two
    (not (equal (jubjub-montgomery-a) 2)))

  (defrule jubjub-montgomery-a-not-minus-two
    (not (equal (jubjub-montgomery-a) (neg 2 (jubjub-q))))
    :enable jubjub-q)

  (in-theory (disable (:e jubjub-montgomery-a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-montgomery-b ()
  :returns (b (fep b (jubjub-q))
              :hints (("Goal" :in-theory (enable fep jubjub-q))))
  :short "The Jubjub coefficient @($B_\\mathbb{M}$) [ZPS:A.2]."
  1
  ///

  (defrule jubjub-montgomery-b-not-zero
    (not (equal (jubjub-montgomery-b) 0)))

  (in-theory (disable (:e jubjub-montgomery-b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-montgomery-curve ()
  :returns (curve ecurve::montgomery-curvep)
  :short "The Jubjub curve in Montgomery form [ZPS:A.2]."
  (ecurve::make-montgomery-curve :a (jubjub-montgomery-a)
                                 :b (jubjub-montgomery-b)
                                 :p (jubjub-q))
  :guard-hints (("Goal"
                 :use jubjub-montgomery-a-not-minus-two
                 :in-theory (enable neg)))
  ///
  (in-theory (disable (:e jubjub-montgomery-curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule not-pfield-squarep-of-jubjub-montgomery-a-square-minus-4
  :short "Theorem related to the exceptional points in the birational mapping."
  :long
  (xdoc::topstring
   (xdoc::p
    "Theorem
     @(see ecurve::montgomery-only-point-with-y-0-when-aa-minus-4-non-square)
     limits certain exceptional points in the birational mapping
     under a certain condition on the Montgomery curve.
     Here we show that Jubjub, in Montgomery form,
     satisfies that condition, i.e. that @($A^2 - 4$) is not a square."))
  (b* ((a (ecurve::montgomery-curve->a (jubjub-montgomery-curve)))
       (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
    (not (ecurve::pfield-squarep a^2-4 (jubjub-q))))
  :enable (ecurve::weak-euler-criterion-contrapositive jubjub-q)
  :use (mod-expt-lemma not-zero-lemma)
  :disable ((:e expt))

  :prep-books ((include-book "kestrel/crypto/ecurve/prime-field-squares-euler-criterion" :dir :system))

  :prep-lemmas

  ((defruled mod-expt-fast-lemma
     (b* ((a (ecurve::montgomery-curve->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal (acl2::mod-expt-fast a^2-4
                                        (/ (1- (jubjub-q)) 2)
                                        (jubjub-q))
                   1)))
     :enable ((:e jubjub-montgomery-curve) jubjub-q)
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))

   (defruled mod-expt-lemma
     (b* ((a (ecurve::montgomery-curve->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal (mod (expt a^2-4
                              (/ (1- (jubjub-q)) 2))
                        (jubjub-q))
                   1)))
     :use (mod-expt-fast-lemma
           (:instance acl2::mod-expt-fast
            (a (sub (mul (ecurve::montgomery-curve->a (jubjub-montgomery-curve))
                         (ecurve::montgomery-curve->a (jubjub-montgomery-curve))
                         (jubjub-q))
                    4
                    (jubjub-q)))
            (i (/ (1- (jubjub-q)) 2))
            (n (jubjub-q))))
     :disable ((:e expt)))

   (defruled not-zero-lemma
     (b* ((a (ecurve::montgomery-curve->a (jubjub-montgomery-curve)))
          (a^2-4 (sub (mul a a (jubjub-q)) 4 (jubjub-q))))
       (not (equal a^2-4 0)))
     :enable ((:e jubjub-montgomery-curve) jubjub-q))))
