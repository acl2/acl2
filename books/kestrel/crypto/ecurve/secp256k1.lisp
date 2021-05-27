; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "secp256k1-domain-parameters")
(include-book "std/testing/assert-bang" :dir :system)
(include-book "short-weierstrass")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Formal spec for secp256k1 elliptic curve functions
;; ==================================================

;; This file specifies addition, multiplication, and negation in secp256k1.


;; Introduction
;; ------------

;; The basic Weierstrass form of an elliptic curve is
;;   y^2 = x^3 + ax + b
;; (although there are other forms as well)
;;
;; secp256k1 is the elliptic curve
;;   y^2 (mod p) = x^3 + 7 (mod p)
;; where x and y are integers in the field Z_p (i.e., in [0, p-1]).
;; p, the size of the field, is:
;;   2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
;; p is defined in the file
;; [books]/kestrel/crypto/primes/secp256k1-field-prime.lisp,
;; as the nullary function secp256k1-field-prime.
;;
;; secp256k1 also defines a group defined on points on the curve
;; (which include an infinity point).
;; The group starts with a generator point G on the curve
;; and the group operator we call "+", such that
;; if g1 and g2 are in the group, g1+g2 is also in the group.
;; Scalar multiplication can be defined in terms of repeated addition.
;; So P = sG means the point P is the result of adding s copies of G.
;; See the references for the exact definition of the group "+".


;; References
;; ----------
;;
;; For more information see:
;;
;;   Standards for Efficient Cryptography
;;   SEC 1: Elliptic Curve Cryptography (Version 2.0)
;;   Certicom Research, May 2009
;;   http://www.secg.org/sec1-v2.pdf
;;
;; secp256k1 constants:
;;   Standards for Efficient Cryptography
;;   SEC 2: Recommended Elliptic Curve Domain Parameters (Version 2.0)
;;   Certicom Research, January 2010
;;   http://www.secg.org/sec2-v2.pdf

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Technical details
-----------------

As excerpted from Standards:

The elliptic curve domain parameters over Fp associated with a Koblitz curve
secp256k1 are specified by the sextuple T = (p,a,b,G,n,h) where the finite
field Fp is defined by:

p = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F
  = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1

The curve E: y^2 = x^3+ax+b over Fp is defined by:

a = 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000
b = 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000007

The base point G in compressed form is:

G = 02 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798
[Note: the "compressed form" takes G's x component and prefixes either:
 "02", if the y value is even; or
 "03", if the y value is odd.]

and in uncompressed form is:

G = 04 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798
       483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8

[Note: the uncompressed form concatenates "04", the base point x value,
 and the base point y value.]

Finally the order n of G and the cofactor are:

n = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141
h = 01
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Elliptic curve parameters

;; We name the above constants as follows in ACL2:
;; p -> (secp256k1-field-prime)
;; a -> (secp256k1-a)
;; b -> (secp256k1-b)
;; n -> (secp256k1-group-prime)
;; h -> (secp256k1-cofactor)
;; G -> (secp256k1-generator)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The prime p is defined in secp256k1-domain-parameters.lisp.

;; Just as an extra validation,
;; we copied this number to wolframalpha.com and asked "Is 0xFFF...C2F prime?"
;; It replied that it is a prime number.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The coefficients a and b are defined in secp256k1-domain-parameters.lisp.

;; Since a=0 and b=7,
;; the curve E is:
;;
;;    y^2 = x^3 + 7

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top xdoc topic for this file.

(defxdoc secp256k1
  :parents (elliptic-curves)
  :short "A library for the Short Weierstrass elliptic curve secp256k1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library contains executable formal specifications of elliptic curve operations
     on secp256k1, defined "
    (xdoc::ahref "http://www.secg.org/sec2-v2.pdf#page=13" "here")
    ", which is a "
    (xdoc::seetopic "short-weierstrass-curves" "short Weierstrass")
    " elliptic curve with @('a=0') and @('b=7'):")
   (xdoc::@[] "y^2=x^3+7")
   (xdoc::p "secp256k1 is used for Bitcoin and Ethereum.")
   (xdoc::p "For more information on secp256k1, see @(see secp256k1-domain-parameters).")
   (xdoc::p "See also the source code for more extensive
             discussion, references, and proved theorems.")
   ))

;; Order the subtopics according to the order in which they were defined.
(xdoc::order-subtopics secp256k1
  nil
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The generator point for the curve (an ordered pair).

(defsection secp256k1-generator
  :parents (secp256k1)
  :short "The generator point @('G')."
  :long "The nullary function call @(call secp256k1-generator)
         returns the standard generator point for the curve secp256k1."
  (defund secp256k1-generator ()
    (declare (xargs :guard t))
    (cons
     (secp256k1-generator-x)
     (secp256k1-generator-y))))

(in-theory (disable (:e secp256k1-generator)))

(defthm pointp-of-secp256k1-generator
  (pointp (secp256k1-generator))
  :hints (("Goal" :in-theory (enable secp256k1-generator
                                     secp256k1-generator-x
                                     secp256k1-generator-y))))

(defthm point-in-pxp-p-of-secp256k1-generator
  (point-in-pxp-p (secp256k1-generator) (secp256k1-field-prime))
  :hints (("Goal" :in-theory (enable point-in-pxp-p
                                     secp256k1-generator
                                     secp256k1-generator-x
                                     secp256k1-generator-y))))

(encapsulate ()

  ;; It's easy to calculate that point-on-weierstrass-elliptic-curve-p holds on
  ;; the generator, except that the rtl::primep guard of this function takes
  ;; too long to compute if the definition of secp256k1-field-prime is enabled.  So
  ;; we separate out the calculation of the body of
  ;; point-on-weierstrass-elliptic-curve-p in the lemma below (where we enable
  ;; secp256k1-field-prime), which we use to prove the main theorem (without enabling
  ;; the definition of secp256k1-field-prime).

  (local
   (defthm lemma
     (let* ((p (secp256k1-field-prime))
            (a (secp256k1-a))
            (b (secp256k1-b))
            (point (secp256k1-generator)))
       ;; body of point-on-weierstrass-elliptic-curve-p:
       (or (eq point :infinity)
           (let ((x (car point))
                 (y (cdr point)))
             (let ((y^2 (pfield::mul y y p))
                   (x^3 (pfield::mul x (pfield::mul x x p) p)))
               (let ((x^3+ax+b (pfield::add x^3
                                            (pfield::add (pfield::mul a x p)
                                                         b
                                                         p)
                                            p)))
                 (equal y^2 x^3+ax+b))))))
     :rule-classes nil
     :hints (("Goal" :in-theory (enable secp256k1-field-prime
                                        secp256k1-generator
                                        secp256k1-generator-x
                                        secp256k1-generator-y
                                        secp256k1-a
                                        secp256k1-b)))))

  (defthm point-on-weierstrass-elliptic-curve-p-of-secp256k1-generator
    (point-on-weierstrass-elliptic-curve-p (secp256k1-generator)
                                           (secp256k1-field-prime)
                                           (secp256k1-a)
                                           (secp256k1-b))
    :hints (("Goal"
             :in-theory (enable point-on-weierstrass-elliptic-curve-p)
             :use lemma))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The order n of the group is defined in secp256k1-domain-parameters.lisp.

;; Two spec validation checks:

;; 1. How can we be sure n is the order of E starting at G?
;; There is an algorithm called Schoof-Elkies-Atkin that can count
;; points on an elliptic curve over a finite field reasonably efficiently.
;; One implementation is in Sage, which can be used at:
;;   https://sagecell.sagemath.org/
;; Type this Sage code:
;;   P = 2^256 - 2^32 - 977
;;   E = EllipticCurve(GF(P),[0,0,0,0,7])
;;   E.cardinality()
;; Clicking the Evaluate button will yield (secp256k1-group-prime):
;;   115792089237316195423570985008687907852837564279074904382605163141518161494337
;; Note, the parameters [0,0,0,0,7] refer to the coefficients
;; [a1,a2,a3,a4,a6] in the Weierstrass equation:
;; y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6

;; 2. Is (secp256k1-group-prime) really prime?
;; It doesn't matter here, but it does in deterministic-ecdsa.lisp
;; To check, we copied this number to wolframalpha.com
;; and asked "Is 0xFFF...141 prime?"
;; It replied that it is a prime number.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The cofactor h is defined in secp256k1-domain-parameters.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make sure secp256k1 has valid parameters for p, a, and b

;; Note, executing (primep ..) is slow.  You have to do it in a proof context.
;; That is why this is not an assert.
(defthm secp256k1-params-define-valid-elliptic-curve
  (weierstrass-elliptic-curve-p (secp256k1-field-prime) (secp256k1-a) (secp256k1-b))
  :hints (("Goal":in-theory (enable weierstrass-elliptic-curve-p
                                    secp256k1-b
                                    fep))))
; Note: enabling secp256k1-a makes the proof hang.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Square root in the prime field

;; Euler's Criterion
;; lets us know that "a" has a square root mod p if
;; a^((p-1)/2) = 1 mod p.
;; See acl2/books/projects/quadratic-reciprocity/support/euler.lisp
;; for a proof of Euler's Criterion.
;;
;; Note, many references define "a is a quadratic residue of p"
;; or "a is a residue of p" or just "a R p"
;; to mean "a has a square root mod p".

(defsection secp256k1-has-square-root?
  :parents (secp256k1)
  :short "Test if @('a') has a square root in secp256k1's prime field @('p')."
  :long "@(call secp256k1-has-square-root?) tests whether @('a') is
         a quadratic residue of @('p'), i.e., whether there exists
         an element @($x$) of the prime field such that @($x^2 = a\\ (mod\\ p)$).
         <p/>
         Note that this function is about the prime field @('p') used
         to define secp256k1.  It is independent of
         the other secp256k1 domain parameters."
  (defun secp256k1-has-square-root? (a)
    (declare (xargs :guard (and (natp a) (< a (secp256k1-field-prime)))
                    :guard-hints (("Goal" :in-theory (enable secp256k1-field-prime fep)))))
    (let ((p (secp256k1-field-prime)))
      (equal (pow a (/ (- p 1) 2) p)
             1)))
  )

;; There is a reasonably simple formula for finding mod-sqrt(a)
;; when p = 3 (mod 4), which is the case here.
(assert! (equal (mod (secp256k1-field-prime) 4) 3))

;; See:
;; * E. Bach and J. Shallit, "Algorithmic number theory," Efficient
;;   Algorithms. Cambridge, MA: MIT Press, 1996, vol. I, p. 155.
;; *  J. L. Lagrange, "Sur la solution des problemes indetermines du second
;;    degre," Histoire Acad. Roy. Sci. Belle-Lett., Berlin, Germany, 1769,
;;    pp. 165-310 (reprint Oeuvres, vol. 2, pp. 377-535).

;; For this case, because p = 3 mod 4, the square root formula is (references above):
;;   a^((p+1)/4) (mod p)
;; However, this will get the wrong answer if there is no square root.
;; We could call SECP256K1-HAS-SQUARE-ROOT? defined above, but
;; if we already have a possible square root, it is easier
;; to just square it to check.

(defsection secp256k1-sqrt
  :parents (secp256k1)
  :short "Compute the modular square root of @('a') in the field @('p')."
  :long "@(call secp256k1-sqrt) finds an @($x$) such that
         @($x^2 = a\\ (mod\\ p)$), if such exists, where @($p$) is the prime
         field used for secp256k1.  If there is no square root, the symbol
         @(':invalid') is returned.
         <p/>
         Note that this function is about the prime field @('p') used
         to define secp256k1.  It is independent of
         the other secp256k1 domain parameters."

  (defun secp256k1-sqrt (a)
    (declare (xargs :guard (and (natp a) (< a (secp256k1-field-prime)))
                    :guard-hints (("Goal"
                                   :in-theory (enable secp256k1-field-prime fep)))))
    (let ((p (secp256k1-field-prime)))
      (let ((poss-root (pow a (/ (+ p 1) 4) p)))
        (if (equal (mod (* poss-root poss-root) p) a)
            poss-root
          ':invalid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Addition in secp256k1.

(defsection secp256k1+
  :parents (secp256k1)
  :short "Add two elliptic curve points."
  :long "@(call secp256k1+) adds
         @('point1') and @('point2') using the elliptic curve group operation.
         The two input points must be on the secp256k1 elliptic curve.
         If either is not, a guard violation occurs.
         <p/>
         The result is a point on the elliptic curve."
  (defund secp256k1+ (point1 point2)
    (declare
     (xargs :guard (and (pointp point1) (pointp point2)
                        (point-in-pxp-p point1 (secp256k1-field-prime))
                        (point-in-pxp-p point2 (secp256k1-field-prime))
                        (point-on-weierstrass-elliptic-curve-p point1
                                                               (secp256k1-field-prime)
                                                               (secp256k1-a)
                                                               (secp256k1-b))
                        (point-on-weierstrass-elliptic-curve-p point2
                                                               (secp256k1-field-prime)
                                                               (secp256k1-a)
                                                               (secp256k1-b)))
            :guard-hints (("Goal"
                           :in-theory (enable secp256k1-field-prime
                                              secp256k1-a
                                              secp256k1-b)))
            :normalize nil)) ; to prevent SECP256K1-A from becoming 0
    (curve-group-+ point1 point2 (secp256k1-field-prime) (secp256k1-a)
  (secp256k1-b)))
)

(defthm pointp-of-secp256k1+
  (implies (and (pointp point1)
                (pointp point2))
           (pointp (secp256k1+ point1 point2)))
  :hints (("Goal" :in-theory (enable secp256k1+ secp256k1-a secp256k1-b fep))))

(defthm point-in-pxp-p-of-secp256k1+
  (implies (and (pointp point1)
                (pointp point2)
                (point-in-pxp-p point1 (secp256k1-field-prime))
                (point-in-pxp-p point2 (secp256k1-field-prime)))
           (point-in-pxp-p (secp256k1+ point1 point2) (secp256k1-field-prime)))
  :hints (("Goal" :in-theory (enable secp256k1+))))

(defthm point-on-weierstrass-elliptic-curve-p-of-secp256k1+
  (implies (and (pointp point1)
                (pointp point2)
                (point-in-pxp-p point1 (secp256k1-field-prime))
                (point-in-pxp-p point2 (secp256k1-field-prime))
                (point-on-weierstrass-elliptic-curve-p point1
                                                       (secp256k1-field-prime)
                                                       (secp256k1-a)
                                                       (secp256k1-b))
                (point-on-weierstrass-elliptic-curve-p point2
                                                       (secp256k1-field-prime)
                                                       (secp256k1-a)
                                                       (secp256k1-b)))
           (point-on-weierstrass-elliptic-curve-p (secp256k1+ point1 point2)
                                                  (secp256k1-field-prime)
                                                  (secp256k1-a)
                                                  (secp256k1-b)))
  :hints (("Goal" :in-theory (enable secp256k1+ secp256k1-a secp256k1-b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Multiplication in secp256k1.

;; This is O(log(s)) since for even S it splits in half and recurses.
(defsection secp256k1*
  :parents (secp256k1)
  :short "Multiply an elliptic curve point by a scalar."
  :long "@(call secp256k1*) applies the elliptic group operation to @('s')
         copies of @('point').
         <p/>
         Since we use @('+') to describe the group operation, this
         operation can be thought of as multiplying @('point') by the scalar @('s').
         <p/>
         (Alternatively, for those who think of the group operation as
         multiplication, this operation can be thought of as exponentiation.)
         <p/>
         @('point') must be on the secp256k1 elliptic curve.  If it is not,
         a guard violation occurs.
         <p/>
         The result is a point on the elliptic curve."
  (defund secp256k1* (s point)
    (declare
     (xargs :guard (and (natp s)
                        (pointp point)
                        (point-in-pxp-p point (secp256k1-field-prime))
                        (point-on-weierstrass-elliptic-curve-p point
                                                               (secp256k1-field-prime)
                                                               (secp256k1-a)
                                                               (secp256k1-b)))
            :guard-hints (("Goal"
                           :in-theory (e/d (secp256k1-field-prime
                                            secp256k1-a
                                            secp256k1-b)
                                           (curve-scalar-*))))
            :normalize nil)) ; to prevent SECP256K1-A from becoming 0
    (curve-scalar-* s point (secp256k1-field-prime) (secp256k1-a) (secp256k1-b))))

(defthm pointp-of-secp256k1*
  (implies (pointp point)
           (pointp (secp256k1* s point)))
  :hints (("Goal" :in-theory (enable secp256k1* secp256k1-a secp256k1-b fep))))

(defthm point-in-pxp-p-of-secp256k1*
  (implies (and (natp s)
                (pointp point)
                (point-in-pxp-p point (secp256k1-field-prime)))
           (point-in-pxp-p (secp256k1* s point) (secp256k1-field-prime)))
  :hints (("Goal" :in-theory (enable secp256k1*))))

(defthm point-on-weierstrass-elliptic-curve-p-of-secp256k1*
  (implies (and (natp s)
                (pointp point)
                (point-in-pxp-p point (secp256k1-field-prime))
                (point-on-weierstrass-elliptic-curve-p point
                                                       (secp256k1-field-prime)
                                                       (secp256k1-a)
                                                       (secp256k1-b)))
           (point-on-weierstrass-elliptic-curve-p (secp256k1* s point)
                                                  (secp256k1-field-prime)
                                                  (secp256k1-a)
                                                  (secp256k1-b)))
  :hints (("Goal" :in-theory (enable secp256k1* secp256k1-a secp256k1-b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Negation in secp256k1.

(defsection secp256k1-negate
  :parents (secp256k1)
  :short "Negate an elliptic curve point."
  :long "@(call secp256k1-negate) finds the inverse of @('point') with
         respect to the secp256k1 elliptic curve group operation.
         <p/>
         The result is a point on the elliptic curve."
  (defund secp256k1-negate (point)
    (declare (xargs :guard (and (pointp point)
                                (point-in-pxp-p point (secp256k1-field-prime)))
                    :guard-hints (("Goal" :in-theory (enable fep)))))
    (curve-negate point (secp256k1-field-prime)))
  )

(defthm pointp-of-secp256k1-negate
  (implies (pointp point)
           (pointp (secp256k1-negate point)))
  :hints (("Goal" :in-theory (enable secp256k1-negate))))

(defthm point-in-pxp-p-of-secp256k1-negate
  (implies (and (pointp point)
                (point-in-pxp-p point (secp256k1-field-prime)))
           (point-in-pxp-p (secp256k1-negate point) (secp256k1-field-prime)))
  :hints (("Goal" :in-theory (enable secp256k1-negate))))
