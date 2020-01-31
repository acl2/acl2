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

(include-book "primes")
(include-book "points")
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "short-weierstrass-closure-simp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Elliptic Curves over Prime Fields in Short Weierstrass Form
; -----------------------------------------------------------
;
; This book specifies
; elliptic curves over prime fields in short Weierstrass form
; with a non-zero constant coefficient.
; The short Weierstrass form is y^2 = x^3 + ax + b,
; with a, b, x, y in Fp and p > 3, where Fp is a prime field,
; and where + and ^ (which is just iterated *) are field operations,
; i.e. regular arithmetic operations mod p.

; When p = 2 or p = 3, the elliptic curve equation has different forms.
; We may generalize this library at some point to cover those forms,
; and possibly also to cover non-prime finite fields.

; When the constant coefficient b is not 0,
; the point (0, 0) does not satisfy the equation,
; and can be therefore used to represent the point at infinity, as we do here.
; We may generalize this library to allow b to be 0,
; changing the representation of points accordingly.
; Also see the file points.lisp.

; See Neal Koblitz's book "A Course in Number Theory and Cryptography" (2nd Ed.)
; for background on elliptic curves.

; Our specification follows the SEC 1 standard,
; available at http://www.secg.org/sec1-v2.pdf,
; as well as the Johnson, Menezes, and Vanstone's
; "The Elliptic Curve Digital Signature Algorithm (ECDSA)",
; International Journal of Information Security,
; August 2001, Volume 1, Issue 1, pages 33-63.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top xdoc topic for this file.

(defxdoc short-weierstrass
  :parents (ecurve::elliptic-curves)
  :short "A library for Short Weierstrass elliptic curves."
  :long
  (xdoc::topstring
   (xdoc::p
    "This libray contains executable formal specifications of elliptic curve operations
     on Short Weierstrass curves, which have the form")
   (xdoc::@[] "y^2=x^3+ax+b")
   (xdoc::p "where @('x') and @('y') are integers in @('\{0,..,p-1\}')
             for an appropriate prime number @('p').")
   (xdoc::p "For details see "
            (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
                     "Standards for Efficient Cryptography 1 (SEC 1)")
            ".")
   (xdoc::p "The arguments @('a') and @('b') to the functions below
             always refer to the coefficients in the equation above.")
   (xdoc::p "The argument @('p') always refers to the prime number
             that is the field order.")
   (xdoc::p "See the source code for more extensive
             discussion, references, and proved theorems.")
   ))

;; Order the subtopics according to the order in which they were defined.
(xdoc::order-subtopics short-weierstrass
  nil
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Valid elliptic curve.
;; sec1-v2 section 2.2.1
;; field size must be an odd prime greater than 3,
;; and a and b must be in the field and satisfy 4a^3 + 27b^2 /= 0
;; (sec1-v2 does not mention the condition p > 3,
;; presumably because the recommended curves all satisfy that anyhow)

(defsection weierstrass-elliptic-curve-p
  :parents (short-weierstrass)
  :short "Test if curve parameters are valid."
  :long "@(call weierstrass-elliptic-curve-p) tests whether
         the Short Weierstrass curve defined by
         @('p'), @('a'), and @('b') is a valid elliptic curve."
  (defund weierstrass-elliptic-curve-p (p a b)
    (and (rtl::primep p)
         (< 3 p)
         (fep a p)
         (fep b p)
         (posp (mod (+ (* 4 a a a) (* 27 b b)) p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A point on the curve is (x,y) where y^2 = x^3 + ax + b (mod p).
;; x and y are nats less than p, i.e. they are field elements.
;; The special infinity point is represented as (0,0).

;; Tests if a point is on an elliptic curve of the form explained above.

(defsection point-on-elliptic-curve-p
  :parents (short-weierstrass)
  :short "Test if a point is on an elliptic curve."
  :long "@(call point-on-elliptic-curve-p) tests whether
          @('point') is on the Short Weierstrass elliptic curve
          defined by @('p'), @('a'), and @('b').
         <p/>
         @('point') is an ordered pair (a cons) of two integers
         in @('\{0,..,p-1\}').  The infinity point is represented
         by the cons pair @('(0 . 0)').  We require @('b') to be nonzero."
  (defund point-on-elliptic-curve-p (point p a b)
    (declare (xargs :guard (and (rtl::primep p)
                                (< 3 p)
                                (fep a p)
                                (fep b p)
                                (not (= b 0))
                                (pointp point)
                                (point-in-pxp-p point p))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (enable fep pointp point-in-pxp-p)))))
    (let ((x (car point))
          (y (cdr point)))
      ;; We represent the infinity point as (0,0).  This is safe as long as b
      ;; is nonzero: if b is nonzero, then (0,0) cannot be a solution to
      ;; y^2 = x^3 + ax + b.
      (or (and (= x 0) (= y 0))
          (let ((y^2 (mul y y p))
                (x^3 (mul x (mul x x p) p)))
            (let ((x^3+ax+b (add x^3
                                 (add (mul a x p)
                                      b
                                      p)
                                 p)))
              (equal y^2 x^3+ax+b))))))
)

;; The infinity point is on the curve.

(defthm point-on-elliptic-curve-p-of-inf
  (implies (< 0 p)
           (point-on-elliptic-curve-p '(0 . 0) p a b))
  :hints (("Goal" :in-theory (enable point-on-elliptic-curve-p))))

;; Since the y^2 is symmetric over the x axis,
;; if the point (x1,y1) is on the curve,
;; then the point (x1, -y1) = (x1, p-y1) is also on the curve.
;; In this case if y1 = 0, they are the same point.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Addition in the elliptic curve group.

;; See http://www.secg.org/sec1-v2.pdf,
;; Section 2.2.1, "Elliptic Curves over Fp".
;; And in the aforementioned ECDSA paper,
;; section 4.1 defines addition and doubling of points on the curve.

;; Adds two points on an elliptic curve (in F_p).
;; point1 and point2 are points on the curve.
;; a and b are from the curve equation:
;;   y^2 = x^3 + ax + b
;; * Also requiring that b be nonzero
;;   so we do not support the form y^2 = x^3 + ax.
;;   This is so we can represent the infinity point as (0,0).
;; In this definition, slope is lambda in SEC 1.

(defsection curve-group-+
  :parents (short-weierstrass)
  :short "Add two elliptic curve points."
  :long "@(call curve-group-+) adds
         @('point1') and @('point2') using the elliptic curve group operation.
         The two input points must be on the Short Weierstrass elliptic curve
         defined by @('p'), @('a'), and @('b').  If either is not, a guard
         violation occurs.
         <p/>
         The result is a point on the elliptic curve."
  (defund curve-group-+ (point1 point2 p a b)
    (declare (xargs :guard (and (rtl::primep p)
                                (< 3 p)
                                (fep a p)
                                (fep b p)
                                (not (= b 0))
                                (pointp point1)
                                (pointp point2)
                                (point-in-pxp-p point1 p)
                                (point-in-pxp-p point2 p)
                                (point-on-elliptic-curve-p point1 p a b)
                                (point-on-elliptic-curve-p point2 p a b))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (enable fep
                                           pointp
                                           point-in-pxp-p
                                           point-on-elliptic-curve-p)))))
    (declare (ignore b))
    (if (equal point1 '(0 . 0))
        point2 ; handles rule 1 (0+0=0) and half of rule 2 (0+Q=Q)
      (if (equal point2 '(0 . 0))
          point1 ; handles the other half of rule 2 (P+0=P)
        (let ((x1 (car point1))
              (y1 (cdr point1))
              (x2 (car point2))
              (y2 (cdr point2)))
          (if (= x1 x2)
              (if (= (add y1 y2 p) 0)
                  '(0 . 0) ; rule 3, y1 = -y2 (mod p)
                ;; rule 5, doubling the point
                (let* ((slope (div (add (mul 3
                                             (mul x1 x1 p)
                                             p)
                                        a
                                        p)
                                   (mul 2 y1 p)
                                   p))
                       (x3 (sub (mul slope slope p)
                                (mul 2 x1 p)
                                p))
                       (y3 (sub (mul slope
                                     (sub x1 x3 p)
                                     p)
                                y1
                                p)))
                  (cons x3 y3)))
            ;; rule 4, adding two points that are not any of the
            ;; other special cases
            (let* ((slope (div (sub y2 y1 p)
                               (sub x2 x1 p)
                               p))
                   (x3 (sub (sub (mul slope slope p)
                                 x1
                                 p)
                            x2
                            p))
                   (y3 (sub (mul slope
                                 (sub x1 x3 p)
                                 p)
                            y1
                            p)))
              (cons x3 y3)))))))
)

;; The file short-weierstrass-validation.lisp contains theorems
;; that more explicitly link this definition to rules 1-5 in SEC 1.

(defthm pointp-of-curve-group-+
  (implies (and (posp p)
                (natp a)
                (natp b)
                (pointp point1)
                (pointp point2))
           (pointp (curve-group-+ point1 point2 p a b)))
  :hints (("Goal" :in-theory (enable curve-group-+ pointp))))

(defthm consp-of-curve-group-+
  (implies (and (consp point1)
                (consp point2))
           (consp (curve-group-+ point1 point2 p a b)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable curve-group-+ pointp))))

(encapsulate
  ()
  (local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

  (defthm point-in-pxp-p-of-curve-group-+
    (implies (and (posp p)
                  (natp a)
                  (natp b)
                  (pointp point1)
                  (pointp point2)
                  (point-in-pxp-p point1 p)
                  (point-in-pxp-p point2 p))
             (point-in-pxp-p (curve-group-+ point1 point2 p a b) p))
    :hints (("Goal" :in-theory (enable curve-group-+ point-in-pxp-p pointp)))))

(defthm curve-group-+-left-identity
  (equal (curve-group-+ '(0 . 0) point p a b)
         point)
  :hints (("Goal" :in-theory (enable curve-group-+))))

(defthm curve-group-+-right-identity
  (equal (curve-group-+ point '(0 . 0) p a b)
         point)
  :hints (("Goal" :in-theory (enable curve-group-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Proof of closure of curve-group-+.

;; The fact that curve-group-+ returns a point on the curve,
;; i.e. that the group is closed under addition,
;; takes a bit of work, which is done in the supporting files
;; short-weierstrass-closure-lemma.lisp and short-weierstrass-closure-simp.lisp
;; included here.
;; Here we take the closure theorem from those files,
;; which is expressed in terms of "simplified" versions of
;; point-on-elliptic-curve-p and cure-group-+,
;; and "transfer" it to the versions of these two functions
;; as defined here in this file.

(encapsulate ()

  (local (include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system))
  (local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

  (local
   (defthmd point-on-elliptic-curve-p-equivalence
     (implies (and (integerp a)
                   (integerp b)
                   (pointp pt))
              (iff (point-on-elliptic-curve-p pt (prime) a b)
                   (simp-point-on-elliptic-curve-p pt a b)))
     :hints (("Goal" :in-theory (e/d (P[X.Y]
                                      simp-point-on-elliptic-curve-p
                                      pointp
                                      point-on-elliptic-curve-p
                                      =p
                                      modp
                                      i*
                                      i+
                                      i-)
                                     (mod-of-*-becomes-mul
                                      acl2::mod-sum-cases))))))

  (local
   (defthmd curve-group-+-equivalence
     (implies (and (integerp a)
                   (integerp b)
                   (pointp point1)
                   (pointp point2)
                   (point-in-pxp-p point1 (prime))
                   (point-in-pxp-p point2 (prime))
                   (point-on-elliptic-curve-p point1 (prime) a b)
                   (point-on-elliptic-curve-p point2 (prime) a b))
              (equal (curve-group-+ point1 point2 (prime) a b)
                     (simp-curve-group-+ point1 point2 a b)))
     :hints (("Goal"
              :in-theory (e/d (simp-curve-group-+
                               curve-group-+
                               pointp-and-point-in-pxp-p-of-simp-curve-group-+
                               pointp
                               point-in-pxp-p
                               x3 y3 alpha{x1=/=x2} alpha{x1=x2}
                               delta-x
                               *-2-X
                               div
                               =p
                               modp
                               i+
                               i-
                               i*
                               sub) ; goes to add of neg
                              (acl2::mod-sum-cases ; avoids case splits
                               acl2::mod-of-minus-arg1))))))

  ;; We first prove the following two theorems "abstractly", that is dependent
  ;; on the constrained 0-ary function PRIME. We prove the same theorem for
  ;; arbitrary integers p after these.

  (local
   (defthmd pointp-and-pointp-in-pxp-of-curve-group-+-abstract
     (implies (and (integerp a)
                   (integerp b)
                   (pointp point1)
                   (pointp point2)
                   (point-in-pxp-p point1 (prime))
                   (point-in-pxp-p point2 (prime))
                   (point-on-elliptic-curve-p point1 (prime) a b)
                   (point-on-elliptic-curve-p point2 (prime) a b))
              (and (pointp (curve-group-+ point1 point2 (prime) a b))
                   (point-in-pxp-p (curve-group-+ point1 point2 (prime) a b)
                                   (prime))))
     :hints (("Goal"
              :in-theory (e/d (curve-group-+-equivalence
                               pointp-and-point-in-pxp-p-of-simp-curve-group-+)
                              (curve-group-+
                               pointp
                               point-in-pxp-p
                               point-on-elliptic-curve-p))))))

  (local
   (defthmd point-on-elliptic-curve-p-of-curve-group-+-abstract
     (implies (and (integerp a)
                   (integerp b)
                   (pointp point1)
                   (pointp point2)
                   (point-in-pxp-p point1 (prime))
                   (point-in-pxp-p point2 (prime))
                   (point-on-elliptic-curve-p point1 (prime) a b)
                   (point-on-elliptic-curve-p point2 (prime) a b))
              (point-on-elliptic-curve-p (curve-group-+ point1 point2
                                                        (prime) a b)
                                         (prime) a b))
     :hints (("Goal" :in-theory (e/d (point-on-elliptic-curve-p-equivalence
                                      curve-group-+-equivalence)
                                     (point-on-elliptic-curve-p
                                      pointp
                                      point-in-pxp-p))
              :use (simp-closure-of-curve-group-+
                    (:instance point-on-elliptic-curve-p-equivalence
                     (pt (simp-curve-group-+ point1 point2 a b))))))))

  (local
   (defthm primep-of-5
     (rtl::primep 5)
     :hints (("Goal" :in-theory (enable (:e rtl::primep))))))

  ;; Main closure theorem.
  ;; We now do a functional instantiation of PRIME.
  ;; This is the only theorems exported by this encapsulate.

  (defthm closure-of-curve-group-+
    (implies (and (natp a)
                  (natp b)
                  (rtl::primep p)
                  (< 3 p)
                  (pointp point1)
                  (pointp point2)
                  (point-in-pxp-p point1 p)
                  (point-in-pxp-p point2 p)
                  (point-on-elliptic-curve-p point1 p a b)
                  (point-on-elliptic-curve-p point2 p a b))
             (and (pointp (curve-group-+ point1 point2 p a b))
                  (point-in-pxp-p (curve-group-+ point1 point2 p a b) p)
                  (point-on-elliptic-curve-p (curve-group-+ point1 point2 p a b)
                                             p a b)))
    :hints (("Goal" :use ((:functional-instance
                           point-on-elliptic-curve-p-of-curve-group-+-abstract
                           (prime (lambda ()
                                    (if (not (and (rtl::primep p)
                                                  (> p 3)))
                                        5
                                      p))))
                          (:functional-instance
                           pointp-and-pointp-in-pxp-of-curve-group-+-abstract
                           (prime (lambda ()
                                    (if (not (and (rtl::primep p)
                                                  (> p 3)))
                                        5
                                      p)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Multiplication (by scalar) in the elliptic curve group.

;; Add POINT to itself S times.
;; This uses the exponentiation by squaring technique,
;; for efficiency when large numbers are involved.
;; In the future we may want to prove that this definition
;; is equivalent to the naive recursive one (perhaps using MBE),
;; but this may require the proof of additional properties of addition,
;; in particular associativity.
;; We may also want to prove additional properties for validation, e.g.
;; (equal (curve-scalar-* s g p a b)
;;        (curve-group-+ g (curve-scalar-* (1- s) g p a b)))

(defsection curve-scalar-*
  :parents (short-weierstrass)
  :short "Multiply an elliptic curve point by a scalar."
  :long "@(call curve-scalar-*) applies the elliptic group operation to @('s')
         copies of @('point').
         <p/>
         Since we use @('+') to describe the group operation, this
         operation can be thought of as multiplying @('point') by the scalar @('s').
         <p/>
         (Alternatively, for those who think of the group operation as
         multiplication, this operation can be thought of as exponentiation.)
         <p/>
         @('point') must be on the Short Weierstrass elliptic curve
         defined by @('p'), @('a'), and @('b').  If it is not, a guard
         violation occurs.
         <p/>
         The result is a point on the elliptic curve."
  (defund curve-scalar-* (s point p a b)
    (declare (xargs :guard (and (natp s)
                                (rtl::primep p)
                                (< 3 p)
                                (fep a p)
                                (fep b p)
                                (not (= b 0))
                                (pointp point)
                                (point-in-pxp-p point p)
                                (point-on-elliptic-curve-p point p a b))
                    :verify-guards nil)) ; done below
    (declare (xargs :measure (nfix s)))
    (if (zp s)
        '(0 . 0)
      (if (= s 1)
          point
        (if (evenp s)
            (let ((half-curve-scalar-* (curve-scalar-* (/ s 2) point p a b)))
              (curve-group-+ half-curve-scalar-* half-curve-scalar-* p a b))
          (curve-group-+ point (curve-scalar-* (- s 1) point p a b) p a b)))))
)

;; Prove closure of scalar multiplication by induction
;; (needed to verify guards).

(defthm closure-of-curve-scalar-*
  (implies (and (natp s)
                (rtl::primep p)
                (< 3 p)
                (natp a)
                (natp b)
                (pointp point)
                (point-in-pxp-p point p)
                (point-on-elliptic-curve-p point p a b))
           (and (pointp (curve-scalar-* s point p a b))
                (point-in-pxp-p (curve-scalar-* s point p a b) p)
                (point-on-elliptic-curve-p (curve-scalar-* s point p a b) p a b)))
  :hints (("Goal" :in-theory (e/d (curve-scalar-*)
                                  (point-on-elliptic-curve-p
                                   point-in-pxp-p
                                   pointp
                                   curve-group-+)))))

(verify-guards curve-scalar-*
  :hints (("Goal"
           :in-theory (e/d (evenp)
                           (closure-of-curve-scalar-*
                            pointp
                            point-in-pxp-p
                            point-on-elliptic-curve-p curve-group-+))
           :use ((:instance closure-of-curve-scalar-* (s (1- s)))
                 (:instance closure-of-curve-scalar-* (s (* 1/2 s)))))))

(defthm pointp-of-curve-scalar-*
  (implies (and (posp p)
                (natp a)
                (natp b)
                (pointp point))
           (pointp (curve-scalar-* s point p a b)))
  :hints (("Goal" :in-theory (enable curve-scalar-*))))

(defthm consp-of-curve-scalar-*
  (implies (consp point)
           (consp (curve-scalar-* s point p a b)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable curve-scalar-* pointp))))

(defthm point-in-pxp-p-of-curve-scalar-*
  (implies (and (natp s)
                (posp p)
                (natp a)
                (natp b)
                (pointp point)
                (point-in-pxp-p point p))
           (point-in-pxp-p (curve-scalar-* s point p a b) p))
  :hints (("Goal" :in-theory (enable curve-scalar-*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inverse (of addition) in the elliptic curve group.

;;  The negation of point (x,y) is (x,-y).
;;  Given x and y are in [0, .. p-1],
;;  -y = (p - y) mod p.

(defsection curve-negate
  :parents (short-weierstrass)
  :short "Negate an elliptic curve point."
  :long "@(call curve-negate) finds the inverse of @('point') with
         respect to the elliptic curve group operation.
         <p/>
         The result is a point on the elliptic curve.
         <p/>
         Note that the curve parameters @('a') and @('b') are irrelevant to
         this operation, so they are not parameters of this function."
  (defund curve-negate (point p)
    (declare (xargs :guard (and (rtl::primep p)
                                (< 3 p)
                                (pointp point)
                                (point-in-pxp-p point p))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (enable fep pointp point-in-pxp-p)))))
    (if (equal point '(0 . 0))
        point
      (cons (car point) (neg (cdr point) p))))
)

;; Prove closure of negation.

(encapsulate ()
  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm closure-of-curve-negate
    (implies (and (rtl::primep p)
                  (< 3 p)
                  (natp a)
                  (natp b)
                  (pointp point)
                  (point-in-pxp-p point p)
                  (point-on-elliptic-curve-p point p a b))
             (and (pointp (curve-negate point p))
                  (point-in-pxp-p (curve-negate point p) p)
                  (point-on-elliptic-curve-p (curve-negate point p) p a b)))
    :hints (("Goal" :in-theory (enable curve-negate
                                       pointp
                                       point-in-pxp-p
                                       point-on-elliptic-curve-p
                                       neg
                                       mul
                                       sub
                                       add)))))

(defthm pointp-of-curve-negate
  (implies (and (posp p)
                (pointp point))
           (pointp (curve-negate point p)))
  :hints (("Goal" :in-theory (enable curve-negate pointp))))

(defthm consp-of-curve-negate
  (consp (curve-negate point p))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable curve-negate))))

(defthm point-in-pxp-p-of-curve-negate
  (implies (and (posp p)
                (pointp point)
                (point-in-pxp-p point p))
           (point-in-pxp-p (curve-negate point p) p))
  :hints (("Goal" :in-theory (enable curve-negate
                                     pointp
                                     point-in-pxp-p
                                     neg sub))))
