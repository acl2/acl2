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

(include-book "kestrel/number-theory/primep-def" :dir :system)
(include-book "points")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "short-weierstrass-closure-simp"))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system))
(local (include-book "kestrel/number-theory/primes" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ short-weierstrass-curves
  :parents (elliptic-curves)
  :short "Elliptic curves over prime fields in short Weierstrass form."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide executable formal specifications of operations on
     elliptic curves in short Weierstrass form,
     which are described by the equation")
   (xdoc::@[] "y^2 = x^3 + a x + b")
   (xdoc::p
    "where @($a$) and @($b$) are integers in a prime field @($\\{0,..,p-1\\}$)
     for an appropriate prime number @($p > 3$),
     satisfying the condition @($4 a^3 + 27 b^2 \\neq 0$),
     and where @($x$) and @($y$) range over the same prime field.
     The arithmetic operations in the equation above,
     namely addition and power (i.e. iterated multiplication),
     are prime field operations (i.e. modulo @($p$)).
     Besides the finite points @($(x,y)$) that satisfy the equation,
     the curve also includes a point at infinity.")
   (xdoc::p
    "When @($p = 2$) or @($p = 3$),
     the elliptic curve equation has different forms,
     not the short Weierstrass form.
     We may extend our formalization to cover those curves in the future.
     We may also extend it to cover curves over non-prime finite fields.")
   (xdoc::p
    "The condition @($4 a^3 + 27 b^2 \\neq 0$),
     where the operations are again field operations,
     means that the cubic equation on the right has no multiple roots.")
   (xdoc::p
    "See Neal Koblitz's book ``A Course in Number Theory and Cryptography''
     (Second Edition) for background on elliptic curves.")
   (xdoc::p
    "Our formalization follows "
    (xdoc::ahref "http://www.secg.org/sec1-v2.pdf"
                 "Standards for Efficient Cryptography 1 (SEC 1)")
    ", as well as
     ``The Elliptic Curve Digital Signature Algorithm (ECDSA)'',
     <i>International Journal of Information Security</i>,
     August 2001, Volume 1, Issue 1, pages 33-63."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod short-weierstrass
  :short "Fixtype of elliptic curves over prime fields
          in short Weierstrass form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of curve is specified by
     the prime @($p$) and the coefficients @($a$) and @($b$);
     see @(see short-weierstrass-curves).
     Thus, we formalize a curve as a triple of these numbers,
     via a fixtype product.")
   (xdoc::p
    "Because @('primep') is slow on large numbers,
     we do not include this requirement into the fixtype;
     otherwise, it may take a long time to construct a value of this fixtype
     for a practical curve.
     We just require @($p$) to be greater than 3;
     see @(see short-weierstrass-curves).
     We express the primality of @($p$) separately.")
   (xdoc::p
    "We require @($a$) and @($b$) to be in the prime field of @($p$).
     We also require them to satisfy the condition ensuring that
     the cubic equation has no multiple roots;
     see @(see short-weierstrass-curves).
     We express this condition by saying that
     @($4 a^3 + 27 b^2 \\mod p > 0$),
     where the operations are not field operations:
     this formulation is equivalent to requiring @($4 a^3 + 27 b^2$)
     with field operation to be different from 0.")
   (xdoc::p
    "To fix the three components to satisfy the requirements above,
     we pick 5 for @($p$), 0 for @($a$), and 1 for @($b$).
     It would be fine to pick 4 for @($p$) as far as this fixtype is concerned
     (since primality is not captured in the fixtype requirements),
     but we pick a prime (the smallest one above 3)
     since we know that this should be a prime."))
  ((p nat :reqfix (if (and (> p 3)
                           (fep a p)
                           (fep b p)
                           (posp (mod (+ (* 4 a a a) (* 27 b b)) p)))
                      p
                    5))
   (a nat :reqfix (if (and (> p 3)
                           (fep a p)
                           (fep b p)
                           (posp (mod (+ (* 4 a a a) (* 27 b b)) p)))
                      a
                    0))
   (b nat :reqfix (if (and (> p 3)
                           (fep a p)
                           (fep b p)
                           (posp (mod (+ (* 4 a a a) (* 27 b b)) p)))
                      b
                    1)))
  :require (and (> p 3)
                (fep a p)
                (fep b p)
                (posp (mod (+ (* 4 a a a) (* 27 b b)) p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-weierstrass-primep ((curve short-weierstrass-p))
  :returns (yes/no booleanp)
  :short "Check that the prime of a short Weierstrass curve is prime."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is in a separate predicate
     for the reason explained in @(tsee short-weierstrass)."))
  (rtl::primep (short-weierstrass->p curve))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Uses of the following predicate will be replaced by SHORT-WEIERSTRASS-P
; (see above), and the following predicate will be eventually eliminated.

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
;; Or it is the point at infinity.

;; Tests if a point is on an elliptic curve of the form explained above.

(defsection point-on-weierstrass-elliptic-curve-p
  :parents (short-weierstrass)
  :short "Test if a point is on an elliptic curve."
  :long "@(call point-on-weierstrass-elliptic-curve-p) tests whether
          @('point') is on the Short Weierstrass elliptic curve
          defined by @('p'), @('a'), and @('b').
         <p/>
         @('point') is either the infinity point @(':infinity'),
         or an ordered pair (a cons) of two integers in @('\{0,..,p-1\}')."
  (defund point-on-weierstrass-elliptic-curve-p (point p a b)
    (declare (xargs :guard (and (rtl::primep p)
                                (< 3 p)
                                (fep a p)
                                (fep b p)
                                (pointp point)
                                (point-in-pxp-p point p))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (enable fep pointp point-in-pxp-p)))))
    (or (eq point :infinity)
        (let ((x (car point))
              (y (cdr point)))
          (let ((y^2 (mul y y p))
                (x^3 (mul x (mul x x p) p)))
            (let ((x^3+ax+b (add x^3
                                 (add (mul a x p)
                                      b
                                      p)
                                 p)))
              (equal y^2 x^3+ax+b)))))))

;; The infinity point is on the curve.

(defthm point-on-weierstrass-elliptic-curve-p-of-inf
  (implies (< 0 p)
           (point-on-weierstrass-elliptic-curve-p :infinity p a b))
  :hints (("Goal" :in-theory (enable point-on-weierstrass-elliptic-curve-p))))

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
                                (pointp point1)
                                (pointp point2)
                                (point-in-pxp-p point1 p)
                                (point-in-pxp-p point2 p)
                                (point-on-weierstrass-elliptic-curve-p point1 p a b)
                                (point-on-weierstrass-elliptic-curve-p point2 p a b))
                    :guard-hints (("Goal"
                                   :in-theory
                                   (enable fep
                                           pointp
                                           point-in-pxp-p
                                           point-on-weierstrass-elliptic-curve-p)))))
    (declare (ignore b))
    (if (equal point1 :infinity)
        point2 ; handles rule 1 (O+O=O) and half of rule 2 (O+Q=Q)
      (if (equal point2 :infinity)
          point1 ; handles the other half of rule 2 (P+O=P)
        (let ((x1 (car point1))
              (y1 (cdr point1))
              (x2 (car point2))
              (y2 (cdr point2)))
          (if (= x1 x2)
              (if (= (add y1 y2 p) 0)
                  :infinity ; rule 3, y1 = -y2 (mod p)
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
  (equal (curve-group-+ :infinity point p a b)
         point)
  :hints (("Goal" :in-theory (enable curve-group-+))))

(defthm curve-group-+-right-identity
  (equal (curve-group-+ point :infinity p a b)
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
;; point-on-weierstrass-elliptic-curve-p and curve-group-+,
;; and "transfer" it to the versions of these two functions
;; as defined here in this file.

(encapsulate ()

  (local (include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system))
  (local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

  (local
   (defthmd point-on-weierstrass-elliptic-curve-p-equivalence
     (implies (and (integerp a)
                   (integerp b)
                   (pointp pt))
              (iff (point-on-weierstrass-elliptic-curve-p pt (prime) a b)
                   (simp-point-on-weierstrass-elliptic-curve-p pt a b)))
     :hints (("Goal" :in-theory (e/d (P[X.Y]
                                      simp-point-on-weierstrass-elliptic-curve-p
                                      pointp
                                      point-on-weierstrass-elliptic-curve-p
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
                   (point-on-weierstrass-elliptic-curve-p point1 (prime) a b)
                   (point-on-weierstrass-elliptic-curve-p point2 (prime) a b))
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
                   (point-on-weierstrass-elliptic-curve-p point1 (prime) a b)
                   (point-on-weierstrass-elliptic-curve-p point2 (prime) a b))
              (and (pointp (curve-group-+ point1 point2 (prime) a b))
                   (point-in-pxp-p (curve-group-+ point1 point2 (prime) a b)
                                   (prime))))
     :hints (("Goal"
              :in-theory (e/d (curve-group-+-equivalence
                               pointp-and-point-in-pxp-p-of-simp-curve-group-+)
                              (curve-group-+
                               pointp
                               point-in-pxp-p
                               point-on-weierstrass-elliptic-curve-p))))))

  (local
   (defthmd point-on-weierstrass-elliptic-curve-p-of-curve-group-+-abstract
     (implies (and (integerp a)
                   (integerp b)
                   (pointp point1)
                   (pointp point2)
                   (point-in-pxp-p point1 (prime))
                   (point-in-pxp-p point2 (prime))
                   (point-on-weierstrass-elliptic-curve-p point1 (prime) a b)
                   (point-on-weierstrass-elliptic-curve-p point2 (prime) a b))
              (point-on-weierstrass-elliptic-curve-p (curve-group-+ point1 point2
                                                                    (prime) a b)
                                                     (prime) a b))
     :hints (("Goal" :in-theory (e/d (point-on-weierstrass-elliptic-curve-p-equivalence
                                      curve-group-+-equivalence)
                                     (point-on-weierstrass-elliptic-curve-p
                                      pointp
                                      point-in-pxp-p))
              :use (simp-closure-of-curve-group-+
                    (:instance point-on-weierstrass-elliptic-curve-p-equivalence
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
                  (point-on-weierstrass-elliptic-curve-p point1 p a b)
                  (point-on-weierstrass-elliptic-curve-p point2 p a b))
             (and (pointp (curve-group-+ point1 point2 p a b))
                  (point-in-pxp-p (curve-group-+ point1 point2 p a b) p)
                  (point-on-weierstrass-elliptic-curve-p (curve-group-+ point1 point2 p a b)
                                                         p a b)))
    :hints (("Goal" :use ((:functional-instance
                           point-on-weierstrass-elliptic-curve-p-of-curve-group-+-abstract
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
                                      p))))))))

  )

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
                                (pointp point)
                                (point-in-pxp-p point p)
                                (point-on-weierstrass-elliptic-curve-p point p a b))
                    :verify-guards nil)) ; done below
    (declare (xargs :measure (nfix s)))
    (if (zp s)
        :infinity
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
                (point-on-weierstrass-elliptic-curve-p point p a b))
           (and (pointp (curve-scalar-* s point p a b))
                (point-in-pxp-p (curve-scalar-* s point p a b) p)
                (point-on-weierstrass-elliptic-curve-p (curve-scalar-* s point p a b) p a b)))
  :hints (("Goal" :in-theory (e/d (curve-scalar-*)
                                  (point-on-weierstrass-elliptic-curve-p
                                   point-in-pxp-p
                                   pointp
                                   curve-group-+)))))

(verify-guards curve-scalar-*
  :hints (("Goal"
           :in-theory (e/d (evenp)
                           (closure-of-curve-scalar-*
                            pointp
                            point-in-pxp-p
                            point-on-weierstrass-elliptic-curve-p curve-group-+))
           :use ((:instance closure-of-curve-scalar-* (s (1- s)))
                 (:instance closure-of-curve-scalar-* (s (* 1/2 s)))))))

(defthm pointp-of-curve-scalar-*
  (implies (and (posp p)
                (natp a)
                (natp b)
                (pointp point))
           (pointp (curve-scalar-* s point p a b)))
  :hints (("Goal" :in-theory (enable curve-scalar-*))))

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
    (if (equal point :infinity)
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
                  (point-on-weierstrass-elliptic-curve-p point p a b))
             (and (pointp (curve-negate point p))
                  (point-in-pxp-p (curve-negate point p) p)
                  (point-on-weierstrass-elliptic-curve-p (curve-negate point p) p a b)))
    :hints (("Goal" :in-theory (e/d (curve-negate
                                     pointp
                                     point-in-pxp-p
                                     point-on-weierstrass-elliptic-curve-p
                                     neg
                                     mul
                                     sub
                                     add)
                                    (;; to avoid loops:
                                     acl2::mod-sum-cases))))))

(defthm pointp-of-curve-negate
  (implies (and (posp p)
                (pointp point))
           (pointp (curve-negate point p)))
  :hints (("Goal" :in-theory (enable curve-negate pointp))))

(defthm point-in-pxp-p-of-curve-negate
  (implies (and (posp p)
                (pointp point)
                (point-in-pxp-p point p))
           (point-in-pxp-p (curve-negate point p) p))
  :hints (("Goal" :in-theory (enable curve-negate
                                     pointp
                                     point-in-pxp-p
                                     neg sub))))
