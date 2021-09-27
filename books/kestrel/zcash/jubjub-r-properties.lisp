; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "jubjub")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following belongs to the prime field library.

(defruled zero-when-equal-to-neg-with-odd-p
  (implies (and (fep x p)
                (posp p)
                (oddp p))
           (equal (equal x (neg x p))
                  (equal x 0)))
  :enable (fep neg oddp)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub-r-properties
  :short "Properties about @(tsee jubjub-r-pointp)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-jubjub-r-pointp-when-lower-order
  :short "If multiplying a non-zero point
          by a positive integer below @(tsee jubjub-r)
          yields the zero point,
          the non-zero point is not in @(tsee jubjub-r-pointp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the definition of having order @(tsee jubjub-r)."))
  (implies (and (jubjub-pointp point)
                (not (equal point (twisted-edwards-zero)))
                (posp k)
                (< k (jubjub-r))
                (equal (jubjub-mul k point)
                       (twisted-edwards-zero)))
           (not (jubjub-r-pointp point)))
  :enable (jubjub-r-pointp
           ecurve::twisted-edwards-point-orderp
           jubjub-curve
           jubjub-mul)
  :use (:instance ecurve::twisted-edwards-point-order-leastp-necc
        (point point)
        (order (jubjub-r))
        (curve (jubjub-curve))
        (order1 k)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-0-m1 ()
  :short "The point @($(0,-1)$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This point is not in @(tsee jubjub-r-pointp),
     because it is not zero and doubling it yields zero
     (so it cannot have order @(tsee jubjub-r)).
     This point plays a role in the proofs of
     other properties about @(tsee jubjub-r-pointp).")
   (xdoc::p
    "This is part of Theorem 5.4.7 in [ZPS]."))
  (ecurve::point-finite 0 (1- (jubjub-q)))
  ///

  (defruled point-0-m1-not-zero
    (not (equal (point-0-m1)
                (twisted-edwards-zero)))
    :enable twisted-edwards-zero)

  (defruled 2-point-0-m1-is-zero
    (equal (jubjub-mul 2 (point-0-m1))
           (twisted-edwards-zero))
    :enable twisted-edwards-zero)

  ;; Normally we would disable this at the end of this DEFINE,
  ;; but the following theorem overflows the stack on SBCL
  ;; if we leave this enabled.
  (in-theory (disable (:e point-0-m1)))

  (defrule point-0-m1-not-in-jubjub-r
    (not (jubjub-r-pointp (point-0-m1)))
    :use ((:instance not-jubjub-r-pointp-when-lower-order
           (point (point-0-m1))
           (k 2))
          point-0-m1-not-zero
          2-point-0-m1-is-zero)
    :enable jubjub-r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection not-jubjub-r-pointp-when-0-ordinate
  :short "A Jubjub point with 0 ordinate is not in @(tsee jubjub-r-pointp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This indirectly depends on the associativity of twisted Edwards addition,
     so we add that as a hypothesis
     (see @(tsee ecurve::twisted-edwards-add-associativity)).")
   (xdoc::p
    "From the curve equation and the fact that the ordinate is 0,
     it turns out that doubling the point yields @(tsee point-0-m1).
     Thus multiplying the point by 4 yields the zero point,
     and therefore the point does not have order @(tsee jubjub-r).
     The point itself is not the zero point, which is @($(0,1)$).")
   (xdoc::p
    "This is part of Theorem 5.4.7 in [ZPS]."))

  (defisar not-jubjub-r-pointp-when-0-ordinate
    (implies (and (ecurve::twisted-edwards-add-associativity)
                  (jubjub-pointp point)
                  (equal (jubjub-point->v point) 0))
             (not (jubjub-r-pointp point)))
    :proof
    ((:assume (:associativity (ecurve::twisted-edwards-add-associativity)))
     (:assume (:point (jubjub-pointp point)))
     (:assume (:v-is-0 (equal (jubjub-point->v point) 0)))
     (:derive (:a.u2-is-1 (equal (mul (jubjub-a)
                                      (mul (jubjub-point->u point)
                                           (jubjub-point->u point)
                                           (jubjub-q))
                                      (jubjub-q))
                                 1))
      :from (:point :v-is-0)
      :use (:instance jubjub-point-satisfies-curve-equation (uv point))
      :prep-books
      ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))
     (:derive (:2-point-is-point-0-m1 (equal (jubjub-mul 2 point)
                                             (point-0-m1)))
      :from (:point :v-is-0 :a.u2-is-1)
      :enable (jubjub-mul
               jubjub-pointp
               point-on-jubjub-p
               ecurve::twisted-edwards-mul
               ecurve::twisted-edwards-mul-nonneg
               ecurve::twisted-edwards-add
               jubjub-curve
               jubjub-q
               jubjub-a
               jubjub-d
               jubjub-point->u
               jubjub-point->v
               (:e point-0-m1)))
     (:derive (:2-2-point-is-2-point-0-m1
               (equal (jubjub-mul 2 (jubjub-mul 2 point))
                      (jubjub-mul 2 (point-0-m1))))
      :from (:2-point-is-point-0-m1))
     (:derive (:4-point-is-zero (equal (jubjub-mul 4 point)
                                       (twisted-edwards-zero)))
      :from (:2-2-point-is-2-point-0-m1 :point :associativity)
      :enable (2-point-0-m1-is-zero
               jubjub-mul
               jubjub-pointp
               point-on-jubjub-p))
     (:derive (:point-not-zero (not (equal point (twisted-edwards-zero))))
      :from (:v-is-0)
      :enable twisted-edwards-zero)
     (:derive (:not-jubjub-r-pointp (not (jubjub-r-pointp point)))
      :from (:4-point-is-zero :point :point-not-zero)
      :enable jubjub-r
      :use (:instance not-jubjub-r-pointp-when-lower-order (k 4)))
     (:qed))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled jubjub-r-doubling-of-nonzero-is-nonzero
  :short "Doubling a non-zero point in @(tsee jubjub-r-pointp)
          yields a non-zero point."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is because otherwise the point would have order 2."))
  (implies (and (jubjub-r-pointp point)
                (not (equal point
                            (twisted-edwards-zero))))
           (not (equal (jubjub-mul 2 point)
                       (twisted-edwards-zero))))
  :use (:instance ecurve::twisted-edwards-point-order-leastp-necc
        (point point)
        (curve (jubjub-curve))
        (order (jubjub-r))
        (order1 2))
  :enable (jubjub-r-pointp
           jubjub-mul
           jubjub-r
           ecurve::twisted-edwards-point-orderp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule jubjub-r-doubling-injectivity
  :short "Injectivity of doubling in @(tsee jubjub-r-pointp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by cases on whether the points are zero or not.
     The case in which they are both non-zero is the more complicated one:")
   (xdoc::ol
    (xdoc::li
     "Assume @($2P = 2Q$).")
    (xdoc::li
     "Since @($P$) and @($Q$) have order @($r$),
      we have @($rP = O = rQ$).")
    (xdoc::li
     "Since @($r$) is odd, @($r = 2k+1$) for some integer @($k$).")
    (xdoc::li
     "So from the equality at (2) we have
      @($k(2P)+P = (2k+1)P = (2k+1)Q = k(2Q)+Q$).")
    (xdoc::li
     "From the equality at (1),
      we also have @($k(2P) = k(2Q)$)
      and we can thus cancel them in the equality at (4),
      obtaining @($P = Q$).")))
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (jubjub-r-pointp x)
                (jubjub-r-pointp y))
           (equal (equal (jubjub-mul 2 x)
                         (jubjub-mul 2 y))
                  (equal x y)))
  :use (jubjbub-r-doubling-injectivity-when-first-is-zero
        jubjbub-r-doubling-injectivity-when-second-is-zero
        jubjub-r-doubling-injectivity-when-neither-is-zero)

  :prep-lemmas

  ((defrule jubjbub-r-doubling-injectivity-when-first-is-zero
     (implies (and (jubjub-r-pointp x)
                   (jubjub-r-pointp y)
                   (equal x (twisted-edwards-zero))
                   (equal (jubjub-mul 2 x)
                          (jubjub-mul 2 y)))
              (equal x y))
     :rule-classes nil
     :enable (twisted-edwards-zero)
     :use (:instance jubjub-r-doubling-of-nonzero-is-nonzero (point y)))

   (defrule jubjbub-r-doubling-injectivity-when-second-is-zero
     (implies (and (jubjub-r-pointp x)
                   (jubjub-r-pointp y)
                   (equal y (twisted-edwards-zero))
                   (equal (jubjub-mul 2 x)
                          (jubjub-mul 2 y)))
              (equal x y))
     :rule-classes nil
     :enable (twisted-edwards-zero)
     :use (:instance jubjub-r-doubling-of-nonzero-is-nonzero (point x)))

   (defisar jubjub-r-doubling-injectivity-when-neither-is-zero
     (implies (and (ecurve::twisted-edwards-add-associativity)
                   (jubjub-r-pointp x)
                   (jubjub-r-pointp y)
                   (not (equal x (twisted-edwards-zero)))
                   (not (equal y (twisted-edwards-zero)))
                   (equal (jubjub-mul 2 x)
                          (jubjub-mul 2 y)))
              (equal x y))
     :proof
     ((:assume (:associativity (ecurve::twisted-edwards-add-associativity)))
      (:assume (:point-x (jubjub-r-pointp x)))
      (:assume (:point-y (jubjub-r-pointp y)))
      (:let (zero (twisted-edwards-zero)))
      (:assume (:not-zero-x (not (equal x zero))))
      (:assume (:not-zero-y (not (equal y zero))))
      (:assume (:doubles-equal (equal (jubjub-mul 2 x)
                                      (jubjub-mul 2 y))))
      (:derive (:r-times-x (equal (jubjub-mul (jubjub-r) x) zero))
       :from (:point-x :not-zero-x)
       :enable (jubjub-r-pointp
                jubjub-mul
                ecurve::twisted-edwards-point-orderp))
      (:derive (:r-times-y (equal (jubjub-mul (jubjub-r) y) zero))
       :from (:point-y :not-zero-y)
       :enable (jubjub-r-pointp
                jubjub-mul
                ecurve::twisted-edwards-point-orderp))
      (:let (k (/ (1- (jubjub-r)) 2)))
      (:derive (:integer-k (integerp k))
       :enable jubjub-r)
      (:derive (:decompose (equal (jubjub-r)
                                  (+ (* 2 k) 1))))
      (:derive (:2k+1-times-x (equal (jubjub-mul (+ (* 2 k) 1) x) zero))
       :from (:r-times-x :decompose))
      (:derive (:2k+1-times-y (equal (jubjub-mul (+ (* 2 k) 1) y) zero))
       :from (:r-times-y :decompose))
      (:derive (:2k-times-x-plus-x (equal (jubjub-add (jubjub-mul (* 2 k) x)
                                                      x)
                                          zero))
       :from (:2k+1-times-x :point-x :associativity :integer-k)
       :use (:instance ecurve::twisted-edwards-mul-of-scalar-addition
             (point x)
             (curve (jubjub-curve))
             (scalar1 (* 2 (/ (1- (jubjub-r)) 2)))
             (scalar2 1))
       :enable (jubjub-add
                jubjub-mul
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p
                jubjub-r))
      (:derive (:2k-times-y-plus-y (equal (jubjub-add (jubjub-mul (* 2 k) y)
                                                      y)
                                          zero))
       :from (:2k+1-times-y :point-y :associativity :integer-k)
       :use (:instance ecurve::twisted-edwards-mul-of-scalar-addition
             (point y)
             (curve (jubjub-curve))
             (scalar1 (* 2 (/ (1- (jubjub-r)) 2)))
             (scalar2 1))
       :enable (jubjub-add
                jubjub-mul
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p
                jubjub-r))
      (:derive (:k-times-2-times-x-plus-x
                (equal (jubjub-add (jubjub-mul k
                                               (jubjub-mul 2 x))
                                   x)
                       zero))
       :from (:2k-times-x-plus-x :point-x :associativity :integer-k)
       :use (:instance ecurve::twisted-edwards-mul-of-mul
             (point x)
             (curve (jubjub-curve))
             (scalar1 2)
             (scalar (/ (1- (jubjub-r)) 2)))
       :disable ecurve::twisted-edwards-mul-of-mul
       :enable (jubjub-mul
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p
                jubjub-r))
      (:derive (:k-times-2-times-y-plus-y
                (equal (jubjub-add (jubjub-mul k
                                               (jubjub-mul 2 y))
                                   y)
                       zero))
       :from (:2k-times-y-plus-y :point-y :associativity :integer-k)
       :use (:instance ecurve::twisted-edwards-mul-of-mul
             (point y)
             (curve (jubjub-curve))
             (scalar1 2)
             (scalar (/ (1- (jubjub-r)) 2)))
       :disable ecurve::twisted-edwards-mul-of-mul
       :enable (jubjub-mul
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p
                jubjub-r))
      (:derive (:k-times-2-times-y-plus-x
                (equal (jubjub-add (jubjub-mul k
                                               (jubjub-mul 2 y))
                                   x)
                       zero))
       :from (:k-times-2-times-x-plus-x :doubles-equal))
      (:let (common (jubjub-mul k (jubjub-mul 2 y))))
      (:derive (:equality (equal (jubjub-add common x)
                                 (jubjub-add common y)))
       :from (:k-times-2-times-y-plus-x :k-times-2-times-y-plus-y))
      (:let (neg-common (jubjub-neg common)))
      (:derive (:add-same (equal (jubjub-add neg-common (jubjub-add common x))
                                 (jubjub-add neg-common (jubjub-add common y))))
       :from (:equality))
      (:derive (:point-common (jubjub-pointp common))
       :from (:point-y))
      (:derive (:point-neg-common (jubjub-pointp neg-common))
       :from (:point-common))
      (:derive (:simp-x (equal (jubjub-add neg-common (jubjub-add common x))
                               x))
       :from (:associativity :point-neg-common :point-common :point-x)
       :disable (ecurve::twisted-edwards-add-commutative
                 ecurve::twisted-edwards-add-associative-right)
       :enable (ecurve::twisted-edwards-add-associative-left
                jubjub-add
                jubjub-neg
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p))
      (:derive (:simp-y (equal (jubjub-add neg-common (jubjub-add common y))
                               y))
       :from (:associativity :point-neg-common :point-common :point-y)
       :disable (ecurve::twisted-edwards-add-commutative
                 ecurve::twisted-edwards-add-associative-right)
       :enable (ecurve::twisted-edwards-add-associative-left
                jubjub-add
                jubjub-neg
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p))
      (:derive (:final-equal (equal x y))
       :from (:add-same :simp-x :simp-y))
      (:qed))
     :rule-classes nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-jubjub-r-pointp-of-jubjub-r-point-with-neg-ordinate
  :short "Negating the ordinate of a point in @(tsee jubjub-r-pointp)
          yields a point that is not in @(tsee jubjub-r-pointp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is Theorem 4.5.7 in [ZPS].
     The proof here follows the one in [ZPS].
     It makes use of some of the preceding theorems."))
  (implies (and (ecurve::twisted-edwards-add-associativity)
                (jubjub-r-pointp point))
           (not (jubjub-r-pointp
                 (ecurve::point-finite
                  (jubjub-point->u point)
                  (neg (jubjub-point->v point) (jubjub-q))))))
  :use (zero-case nonzero-case)

  :prep-lemmas

  ((defisar zero-case
     (implies (equal point (twisted-edwards-zero))
              (not (jubjub-r-pointp
                    (ecurve::point-finite
                     (jubjub-point->u point)
                     (neg (jubjub-point->v point) (jubjub-q))))))
     :proof
     ((:assume (:zero (equal point (twisted-edwards-zero))))
      (:derive (:point-0-m1 (equal (ecurve::point-finite
                                    (jubjub-point->u point)
                                    (neg (jubjub-point->v point) (jubjub-q)))
                                   (point-0-m1)))
       :from (:zero)
       :enable (twisted-edwards-zero
                ecurve::point-finite
                jubjub-q
                (:e point-0-m1)))
      (:derive (:conclusion (not (jubjub-r-pointp
                                  (ecurve::point-finite
                                   (jubjub-point->u point)
                                   (neg (jubjub-point->v point) (jubjub-q))))))
       :from (:point-0-m1)
       :use point-0-m1-not-in-jubjub-r
       :disable point-0-m1-not-in-jubjub-r)
      (:qed)))

   (defisar nonzero-case
     (implies (and (ecurve::twisted-edwards-add-associativity)
                   (jubjub-r-pointp point)
                   (not (equal point (twisted-edwards-zero)))
                   (jubjub-r-pointp
                    (ecurve::point-finite
                     (jubjub-point->u point)
                     (neg (jubjub-point->v point) (jubjub-q)))))
              nil)
     :proof
     ((:assume (:associativity (ecurve::twisted-edwards-add-associativity)))
      (:assume (:point (jubjub-r-pointp point)))
      (:assume (:nonzero (not (equal point (twisted-edwards-zero)))))
      (:let (u (jubjub-point->u point)))
      (:let (v (jubjub-point->v point)))
      (:let (qoint (ecurve::point-finite u (neg v (jubjub-q)))))
      (:assume (:qoint (jubjub-r-pointp qoint)))
      (:derive (:2-point (jubjub-pointp (jubjub-mul 2 point)))
       :from (:point))
      (:derive (:2-qoint-is-minus-2-point
                (equal (jubjub-mul 2 qoint)
                       (jubjub-neg (jubjub-mul 2 point))))
       :from (:point :qoint :nonzero)
       :enable (jubjub-mul-of-2
                jubjub-add
                jubjub-neg
                jubjub-curve
                jubjub-point->u
                jubjub-point->v
                jubjub-r-pointp
                jubjub-pointp
                ecurve::twisted-edwards-add
                ecurve::twisted-edwards-neg
                ecurve::point-finite
                ecurve::point-finite->x
                ecurve::point-finite->y
                twisted-edwards-zero
                ecurve::point-kind
                ecurve::pointp
                div)
       :prep-books
       ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system)))
      (:derive (:2-qoint-is-m1-2-point
                (equal (jubjub-mul 2 qoint)
                       (jubjub-mul -1 (jubjub-mul 2 point))))
       :from (:2-qoint-is-minus-2-point :2-point)
       :enable (jubjub-mul
                jubjub-neg
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p))
      (:derive (:2-qoint-is-2-m1-point
                (equal (jubjub-mul 2 qoint)
                       (jubjub-mul 2 (jubjub-mul -1 point))))
       :from (:2-qoint-is-m1-2-point :associativity :point)
       :disable ecurve::twisted-edwards-mul-of-minus1
       :enable (jubjub-mul
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p))
      (:derive (:2-qoint-is-2-minus-point
                (equal (jubjub-mul 2 qoint)
                       (jubjub-mul 2 (jubjub-neg point))))
       :from (:2-qoint-is-2-m1-point :point)
       :enable (jubjub-mul
                jubjub-neg
                jubjub-r-pointp
                jubjub-pointp
                point-on-jubjub-p))
      (:derive (:qoint-is-minus-point
                (equal qoint (jubjub-neg point)))
       :from (:2-qoint-is-2-minus-point :point :qoint :associativity)
       :disable jubjub-r-doubling-injectivity
       :use (:instance jubjub-r-doubling-injectivity
             (x (ecurve::point-finite (jubjub-point->u point)
                                      (neg (jubjub-point->v point) (jubjub-q))))
             (y (jubjub-neg point))))
      (:derive (:neg-v-is-v (equal (jubjub-point->v point)
                                   (neg (jubjub-point->v point) (jubjub-q))))
       :from (:qoint-is-minus-point :point)
       :enable (ecurve::point-finite
                ecurve::point-finite->x
                ecurve::point-finite->y
                ecurve::twisted-edwards-neg
                twisted-edwards-zero
                ecurve::pointp
                jubjub-r-pointp
                jubjub-pointp
                jubjub-point->u
                jubjub-point->v
                jubjub-neg))
      (:derive (:v-is-0 (equal (jubjub-point->v point) 0))
       :from (:neg-v-is-v :point)
       :enable (fep
                jubjub-r-pointp
                jubjub-q
                zero-when-equal-to-neg-with-odd-p))
      (:derive (:not-point (not (jubjub-r-pointp point)))
       :from (:v-is-0 :point :associativity)
       :enable not-jubjub-r-pointp-when-0-ordinate)
      (:derive (:contradiction nil)
       :from (:not-point :point))
      (:qed))
     :rule-classes nil)))
