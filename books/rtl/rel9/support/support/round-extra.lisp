; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

; This book was originally certified (in some directory, probably not support/)
; starting with:

; (include-book "rtl/rel4/lib/top" :dir :system)

; Then that form was replaced by the forms below, up through the form (local
; (in-theory (theory 'lib-top1))).  See the comments at the top of
; fadd-extra.lisp for further explanation of how to extend the library.

(include-book "sticky") ; needed for some definitions
(include-book "util")   ; needed for definition of local-defthm

; Now put ourselves in what amounts to the environment of ../lib/top, as
; explained above.
(local (include-book "top1"))
(local (in-theory (theory 'lib-top1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; sticky-monotone
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here is David Russinoff's proof outline for sticky-monotone.

; Proof:
;
; By sticky-pos, sticky-0, and sticky-minus, we may assume x > 0.
;
; By expo-sticky, we nay assume expo(x) = expo(y).
;
; By trunc-monotone and the definition of sticky, we nay assume that
; y is (n-1)-exact and x is not (n-1)-exact.
;
; By fp+2, since y > x > trunc(x,n-1),
;
;   sticky(y,n) = y
;              >= fp+(trunc(x,n-1),n-1)
;               = trunc(x,n-1) + 2^(expo(trunc(x,n-1)) + 1 - (n-1))
;               > trunc(x,n-1) + 2^(expo(trunc(x,n-1)) + 1 - n)
;               = trunc(x,n-1) + 2^(expo(x) + 1 - n)
;               = sticky(x,n).

; [end of proof outline for sticky-monotone]

(local-defthm main-1
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (exactp y (1- n))
                (not (exactp x (1- n)))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (>= y (fp+ (trunc x (1- n)) (1- n))))
  :hints (("Goal" :use ((:instance fp+2
                                   (y y)
                                   (x (trunc x (1- n)))
                                   (n (1- n))))
           :in-theory (enable trunc-upper-pos)))
  :rule-classes nil)

(local-defthm main-2
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (exactp y (1- n))
                (not (exactp x (1- n)))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (> (fp+ (trunc x (1- n)) (1- n))
              (+ (trunc x (1- n))
                 (expt 2 (+ (expo (trunc x (1- n)))
                            1
                            (- n))))))
  :hints (("Goal" :use ((:instance expt-strong-monotone
                                   (n (+ 1 (expo x) (* -1 n)))
                                   (m (+ 2 (expo x) (* -1 n)))))))
  :rule-classes nil)

(local-defthm main
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (exactp y (1- n))
                (not (exactp x (1- n)))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (>= y (sticky x n)))
  :hints (("Goal" :use (main-1 main-2)
           :in-theory (enable sgn)
           :expand ((sticky x n))))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main-1
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (exactp y (1- n))
                (not (exactp x (1- n)))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :use main
           :expand ((sticky y n))))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main-2
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (not (exactp y (1- n)))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :in-theory (enable sticky sgn)
           :use ((:instance trunc-monotone (n (1- n)))
                 (:instance trunc-exactp-b (x x) (n (1- n))))))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main-3
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (exactp x (1- n))
                (exactp y (1- n))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 1))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :in-theory (enable sticky)))
  :rule-classes nil)

(defthm sticky-monotone-pos-main-n=1
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (rationalp x)
                (rationalp y))
           (<= (sticky x 1) (sticky y 1)))
  :hints (("Goal" :expand ((sticky x 1) (sticky y 1))
           :in-theory (enable sgn)))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main
  (implies (and (<= x y)
                (< 0 x)
                (equal (expo x) (expo y))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :use (sticky-monotone-pos-main-1
                        sticky-monotone-pos-main-2
                        sticky-monotone-pos-main-3
                        sticky-monotone-pos-main-n=1)
           :in-theory (enable sgn)))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main-alt-1
  (implies (and (<= x y)
                (< 0 x)
                (< (expo x) (expo y))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (< (expo (sticky x n)) (expo (sticky y n))))
  :hints (("Goal" :use ((:instance expo-sticky (x x))
                        (:instance expo-sticky (x y)))))
  :rule-classes nil)

(local-defthm sticky-monotone-pos-main-alt
  (implies (and (<= x y)
                (< 0 x)
                (< (expo x) (expo y))
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :use (sticky-monotone-pos-main-alt-1
                        (:instance expo-monotone
                                   (x (sticky y n))
                                   (y (sticky x n))))

           :in-theory (enable sticky-pos)))
  :rule-classes nil)

(local-defthm sticky-monotone-pos
  (implies (and (<= x y)
                (< 0 x)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :use (sticky-monotone-pos-main
                        sticky-monotone-pos-main-alt
                        expo-monotone)))
  :rule-classes nil)

(local-defthm sticky-monotone-neg
  (implies (and (<= x y)
                (< y 0)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (sticky x n) (sticky y n)))
  :hints (("Goal" :use ((:instance sticky-monotone-pos
                                   (x (- y))
                                   (y (- x))))
           :in-theory (enable sticky-minus)))
  :rule-classes nil)

(local-defthm sticky-nonneg-type-prescription
  (implies (and (<= 0 x)
                (rationalp x)
                (integerp n)
                (> n 0))
           (and (rationalp (sticky x n))
                (>= (sticky x n) 0)))
  :hints (("Goal" :in-theory (enable sticky-pos)
           :use ((:theorem (implies (and (<= 0 x)
                                         (rationalp x))
                                    (or (equal x 0)
                                        (< 0 x)))))))
  :rule-classes :type-prescription)

(local-defthm sticky-nonpos-type-prescription
  (implies (and (<= x 0)
                (rationalp x)
                (integerp n)
                (> n 0))
           (and (rationalp (sticky x n))
                (<= (sticky x n) 0)))
  :hints (("Goal" :use ((:instance sticky-nonneg-type-prescription
                                   (x (- x))))
           :in-theory (enable sticky-minus)))
  :rule-classes :type-prescription)

;;(i-am-here) ;; Fri Oct 13 12:30:27 2006

(encapsulate ()
    (local
       (defthmd sticky-monotone-support
         (implies (and (<= x y)
                       (rationalp x)
                       (rationalp y)
                       (integerp n)
                       (> n 0))
                  (<= (sticky x n) (sticky y n)))
         :hints (("Goal" :use (sticky-monotone-pos
                               sticky-monotone-neg)))
         :rule-classes :linear))

    (encapsulate ()
       (local (include-book "trunc"))
       (defthm trunc-to-0
         (implies (and (integerp n)
                       (<= n 0))
                  (equal (trunc x n) 0))
         :hints (("Goal" :by trunc-to-0-or-fewer-bits))))

    (local
      (defthm |1/2-sig-x-not-integerp-lemma|
        (implies (and (rationalp x)
                      (not (equal x 0))
                      (rationalp y)
                      (< 0 y)
                      (<= y 1/2))
                 (not (integerp (* (sig x) y))))
        :hints (("Goal" :use ((:instance sig-upper-bound)
                              (:instance sig-lower-bound))))))


    (local
     (defthm exactp-minus-fact
       (implies (and (integerp n)
                     (rationalp x)
                     (not (equal x 0))
                     (<= n 0))
                (not (exactp x n)))
       :hints (("Goal" :in-theory (enable exactp)
                :use ((:instance sig-upper-bound)
                      (:instance sig-lower-bound)
                      (:instance |1/2-sig-x-not-integerp-lemma|
                                 (y (expt 2 (+ -1 n))))
                      (:instance expt-weak-monotone-linear
                                 (n (+ -1 n))
                                 (m -1)))))))

  (defthmd sticky-monotone
    (implies (and (<= x y)
                  (rationalp x)
                  (rationalp y)
                  (natp n))
             (<= (sticky x n) (sticky y n)))
    :hints (("Goal" :cases ((not (equal n 0)))
             :in-theory (enable sticky sgn))
            ("Subgoal 2" :cases ((not (equal y 0))))
            ("Subgoal 2.1" :use ((:instance expo-monotone
                                            (y x)
                                            (x y))
                                 (:instance expo-monotone
                                            (x x)
                                            (y y))
                                 (:instance expt-weak-monotone-linear
                                            (n (+ 1 (expo y)))
                                            (m (+ 1 (expo x))))
                                 (:instance expt-weak-monotone-linear
                                            (n (+ 1 (expo x)))
                                            (m (+ 1 (expo y))))))
            ("Subgoal 1" :use ((:instance sticky-monotone-support))))
    :rule-classes :linear))

