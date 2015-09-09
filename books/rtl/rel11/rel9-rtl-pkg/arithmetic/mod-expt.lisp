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

(in-package "RTL")

;one of these is still broken


(include-book "power2p")


;don't need everything in this book!
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "nniq"))
(local (include-book "arith2"))
(local (include-book "ground-zero"))
(local (include-book "floor"))
(local (include-book "integerp"))
(local (include-book "rationalp"))
(local (include-book "unary-divide"))
(local (include-book "expt"))
(local (include-book "expo"))
(local (include-book "fl-expt"))
(local (include-book "mod"))
(local (include-book "fl"))

(local (in-theory (enable expt-minus)))

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defthmd fl-shift-pull-inside-mod
  (implies (and ;(rationalp x)
                (<= j i) ;what if not?
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 i))))
                  (mod (FL (* x (/ (EXPT 2 J))))
                       (expt 2 (- i j)))))
  :hints (("Goal" :in-theory (enable mod expt-split))))

(defthm mod-integerp-when-y-is-power-of-2
  (implies (integerp x)
           (integerp (mod x (expt 2 i))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :cases ((< i 0)))))

;Helpful, since if we split exponents, the rule above may not fire.
(defthm mod-integerp-when-y-is-power-of-2-gen
  (implies (and (integerp x)
                (syntaxp (power2-syntaxp y))
                (force (power2p y)))
           (integerp (mod x y)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable power2p-rewrite))))

(encapsulate
 ()
 (local (defthm mod-pull-inside-fl-shift-usual-case
          (implies (and (<= 0 i) ;this case
;                (rationalp x)
                        (case-split (integerp i)) ;may be droppable
                        (case-split (integerp j))
                        )
                   (equal (mod (FL (* x (/ (EXPT 2 J))))
                               (expt 2 i))
                          (FL (* (/ (EXPT 2 J))
                                 (MOD x (EXPT 2 (+ i j)))))))
          :otf-flg t
          :hints (("Goal" :use ((:instance fl-def-linear-part-1 (x (* X (/ (EXPT 2 I))
                                                                      (/ (EXPT 2 J)))))
                                (:instance fl-def-linear-part-2 (x (* X (/ (EXPT 2 I))
                                                                      (/ (EXPT 2 J))))))
                   :in-theory (set-difference-theories
                               (enable mod expt-split)
                               '(  FL-WEAK-MONOTONE
                                   fl-def-linear-part-1
                                   fl-def-linear-part-2)
                               )))))


 (local (defthm mod-pull-inside-fl-shift-other-case
          (implies (and (< i 0) ;this case
;                (rationalp x)
                        (case-split (integerp i))
                        (case-split (integerp J))

                        )
                   (equal (mod (FL (* x (/ (EXPT 2 J))))
                               (expt 2 i))
                          (FL (* (/ (EXPT 2 J))
                                 (MOD x (EXPT 2 (+ i j)))))))
          :otf-flg t
          :hints (("Goal" :use ((:instance <-transitive
                                           (a x)
                                           (b (+ (* (EXPT 2 I) (EXPT 2 J))
                                                 (* (EXPT 2 I)
                                                    (EXPT 2 J)
                                                    (FL (* X (/ (EXPT 2 I)) (/ (EXPT 2 J)))))))
                                           (c (+ (EXPT 2 J)
                                                 (* (EXPT 2 I)
                                                    (EXPT 2 J)
                                                    (FL (* X (/ (EXPT 2 I))
                                                           (/ (EXPT 2 J))))))))
                                (:instance fl-def-linear-part-1 (x (* X (/ (EXPT 2 I))
                                                                      (/ (EXPT 2 J)))))
                                (:instance fl-def-linear-part-2 (x (* X (/ (EXPT 2 I))
                                                                      (/ (EXPT 2 J))))))
                   :in-theory (set-difference-theories
                               (enable mod expt-split)
                               '(FL-WEAK-MONOTONE
;                         expt-compare
                                 fl-def-linear-part-1
                                 fl-def-linear-part-2)
                               )))))


;Basic idea: mod chops off some high bits from x and fl chops off some low bits.  We can do the chops in
;either order.
 (defthm mod-pull-inside-fl-shift
   (implies (and ;no hyp about x
             (case-split (integerp i))
             (case-split (integerp j))
             )
            (equal (mod (fl (* x (/ (expt 2 j))))
                        (expt 2 i))
                   (fl (* (/ (expt 2 j))
                          (mod x (expt 2 (+ i j)))))))
   :otf-flg t
   :hints (("goal" :cases ( (<= 0 i)))))
 )


(defthm mod-pull-inside-fl-shift-alt
  (implies (and ;(rationalp x)
                (integerp i)
                (integerp j)
                )
           (equal (mod (FL (* (/ (EXPT 2 J)) x))
                       (expt 2 i))
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ i j))))))))

(defthm mod-pull-inside-fl-shift-alt-alt
  (implies (and ;(rationalp x)
                (integerp i)
                (integerp j)
                )
           (equal (mod (FL (* (/ (EXPT 2 J)) x))
                       (* 2 (expt 2 i)))
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ i 1 j)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '(MOD-PULL-INSIDE-FL-SHIFT
                                mod-pull-inside-fl-shift-alt))
           :use (:instance mod-pull-inside-fl-shift
                           (i (+ i 1))))))

(defthm mod-pull-inside-fl-shift-alt-alt-alt
  (implies (and ;(rationalp x)
                (integerp j)
                )
           (equal (mod (FL (* (/ (EXPT 2 J)) x))
                       2)
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ 1 j)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '( MOD-PULL-INSIDE-FL-SHIFT
                                 mod-pull-inside-fl-shift-alt
                                 mod-pull-inside-fl-shift-alt-alt))
           :use (:instance mod-pull-inside-fl-shift-alt-alt
                           (i 0)))))

(defthm mod-pull-inside-fl-shift-alt-alt-alt-alt
  (implies (and ;(rationalp x)
                (integerp j)
                )
           (equal (mod (FL (* x (/ (EXPT 2 J)))) ;factors commuted
                       2)
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ 1 j)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '( MOD-PULL-INSIDE-FL-SHIFT
                                 mod-pull-inside-fl-shift-alt
                                 mod-pull-inside-fl-shift-alt-alt
                                 mod-pull-inside-fl-shift-alt-alt-alt))
           :use (:instance mod-pull-inside-fl-shift-alt-alt
                           (i 0)))))


;gen and move?
(defthm fl-mod-zero
  (implies (and (<= i2 i1)
                (integerp i1)
                (integerp i2)
                )
           (equal (FL (* (/ (EXPT 2 i1))
                         (MOD X (EXPT 2 i2))))
                  0))

  )



;generalize?
(defthm mod-pull-inside-fl-shift-alt-5
  (implies (and; (rationalp x)
                (integerp i)
                (integerp j)
                )
           (equal (mod (FL (* (/ (EXPT 2 J)) x))
                       (* 2 (expt 2 i)))
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ 1 i j)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '(
                               MOD-PULL-INSIDE-FL-SHIFT
                               mod-pull-inside-fl-shift-alt
                               mod-pull-inside-fl-shift-alt-alt
                               mod-pull-inside-fl-shift-alt-alt-alt))
           :use (:instance  mod-pull-inside-fl-shift-alt (i (+ i 1))))))


(defthm mod-pull-inside-fl-shift-alt-6
  (implies (and; (case-split (rationalp x))
                (integerp i)
                (integerp j)
                (integerp k)
                )
           (equal (mod (FL (* x (/ (EXPT 2 J))))
                       (* 2 (expt 2 i) (/ (expt 2 k))))
                  (FL (* (/ (EXPT 2 J))
                         (MOD x (EXPT 2 (+ 1 (- k) i j)))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '(
                               MOD-PULL-INSIDE-FL-SHIFT
                               mod-pull-inside-fl-shift-alt
                               mod-pull-inside-fl-shift-alt-alt
                               mod-pull-inside-fl-shift-alt-alt-alt
                               ))
           :use (:instance  mod-pull-inside-fl-shift-alt (i (+ i (- k) 1))))))

;why disable?
;use i and j
(defthmd mod-mod-eric
  (implies (and (<= i1 i2)
                (case-split (integerp i1))
                (case-split (integerp i2))
                )
           (= (mod (mod x (expt 2 i2)) (expt 2 i1))
              (mod x (expt 2 i1)))))


;conclude from something more general?
; NOTE: This is now a corollary of mod-of-mod.  But we might as well retain the
; original proof.
(defthmd mod-of-mod-cor
  (implies (and (<= b a)
                (case-split (integerp b))
                (case-split (integerp a))
                )
           (equal (mod (mod x (expt 2 a)) (expt 2 b))
                  (mod x (expt 2 b))))
  :hints (("Goal" :in-theory (enable mod-mod-eric)))
  )



#|

nice rules?

(local
 (defthm mod-2m-2n-k-1
   (implies (and (integerp m) (>= m n)
                 (integerp n) (> n k)
                 (integerp k) (> k 0))
            (= (mod (- (expt 2 m) (expt 2 (- n k)))
                    (expt 2 n))
               (mod (- (expt 2 n) (expt 2 (- n k)))
                    (expt 2 n))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable  a15)
            :use ((:instance mod-mult-eric
                             (x (- (expt 2 n) (expt 2 (- n k))))
                             (y (expt 2 n))
                             (a (1- (expt 2 (- m n)))))
                  (:instance expt-weak-monotone (n (- n k)) (m n)))))))

(local
(defthm mod-2m-2n-k-2
    (implies (and (integerp n) (> n k)
		  (integerp k) (> k 0))
	     (= (mod (- (expt 2 n) (expt 2 (- n k)))
		     (expt 2 n))
		(- (expt 2 n) (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance mod-does-nothing (m (- (expt 2 n) (expt 2 (- n k)))) (n (expt 2 n)))
			(:instance expt-weak-monotone (n (- n k)) (m n))))
)))

;nice rule?
(local
 (defthm mod-2m-2n-k
   (implies (and (integerp m) (>= m n)
                 (integerp n) (> n k)
                 (integerp k) (> k 0))
            (= (mod (- (expt 2 m) (expt 2 (- n k)))
                    (expt 2 n))
               (- (expt 2 n) (expt 2 (- n k)))))
   :rule-classes ()
   :hints (("goal" :use ((:instance mod-2m-2n-k-1)
                         (:instance mod-2m-2n-k-2))))))

|#

