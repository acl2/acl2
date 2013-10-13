#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;This file contains stuff proven using rtl's arithmetic.


(local (in-theory (disable expt)))

(defthm integer-range-p-extend-upper
  (implies (and (ACL2::INTEGER-RANGE-P lower upper x)
                (<= upper upper+))
           (ACL2::INTEGER-RANGE-P lower upper+ x))
  :hints (("Goal" :in-theory (enable ACL2::INTEGER-RANGE-P))))

(defthm integer-range-p-extend-lower
  (implies (and (ACL2::INTEGER-RANGE-P lower upper x)
                (<= lower- lower))
           (ACL2::INTEGER-RANGE-P lower- upper x))
  :hints (("Goal" :in-theory (enable ACL2::INTEGER-RANGE-P))))

; (Matt K., 10/2013: Changed rel8 to rel9.)
(local (include-book "rtl/rel9/arithmetic/expo" :dir :system))
(local (include-book "rtl/rel9/arithmetic/expt" :dir :system))
(local (include-book "rtl/rel9/arithmetic/top" :dir :system))

(local (in-theory (enable expt-split)))


;necessary for the stuff below
(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
        ((< x 0) '(2 . 0))
        ((< x 1) (cons 1 (fl (/ x))))
        (t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
        ((< x 0) (expo (- x)))
        ((< x 1) (1- (expo (* 2 x))))
        ((< x 2) 0)
        (t (1+ (expo (/ x 2))))))

(defund power2p-measure (x)
  (declare (xargs :guard (and (rationalp x) (not (equal x 0)))))
  (cond ((or (not (rationalp x))
             (<= x 0)) 0)
        ((< x 1) (cons 1 (fl (/ x))))
        (t (fl x))))

;disabled
(defund power2p (x)
  (declare (xargs :guard t :measure (power2p-measure x)
                  :hints (("goal" :in-theory (enable power2p-measure)))))
  (cond ((or (not (rationalp x)) (<= x 0)) nil)
        ((< x 1) (power2p (* 2 x)))
        ((<= 2 x) (power2p (* 1/2 x)))
        ((equal x 1) t)
        (t nil)))

;feed back to AMD?
(defthm expt-expo-when-power2p
  (implies (power2p x)
           (equal (expt 2 (expo x))
                  x))
  :hints (("Goal" :in-theory (e/d (expo power2p) (EXPO-MINUS-ERIC
                                                  EXPO-MINUS
                                                  expo-double
                                                  expo-half)))))

;consider and -alt form with LHS (unsigned-byte-p (+ m n) (* x (expt 2 m)))
(defthm unsigned-byte-p-shift-by-power-of-2
  (implies (and (unsigned-byte-p n x)
                (acl2::natp n)
                (<= 0 m) ;drop?
                (integerp m)
                )
           (unsigned-byte-p (+ m n) (* (expt 2 m) x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;generalize this?
(defthm unsigned-byte-p-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (integerp k)
                (unsigned-byte-p (- n (expo k)) x)
                )
           (equal (unsigned-byte-p n (* k x))
                  (natp n)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-shift-by-power-of-2)
           :use (:instance unsigned-byte-p-shift-by-power-of-2
                           (m (expo k))
                           (n (- n (expo k)))))))



;challenge that we can now handle:
;; (thm
;;  (implies (UNSIGNED-BYTE-P 8 x)
;;           (UNSIGNED-BYTE-P 16 (* 256 x))))


;bzo somehow, the arithmetic is stronger here than when we have the aamp model loaded?  why?
;bzo books/arithmetic is being used here.  consider using books/arithmetic-3 instead
;(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(defthm expo-expt2
  (equal (expo (expt 2 i))
         (if (integerp i)
             i
             0)))

;these are gross hacks that eric found rtl could prove but super-ihs couldn't.
;these should be cleaned up, or we should make a better floor-mod book.

(defthmd eric1
  (IMPLIES (AND (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (<= (FLOOR X (EXPT 2 SIZE)) B)
                (INTEGERP SIZE)
                (INTEGERP B)
                (INTEGERP X)
                )
           (<= X (* B (EXPT 2 SIZE)))))

;rtl can prove this
(defthmd eric2
  (IMPLIES (AND (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (< B (FLOOR X (EXPT 2 SIZE)))
                (INTEGERP SIZE)
      ;              (<= 0 SIZE)
                (INTEGERP B)
      ;               (<= 0 B)
                (INTEGERP X)
      ;                (<= 0 X)
                )
           (< (* B (EXPT 2 SIZE)) X)))

;rtl can prove this
(defthm rtl1
  (IMPLIES (AND (< I (* 2 Y))
                (NOT (INTEGERP (* 1/2 (FLOOR I Y))))
;(INTEGERP I)
                (<= 0 I)
                (rationalp y)
                )
           (EQUAL (FLOOR I Y)        
                  1)))


(defthm eric3
  (IMPLIES (AND (< B (FLOOR X (EXPT 2 SIZE)))
                (INTEGERP SIZE)
;                (<= 0 SIZE)
                (INTEGERP A)
;               (<= 0 A)
                (INTEGERP B)
;              (<= 0 B)
                (INTEGERP X)
;             (<= 0 X)
                )
           (< (+ (* B (EXPT 2 SIZE))
                 (* (EXPT 2 SIZE)
                    (MOD (* A (/ (EXPT 2 SIZE))) 1)))
              X)))

(defthm eric4
  (IMPLIES (AND (<= (FLOOR X (EXPT 2 SIZE)) B)
                (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (INTEGERP SIZE)
;                (<= 0 SIZE)
                (INTEGERP A)
;               (<= 0 A)
                (INTEGERP B)
;              (<= 0 B)
                (INTEGERP X)
;             (<= 0 X)
                )
           (<= X
               (+ (* B (EXPT 2 SIZE))
                  (* (EXPT 2 SIZE)
                     (MOD (* A (/ (EXPT 2 SIZE))) 1))))))

(defthm eric700
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (< I 32768)
                )
           (equal (INTEGERP (* 1/32768 I))
                  (equal i 0))))

(defthm eric9
  (IMPLIES (AND (INTEGERP X)
                (<= 0 X)
                (< X 65536)
                (NOT (ODDP (FLOOR X 32768))))
           (< X 32768))
  :hints (("Goal" :in-theory (enable oddp evenp))))

;bzo does RTL's ability to prove this reveal some rules we should add to super-ihs?
;should this be disabled?
(defthm floor-determined-1
  (implies (and (< i (* 2 j))
                (<= j i)
                (rationalp j)
                (rationalp i)
                )
           (equal (floor i j)
                  1)))

;rename?
;see lemma rtl1?
(defthm floor-simple-cases
  (implies (and (< i (* 2 j))
                (<= 0 i)
                (rationalp j)
                (rationalp i)
                )
           (equal (floor i j) ;floor-by-twice-hack took a term out of the normal form -huh?
                  (if (< i j)
                      0
                    1))))

