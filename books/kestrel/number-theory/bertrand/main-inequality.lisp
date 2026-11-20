; The inequality that makes Bertrand's Postulate hold for large n
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primorial") ; for pow4
(local (include-book "arithmetic-5/top" :dir :system))

;; We show: if x = 2n >= 2048, u^2 <= x, and m = floor(2n/3), then
;;   x^u * 4^m < 4^n.
;; The proof is integer-only: with L the number of bits of x, we have
;; x < 2^L and 9L^2 <= 2^(L-1) <= x, hence 3uL <= x, hence
;; x^(3u) < 2^(3uL) <= 2^x = 4^n <= (4^(n-m))^3, and so x^u < 4^(n-m).

;; The number of bits in x.
(defund bit-length (x)
  (if (zp x)
      0
    (+ 1 (bit-length (floor x 2)))))

(defthm natp-of-bit-length
  (natp (bit-length x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bit-length))))

(defthm bit-length-bounds
  (implies (posp x)
           (and (< x (expt 2 (bit-length x)))
                (<= (expt 2 (+ -1 (bit-length x))) x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bit-length))))

(defthm bit-length-at-least-12
  (implies (and (<= 2048 x)
                (integerp x))
           (<= 12 (bit-length x)))
  :rule-classes :linear
  :hints (("Goal" :use (bit-length-bounds
                        (:instance expt-is-weakly-increasing-for-base->-1
                                   (x 2) (m (bit-length x)) (n 11))))))

(local
 (defun induct-from-12 (l)
   (declare (xargs :measure (nfix l)))
   (if (and (integerp l)
            (< 12 l))
       (induct-from-12 (+ -1 l))
     l)))

(local
 (defthm square-step-bound
   (implies (and (<= 3 l)
                 (rationalp l))
            (<= (* (+ 1 l) (+ 1 l)) (* 2 l l)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthmd expt-2-of-+-1
   (implies (integerp i)
            (equal (expt 2 (+ 1 i))
                   (* 2 (expt 2 i))))))

(local
 (defthm nine-l-squared-bound-step
   (implies (and (<= (* 9 (+ -1 l) (+ -1 l)) p)
                 (<= 12 l)
                 (integerp l)
                 (rationalp p))
            (<= (* 9 l l) (* 2 p)))
   :rule-classes nil
   :hints (("Goal" :use (:instance square-step-bound (l (+ -1 l)))))))

(defthm nine-l-squared-bound
  (implies (and (<= 12 l)
                (integerp l))
           (<= (* 9 l l) (expt 2 (+ -1 l))))
  :rule-classes nil
  :hints (("Goal" :induct (induct-from-12 l))
          (and stable-under-simplificationp
               '(:use ((:instance nine-l-squared-bound-step
                                  (p (expt 2 (+ -2 l)))))))))

(local
 (defthm product-of-bounds
   (implies (and (<= a x)
                 (<= b x)
                 (<= 0 a)
                 (<= 0 b)
                 (rationalp a)
                 (rationalp b)
                 (rationalp x))
            (<= (* a b) (* x x)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm square-cancel
   (implies (and (<= (* a a) (* b b))
                 (<= 0 b)
                 (rationalp a)
                 (rationalp b))
            (<= a b))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm three-u-bit-length-bound
  (implies (and (<= (* u u) x)
                (<= 2048 x)
                (integerp x)
                (natp u))
           (<= (* 3 u (bit-length x)) x))
  :rule-classes nil
  :hints (("Goal" :use ((:instance bit-length-bounds)
                        (:instance nine-l-squared-bound (l (bit-length x)))
                        (:instance product-of-bounds
                                   (a (* 9 (bit-length x) (bit-length x)))
                                   (b (* u u)))
                        (:instance square-cancel
                                   (a (* 3 u (bit-length x)))
                                   (b x))))))

(local
 (defun pos-induct (e)
   (declare (xargs :measure (nfix e)))
   (if (and (integerp e)
            (< 1 e))
       (pos-induct (+ -1 e))
     e)))

(local
 (defthm expt-strictly-increasing-in-base-step
   (implies (and (< (expt a e) (expt b e))
                 (< a b)
                 (<= 0 a)
                 (rationalp a)
                 (rationalp b)
                 (posp e))
            (< (* a (expt a e)) (* b (expt b e))))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm expt-of-+-1-for-mono
   (implies (and (posp e)
                 (rationalp a))
            (equal (expt a e)
                   (* a (expt a (+ -1 e)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt a e))))))

(local
 (defthm expt-strictly-increasing-in-base
   (implies (and (< a b)
                 (<= 0 a)
                 (rationalp a)
                 (rationalp b)
                 (posp e))
            (< (expt a e) (expt b e)))
   :hints (("Goal" :induct (pos-induct e))
           (and stable-under-simplificationp
                '(:use ((:instance expt-strictly-increasing-in-base-step
                                   (e (+ -1 e)))
                        (:instance expt-of-+-1-for-mono)
                        (:instance expt-of-+-1-for-mono (a b))))))))

(local
 (defthm expt-x-3u-bound-1
   (implies (and (posp x)
                 (posp u))
            (< (expt x (* 3 u))
               (expt 2 (* 3 u (bit-length x)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance bit-length-bounds)
                         (:instance expt-strictly-increasing-in-base
                                    (a x)
                                    (b (expt 2 (bit-length x)))
                                    (e (* 3 u))))
            :in-theory (disable expt-strictly-increasing-in-base)))))

(local
 (defthm expt-x-3u-bound-2
   (implies (and (<= (* u u) x)
                 (<= 2048 x)
                 (integerp x)
                 (posp u))
            (<= (expt 2 (* 3 u (bit-length x)))
                (expt 2 x)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance three-u-bit-length-bound)
                         (:instance expt-is-weakly-increasing-for-base->-1
                                    (x 2) (m (* 3 u (bit-length x))) (n x)))))))

(defthm expt-x-3u-bound
  (implies (and (<= (* u u) x)
                (<= 2048 x)
                (integerp x)
                (posp u))
           (< (expt x (* 3 u)) (expt 2 x)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance expt-x-3u-bound-1)
                        (:instance expt-x-3u-bound-2))
           :in-theory (union-theories (theory 'minimal-theory) '(posp)))))

(defthm power-of-4-becomes-expt-2
  (implies (natp k)
           (equal (power-of-4 k)
                  (expt 2 (* 2 k))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable power-of-4))))

(local
 (defthm cube-cancel
   (implies (and (< (* a a a) (* b b b))
                 (<= 0 b)
                 (rationalp a)
                 (rationalp b))
            (< a b))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm cube-of-expt
   (implies (and (posp x)
                 (natp u))
            (equal (* (expt x u) (expt x u) (expt x u))
                   (expt x (* 3 u))))
   :rule-classes nil))

(local
 (defthm power-of-4-of-triple
   (implies (natp k)
            (equal (power-of-4 (* 3 k))
                   (* (power-of-4 k) (power-of-4 k) (power-of-4 k))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance power-of-4-of-+ (a k) (b k))
                         (:instance power-of-4-of-+ (a (* 2 k)) (b k)))
            :in-theory (disable power-of-4-of-+)))))

(local
 (defthm floor-facts-for-main
   (implies (natp n)
            (and (natp (floor (* 2 n) 3))
                 (natp (- n (floor (* 2 n) 3)))
                 (<= n (* 3 (- n (floor (* 2 n) 3))))))
   :rule-classes nil))

(local
 (defthm power-of-4-split-for-main
   (implies (natp n)
            (equal (power-of-4 n)
                   (* (power-of-4 (floor (* 2 n) 3))
                      (power-of-4 (- n (floor (* 2 n) 3))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance power-of-4-of-+
                                    (a (floor (* 2 n) 3))
                                    (b (- n (floor (* 2 n) 3))))
                         (:instance floor-facts-for-main))
            :in-theory (disable power-of-4-of-+)))))

(local
 (defthm power-of-4-monotone-for-main
   (implies (natp n)
            (<= (power-of-4 n)
                (power-of-4 (* 3 (- n (floor (* 2 n) 3))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance power-of-4-monotone
                                    (a n)
                                    (b (* 3 (- n (floor (* 2 n) 3)))))
                         (:instance floor-facts-for-main))
            :in-theory (disable power-of-4-monotone)))))

(local
 (defthm rationalp-of-expt-for-main
   (implies (integerp n)
            (rationalp (expt (* 2 n) u)))))

(local
 (defthm main-inequality-1
   (implies (and (<= (* u u) (* 2 n))
                 (<= 1024 n)
                 (integerp n)
                 (posp u))
            (< (expt (* 2 n) u)
               (power-of-4 (- n (floor (* 2 n) 3)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance cube-of-expt (x (* 2 n)))
                         (:instance expt-x-3u-bound (x (* 2 n)))
                         (:instance power-of-4-becomes-expt-2 (k n))
                         (:instance power-of-4-monotone-for-main)
                         (:instance power-of-4-of-triple
                                    (k (- n (floor (* 2 n) 3))))
                         (:instance floor-facts-for-main)
                         (:instance cube-cancel
                                    (a (expt (* 2 n) u))
                                    (b (power-of-4 (- n (floor (* 2 n) 3))))))
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(natp posp (:type-prescription expt)
                          rationalp-of-expt-for-main
                          (:type-prescription power-of-4)
                          (:type-prescription posp-of-power-of-4)))))))

(local
 (defthm scale-strict-for-main
   (implies (and (< a b)
                 (< 0 c)
                 (rationalp a)
                 (rationalp b)
                 (rationalp c))
            (< (* a c) (* b c)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

;; The main inequality.  Here x = 2n and u plays the role of 1 + (the number
;; of primes p with p^2 <= 2n).
(defthm main-inequality
  (implies (and (<= (* u u) (* 2 n))
                (<= 1024 n)
                (integerp n)
                (posp u))
           (< (* (expt (* 2 n) u)
                 (power-of-4 (floor (* 2 n) 3)))
              (power-of-4 n)))
  :hints (("Goal" :use ((:instance main-inequality-1)
                        (:instance power-of-4-split-for-main)
                        (:instance scale-strict-for-main
                                   (a (expt (* 2 n) u))
                                   (b (power-of-4 (- n (floor (* 2 n) 3))))
                                   (c (power-of-4 (floor (* 2 n) 3)))))
           :in-theory (disable power-of-4-of-+))))
