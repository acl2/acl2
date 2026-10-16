; The primorial function and the bound primorial(m) <= 4^m
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "legendre")
(local (include-book "arithmetic-5/top" :dir :system))

;; The product of all primes <= m.
(defund primorial (m)
  (if (zp m)
      1
    (* (if (dm::primep m) m 1)
       (primorial (+ -1 m)))))

(defthm posp-of-primorial
  (posp (primorial m))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable primorial))))

(local
 (defthm primep-forward-primorial
   (implies (dm::primep p)
            (and (integerp p)
                 (< 1 p)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use dm::primep-gt-1))))

(defthm primorial-monotone
  (implies (and (<= i j)
                (natp i)
                (natp j))
           (<= (primorial i) (primorial j)))
  :rule-classes ((:linear :trigger-terms ((primorial i) (primorial j))))
  :hints (("Goal" :induct (primorial j)
           :in-theory (enable primorial))
          (and stable-under-simplificationp
               '(:nonlinearp t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm expt-lower-bound-primorial
   (implies (and (integerp k)
                 (< 1 k)
                 (natp e))
            (<= 1 (expt k e)))
   :rule-classes :linear))

(defthm binomial-prime-product-lower-bound
  (implies (and (natp a)
                (natp b))
           (<= 1 (binomial-prime-product a b k)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable binomial-prime-product))
          (and stable-under-simplificationp
               '(:nonlinearp t))))

(local
 (defthm floor-lower-bound-primorial
   (implies (and (<= p x)
                 (rationalp x)
                 (rationalp p)
                 (< 0 p))
            (<= 1 (floor x p)))
   :rule-classes nil))

;; Every prime q with k+1 < q <= 2k+1 divides (2k+1 choose k).
(defthm binomial-exponent-lower-bound-when-big-prime
  (implies (and (< (+ 1 k) q)
                (<= q (+ 1 (* 2 k)))
                (natp k)
                (integerp q))
           (<= 1 (binomial-exponent k (+ 1 k) q)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (binomial-exponent) (legendre-sum-of-+-1))
           :use ((:instance legendre-sum-unroll (m (+ 1 (* 2 k))) (p q))
                 (:instance floor-lower-bound-primorial
                            (x (+ 1 (* 2 k)))
                            (p q))))))

(local
 (defun dec-induct (j k)
   (declare (xargs :measure (nfix j)))
   (if (and (posp j)
            (< (+ 1 k) j))
       (dec-induct (+ -1 j) k)
     j)))

(local
 (defthm product-step-primorial
   (implies (and (<= pj1 (* c bj1))
                 (<= f g)
                 (<= 0 f)
                 (<= 0 pj1)
                 (<= 0 c)
                 (<= 0 bj1)
                 (rationalp f)
                 (rationalp g)
                 (rationalp pj1)
                 (rationalp c)
                 (rationalp bj1))
            (<= (* f pj1) (* c (* g bj1))))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm expt-when-exponent-at-least-1
   (implies (and (<= 1 e)
                 (integerp e)
                 (integerp j)
                 (< 1 j))
            (<= j (expt j e)))
   :rule-classes nil))

(local
 (defthm primorial-bound-by-binomial-prime-product-step
   (implies (and (<= (primorial (+ -1 j))
                     (* (primorial (+ 1 k))
                        (binomial-prime-product k (+ 1 k) (+ -1 j))))
                 (< (+ 1 k) j)
                 (<= j (+ 1 (* 2 k)))
                 (natp k)
                 (natp j))
            (<= (primorial j)
                (* (primorial (+ 1 k)) (binomial-prime-product k (+ 1 k) j))))
   :hints (("Goal" :expand ((primorial j)
                            (binomial-prime-product k (+ 1 k) j))
            :use ((:instance product-step-primorial
                             (pj1 (primorial (+ -1 j)))
                             (c (primorial (+ 1 k)))
                             (bj1 (binomial-prime-product k (+ 1 k) (+ -1 j)))
                             (f (if (dm::primep j) j 1))
                             (g (if (dm::primep j)
                                    (expt j (binomial-exponent k (+ 1 k) j))
                                  1)))
                  (:instance expt-when-exponent-at-least-1
                             (e (binomial-exponent k (+ 1 k) j))))
            :in-theory (disable primorial binomial-prime-product)))))

(local
 (defthm primorial-bound-by-binomial-prime-product-base
   (implies (natp k)
            (<= (primorial (+ 1 k))
                (* (primorial (+ 1 k))
                   (binomial-prime-product k (+ 1 k) (+ 1 k)))))
   :hints (("Goal" :nonlinearp t
            :in-theory (disable primorial binomial-prime-product)))))

(defthm primorial-bound-by-binomial-prime-product
  (implies (and (<= (+ 1 k) j)
                (<= j (+ 1 (* 2 k)))
                (natp k)
                (natp j))
           (<= (primorial j)
               (* (primorial (+ 1 k)) (binomial-prime-product k (+ 1 k) j))))
  :hints (("Goal" :induct (dec-induct j k)
           :in-theory (disable primorial binomial-prime-product))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Powers of 4.  We use our own function rather than EXPT, because the
;; arithmetic library normalizes powers of 4 inconsistently (sometimes to
;; powers of 2), which interferes with linear reasoning.

(defund power-of-4 (n)
  (if (zp n)
      1
    (* 4 (power-of-4 (+ -1 n)))))

(defthm posp-of-power-of-4
  (posp (power-of-4 n))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable power-of-4))))

(defthm power-of-4-of-+-1
  (implies (natp n)
           (equal (power-of-4 (+ 1 n))
                  (* 4 (power-of-4 n))))
  :hints (("Goal" :expand ((power-of-4 (+ 1 n))))))

(defthm power-of-4-of-+
  (implies (and (natp a)
                (natp b))
           (equal (power-of-4 (+ a b))
                  (* (power-of-4 a) (power-of-4 b))))
  :hints (("Goal" :induct (power-of-4 a)
           :in-theory (enable power-of-4))))

(defthm power-of-4-monotone
  (implies (and (<= a b)
                (natp a)
                (natp b))
           (<= (power-of-4 a) (power-of-4 b)))
  :rule-classes ((:linear :trigger-terms ((power-of-4 a) (power-of-4 b))))
  :hints (("Goal" :induct (power-of-4 b)
           :in-theory (enable power-of-4))))

(defthm power-of-4-becomes-expt
  (equal (power-of-4 n)
         (expt 4 (nfix n)))
  :hints (("Goal" :in-theory (enable power-of-4))))

(in-theory (disable power-of-4-becomes-expt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (2k+1 choose k) <= 4^k

(local
 (defthm scale-inequality-primorial
   (implies (and (<= x y)
                 (<= c d)
                 (<= 0 c)
                 (<= 0 y)
                 (rationalp x)
                 (rationalp y)
                 (rationalp c)
                 (rationalp d))
            (<= (* c x) (* d y)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm odd-binomial-bound-mult
   (implies (natp k)
            (<= (dm::fact (+ 1 (* 2 k)))
                (* (power-of-4 k) (dm::fact k) (dm::fact (+ 1 k)))))
   :hints (("Goal" :induct (dm::fact k)
            :in-theory (disable (:definition dm::fact)))
           ("Subgoal *1/2"
            :expand ((dm::fact (+ 1 (* 2 k)))
                     (dm::fact (* 2 k))
                     (dm::fact (+ 1 k))
                     (dm::fact k)
                     (power-of-4 k))
            :use ((:instance scale-inequality-primorial
                             (x (dm::fact (+ -1 (* 2 k))))
                             (y (* (power-of-4 (+ -1 k))
                                   (dm::fact (+ -1 k))
                                   (dm::fact k)))
                             (c (* (+ 1 (* 2 k)) (* 2 k)))
                             (d (* 4 (+ 1 k) k))))))))

(local
 (defthm posp-of-fact-primorial
   (posp (dm::fact n))
   :rule-classes :type-prescription))

(local
 (defthm divide-inequality-primorial
   (implies (and (<= x (* e d))
                 (< 0 d)
                 (rationalp x)
                 (rationalp e)
                 (rationalp d))
            (<= (/ x d) e))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm odd-binomial-bound
  (implies (natp k)
           (<= (/ (dm::fact (+ 1 (* 2 k)))
                  (* (dm::fact k) (dm::fact (+ 1 k))))
               (power-of-4 k)))
  :hints (("Goal" :use (odd-binomial-bound-mult
                        (:instance divide-inequality-primorial
                                   (x (dm::fact (+ 1 (* 2 k))))
                                   (e (power-of-4 k))
                                   (d (* (dm::fact k) (dm::fact (+ 1 k))))))
           :in-theory (disable odd-binomial-bound-mult
                               (:definition dm::fact)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; primorial(m) <= 4^m (Erdos)

(local
 (defun primorial-induct (m)
   (declare (xargs :measure (nfix m)))
   (if (and (natp m)
            (< 2 m))
       (if (integerp (/ m 2))
           (primorial-induct (+ -1 m))
         (primorial-induct (+ 1 (floor m 2))))
     m)))

(local
 (defthm not-primep-when-even
   (implies (and (integerp (/ m 2))
                 (< 2 m))
            (not (dm::primep m)))
   :hints (("Goal" :use (:instance dm::primep-no-divisor (p m) (d 2))
            :in-theory (enable dm::divides)))))

(local
 (defthm binomial-prime-product-odd-bound
   (implies (natp k)
            (<= (binomial-prime-product k (+ 1 k) (+ 1 (* 2 k)))
                (power-of-4 k)))
   :hints (("Goal" :use ((:instance odd-binomial-bound)
                         (:instance binomial-prime-product-when-<=
                                    (a k)
                                    (b (+ 1 k))
                                    (k (+ 1 (* 2 k)))))
            :in-theory (disable odd-binomial-bound
                                binomial-prime-product-when-<=
                                (:definition dm::fact))))))

(local
 (defthm primorial-bound-odd-step
   (implies (and (<= (primorial (+ 1 k)) (power-of-4 (+ 1 k)))
                 (posp k))
            (<= (primorial (+ 1 (* 2 k)))
                (power-of-4 (+ 1 (* 2 k)))))
   :hints (("Goal" :use ((:instance primorial-bound-by-binomial-prime-product
                                    (j (+ 1 (* 2 k))))
                         (:instance binomial-prime-product-odd-bound)
                         (:instance scale-inequality-primorial
                                    (x (binomial-prime-product
                                        k (+ 1 k) (+ 1 (* 2 k))))
                                    (y (power-of-4 k))
                                    (c (primorial (+ 1 k)))
                                    (d (power-of-4 (+ 1 k))))
                         (:instance power-of-4-of-+ (a (+ 1 k)) (b k)))
            :in-theory (disable primorial-bound-by-binomial-prime-product
                                binomial-prime-product-odd-bound
                                primorial
                                binomial-prime-product
                                binomial-prime-product-when-<=
                                power-of-4-of-+ power-of-4-of-+-1
                                (:definition dm::fact))))))

(local
 (defthm odd-as-double-floor-plus-1
   (implies (and (not (integerp (* 1/2 m)))
                 (integerp m))
            (equal (+ 1 (* 2 (floor m 2)))
                   m))
   :rule-classes nil))

(local
 (defthm primorial-bound-odd-case
   (implies (and (<= (primorial (+ 1 (floor m 2)))
                     (power-of-4 (+ 1 (floor m 2))))
                 (not (integerp (* 1/2 m)))
                 (< 2 m)
                 (natp m))
            (<= (primorial m)
                (power-of-4 m)))
   :hints (("Goal" :use ((:instance primorial-bound-odd-step (k (floor m 2)))
                         (:instance odd-as-double-floor-plus-1))
            :in-theory (disable primorial-bound-odd-step power-of-4-of-+-1)))))

(local
 (defthm primorial-bound-even-case
   (implies (and (<= (primorial (+ -1 m)) (power-of-4 (+ -1 m)))
                 (integerp (* 1/2 m))
                 (< 2 m)
                 (natp m))
            (<= (primorial m)
                (power-of-4 m)))
   :hints (("Goal" :expand ((primorial m)
                            (power-of-4 m))))))

(local
 (defthm primorial-bound-base-case
   (implies (and (<= m 2)
                 (natp m))
            (<= (primorial m)
                (power-of-4 m)))
   :hints (("Goal" :cases ((equal m 0) (equal m 1) (equal m 2))))))

(defthm primorial-bound
  (implies (natp m)
           (<= (primorial m) (power-of-4 m)))
  :hints (("Goal" :induct (primorial-induct m)
           :in-theory (disable primorial power-of-4-of-+-1))))
