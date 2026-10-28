; Prime factorizations of factorials and binomial coefficients (Legendre)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "projects/numbers/euclid" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The p-adic valuation of a positive integer: the exponent of p in n.

(defund padic-valuation (p n)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (enable dm::divides)))))
  (if (and (integerp p)
           (< 1 p)
           (posp n)
           (dm::divides p n))
      (+ 1 (padic-valuation p (/ n p)))
    0))

(defthm padic-valuation-when-not-divides
  (implies (not (dm::divides p n))
           (equal (padic-valuation p n)
                  0))
  :hints (("Goal" :in-theory (enable padic-valuation))))

(defthm padic-valuation-of-*-same
  (implies (and (integerp p)
                (< 1 p)
                (posp m))
           (and (equal (padic-valuation p (* p m))
                       (+ 1 (padic-valuation p m)))
                (equal (padic-valuation p (* m p))
                       (+ 1 (padic-valuation p m)))))
  :hints (("Goal" :expand ((padic-valuation p (* p m))
                           (padic-valuation p (* m p)))
           :in-theory (enable dm::divides))))

(local
 (defthm primep-forward
   (implies (dm::primep p)
            (and (integerp p)
                 (< 1 p)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use dm::primep-gt-1))))

;; A prime q does not divide a different prime p.
(local
 (defthm not-divides-when-primes
   (implies (and (dm::primep p)
                 (dm::primep q)
                 (not (equal p q)))
            (not (dm::divides q p)))
   :hints (("Goal" :use (:instance dm::primep-no-divisor (p p) (d q))))))

(local
 (defthm divides-of-*-when-not-divides
   (implies (and (dm::primep q)
                 (integerp a)
                 (integerp b)
                 (not (dm::divides q a))
                 (not (dm::divides q b)))
            (not (dm::divides q (* a b))))
   :hints (("Goal" :use (:instance dm::euclid (p q))))))

(local
 (defthm integerp-of-quotient-when-divides
   (implies (dm::divides q m)
            (integerp (/ m q)))
   :hints (("Goal" :in-theory (enable dm::divides)))))

(local
 (defthm posp-of-quotient-when-divides
   (implies (and (dm::divides q m)
                 (posp m)
                 (< 0 q))
            (posp (/ m q)))
   :hints (("Goal" :in-theory (enable dm::divides)))))

(local
 (defthm divides-of-*-when-divides
   (implies (and (dm::divides q m)
                 (integerp p))
            (and (dm::divides q (* p m))
                 (dm::divides q (* m p))))
   :hints (("Goal" :use (:instance dm::divides-product (x q) (y m) (z p))))))

(defthmd padic-valuation-when-divides
  (implies (and (integerp p)
                (< 1 p)
                (posp n)
                (dm::divides p n))
           (equal (padic-valuation p n)
                  (+ 1 (padic-valuation p (/ n p)))))
  :hints (("Goal" :in-theory (enable padic-valuation))))

(defthm padic-valuation-of-*-other
  (implies (and (dm::primep p)
                (dm::primep q)
                (not (equal p q))
                (posp m))
           (and (equal (padic-valuation q (* p m))
                       (padic-valuation q m))
                (equal (padic-valuation q (* m p))
                       (padic-valuation q m))))
  :hints (("Goal" :induct (padic-valuation q m)
           :in-theory (enable padic-valuation-when-divides
                              (:induction padic-valuation)))))

(defthm padic-valuation-of-1
  (equal (padic-valuation p 1)
         0)
  :hints (("Goal" :in-theory (enable padic-valuation dm::divides))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The product, over all primes q <= k, of q^(padic-valuation q n).

(defund prime-power-product (n k)
  (if (zp k)
      1
    (* (if (dm::primep k) (expt k (padic-valuation k n)) 1)
       (prime-power-product n (+ -1 k)))))

(defthm posp-of-prime-power-product
  (posp (prime-power-product n k))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable prime-power-product))))

(defthm prime-power-product-of-1
  (equal (prime-power-product 1 k)
         1)
  :hints (("Goal" :in-theory (enable prime-power-product))))

(defthm prime-power-product-of-*-prime
  (implies (and (dm::primep p)
                (posp m))
           (equal (prime-power-product (* p m) k)
                  (if (and (natp k) (<= p k))
                      (* p (prime-power-product m k))
                    (prime-power-product m k))))
  :hints (("Goal" :in-theory (enable prime-power-product))))

(local
 (defthm least-prime-divisor-facts
   (implies (and (integerp n)
                 (< 1 n))
            (and (integerp (dm::least-prime-divisor n))
                 (<= 2 (dm::least-prime-divisor n))
                 (dm::primep (dm::least-prime-divisor n))
                 (dm::divides (dm::least-prime-divisor n) n)
                 (integerp (/ n (dm::least-prime-divisor n)))
                 (< 0 (/ n (dm::least-prime-divisor n)))
                 (<= (/ n (dm::least-prime-divisor n)) n)))
   :hints (("Goal" :use ((:instance dm::primep-least-prime-divisor)
                         (:instance dm::least-divisor-divides (k 2)))
            :in-theory (enable dm::divides)))))

(local
 (defthm least-prime-divisor-quotient-linear
   (implies (and (integerp n)
                 (< 1 n))
            (<= (/ n (dm::least-prime-divisor n)) n))
   :rule-classes :linear))

(local
 (defun least-prime-divisor-induct (n)
   (declare
    (xargs :measure (nfix n)
           :hints (("Goal" :use ((:instance dm::primep-least-prime-divisor)
                                 (:instance dm::least-divisor-divides (k 2)))
                    :in-theory (enable dm::divides)))))
   (if (and (integerp n) (< 1 n))
       (least-prime-divisor-induct (/ n (dm::least-prime-divisor n)))
     n)))

(local
 (defthm prime-power-product-when-<=-step
   (implies (and (integerp n)
                 (< 1 n)
                 (natp k)
                 (<= n k)
                 (equal (prime-power-product
                         (/ n (dm::least-prime-divisor n)) k)
                        (/ n (dm::least-prime-divisor n))))
            (equal (prime-power-product n k)
                   n))
   :hints (("Goal" :use ((:instance prime-power-product-of-*-prime
                                    (p (dm::least-prime-divisor n))
                                    (m (/ n (dm::least-prime-divisor n))))
                         (:instance dm::primep-least-prime-divisor)
                         (:instance dm::least-divisor-divides (k 2))
                         (:instance dm::divides-leq
                                    (x (dm::least-prime-divisor n))
                                    (y n)))
            :in-theory (e/d (dm::divides) (prime-power-product-of-*-prime))))))

(defthm prime-power-product-when-<=
  (implies (and (posp n)
                (natp k)
                (<= n k))
           (equal (prime-power-product n k)
                  n))
  :hints (("Goal" :induct (least-prime-divisor-induct n)
           :in-theory (disable dm::least-prime-divisor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Legendre's sum: floor(m/p) + floor(m/p^2) + floor(m/p^3) + ...
;; computed using floor(floor(m/p^i)/p) = floor(m/p^(i+1)).

(defund legendre-sum (m p)
  (declare (xargs :measure (nfix m)))
  (if (and (natp m)
           (integerp p)
           (< 1 p)
           (<= p m))
      (+ (floor m p) (legendre-sum (floor m p) p))
    0))

(defthm natp-of-legendre-sum
  (natp (legendre-sum m p))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable legendre-sum))))

(defthm legendre-sum-when-<
  (implies (< m p)
           (equal (legendre-sum m p)
                  0))
  :hints (("Goal" :in-theory (enable legendre-sum))))

(defthmd legendre-sum-unroll
  (implies (and (natp m)
                (integerp p)
                (< 1 p))
           (equal (legendre-sum m p)
                  (+ (floor m p) (legendre-sum (floor m p) p))))
  :hints (("Goal" :expand ((legendre-sum m p))
           :in-theory (enable legendre-sum))))

(local
 (defun legendre-sum-induct (m p)
   (declare (xargs :measure (nfix m)))
   (if (and (posp m)
            (integerp p)
            (< 1 p))
       (legendre-sum-induct (floor m p) p)
     m)))

(local
 (defthm mod-of-+-1
   (implies (and (natp m)
                 (integerp p)
                 (< 1 p))
            (equal (mod (+ 1 m) p)
                   (if (equal (mod m p) (+ -1 p))
                       0
                     (+ 1 (mod m p)))))
   :hints (("Goal" :in-theory (enable mod)))))

(local
 (defthm floor-of-+-1
   (implies (and (natp m)
                 (integerp p)
                 (< 1 p))
            (equal (floor (+ 1 m) p)
                   (if (dm::divides p (+ 1 m))
                       (+ 1 (floor m p))
                     (floor m p))))
   :hints (("Goal" :use ((:instance dm::divides-mod-0 (n p) (a (+ 1 m)))
                         (:instance mod-of-+-1))
            :in-theory (e/d (mod) (mod-of-+-1))))))

(local
 (defthmd quotient-of-+-1-when-divides
   (implies (and (natp m)
                 (integerp p)
                 (< 1 p)
                 (dm::divides p (+ 1 m)))
            (equal (/ (+ 1 m) p)
                   (+ 1 (floor m p))))
   :hints (("Goal" :use (floor-of-+-1)
            :in-theory (e/d (dm::divides) (floor-of-+-1))))))

(defthm legendre-sum-of-+-1
  (implies (and (natp m)
                (integerp p)
                (< 1 p))
           (equal (legendre-sum (+ 1 m) p)
                  (+ (legendre-sum m p) (padic-valuation p (+ 1 m)))))
  :hints (("Goal" :induct (legendre-sum-induct m p))
          ("Subgoal *1/1"
           :use ((:instance legendre-sum-unroll (m (+ 1 m)))
                 (:instance legendre-sum-unroll (m m))
                 (:instance padic-valuation-when-divides (n (+ 1 m)))
                 (:instance quotient-of-+-1-when-divides)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Legendre's formula, in product form: m! is the product, over all primes
;; q <= m, of q^(legendre-sum m q).

(defund legendre-product (m k)
  (if (zp k)
      1
    (* (if (dm::primep k) (expt k (legendre-sum m k)) 1)
       (legendre-product m (+ -1 k)))))

(defthm legendre-product-of-+-1
  (implies (natp m)
           (equal (legendre-product (+ 1 m) k)
                  (* (legendre-product m k) (prime-power-product (+ 1 m) k))))
  :hints (("Goal" :in-theory (enable legendre-product prime-power-product))))

(defthm legendre-product-of-0
  (equal (legendre-product 0 k)
         1)
  :hints (("Goal" :in-theory (enable legendre-product))))

(local
 (defthmd legendre-product-unroll-m
   (implies (posp m)
            (equal (legendre-product m k)
                   (* (legendre-product (+ -1 m) k) (prime-power-product m k))))
   :hints (("Goal" :use (:instance legendre-product-of-+-1 (m (+ -1 m)))
            :in-theory (disable legendre-product-of-+-1)))))

(defthm legendre-product-when-<=
  (implies (and (natp m)
                (natp k)
                (<= m k))
           (equal (legendre-product m k)
                  (dm::fact m)))
  :hints (("Goal" :induct (dm::fact m)
           :in-theory (enable dm::fact legendre-product-unroll-m))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Properties of legendre-sum

(local
 (defun legendre-sum-induct2 (x y p)
   (declare (xargs :measure (nfix y)))
   (if (and (posp y)
            (integerp p)
            (< 1 p))
       (legendre-sum-induct2 (floor x p) (floor y p) p)
     (list x y))))

(local
 (defthm floor-bounds-for-bertrand
   (implies (and (rationalp x)
                 (rationalp p)
                 (< 0 p))
            (and (<= (floor x p) (/ x p))
                 (< (/ x p) (+ 1 (floor x p)))))
   :rule-classes :linear))

(local
 (defthm quotient-monotone
   (implies (and (<= x y)
                 (rationalp x)
                 (rationalp y)
                 (rationalp p)
                 (< 0 p))
            (<= (/ x p) (/ y p)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm floor-monotone
   (implies (and (<= x y)
                 (rationalp x)
                 (rationalp y)
                 (rationalp p)
                 (< 0 p))
            (<= (floor x p) (floor y p)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance floor-bounds-for-bertrand)
                         (:instance floor-bounds-for-bertrand (x y)))
            :nonlinearp t
            :in-theory (disable floor-bounds-for-bertrand)))))

(defthm legendre-sum-monotone
  (implies (and (<= x y)
                (natp x)
                (natp y)
                (integerp p)
                (< 1 p))
           (<= (legendre-sum x p) (legendre-sum y p)))
  :rule-classes ((:linear :trigger-terms ((legendre-sum x p)
                                          (legendre-sum y p))))
  :hints (("Goal" :induct (legendre-sum-induct2 x y p))
          ("Subgoal *1/1" :use ((:instance legendre-sum-unroll (m x))
                                (:instance legendre-sum-unroll (m y))
                                (:instance floor-monotone)))))

(local
 (defthm floor-superadditive
   (implies (and (natp a)
                 (natp b)
                 (integerp p)
                 (< 1 p))
            (<= (+ (floor a p) (floor b p))
                (floor (+ a b) p)))
   :rule-classes :linear))

(local
 (defun legendre-sum-induct3 (a b p)
   (declare
    (xargs :measure (nfix (+ a b))
           :hints (("Goal" :use ((:instance floor-bounds-for-bertrand (x a))
                                 (:instance floor-bounds-for-bertrand (x b)))
                    :nonlinearp t
                    :in-theory (disable floor-bounds-for-bertrand)))))
   (if (and (natp a)
            (natp b)
            (posp (+ a b))
            (integerp p)
            (< 1 p))
       (legendre-sum-induct3 (floor a p) (floor b p) p)
     (list a b))))

(defthm legendre-sum-superadditive
  (implies (and (natp a)
                (natp b)
                (integerp p)
                (< 1 p))
           (<= (+ (legendre-sum a p) (legendre-sum b p))
               (legendre-sum (+ a b) p)))
  :rule-classes :linear
  :hints (("Goal" :induct (legendre-sum-induct3 a b p))
          ("Subgoal *1/1" :use ((:instance legendre-sum-unroll (m a))
                                (:instance legendre-sum-unroll (m b))
                                (:instance legendre-sum-unroll (m (+ a b)))
                                (:instance legendre-sum-monotone
                                           (x (+ (floor a p) (floor b p)))
                                           (y (floor (+ a b) p))))
           :in-theory (disable legendre-sum-monotone))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The exponent of the prime p in the binomial coefficient (a+b)!/(a!b!).

(defund binomial-exponent (a b p)
  (- (legendre-sum (+ a b) p)
     (+ (legendre-sum a p) (legendre-sum b p))))

(defthm natp-of-binomial-exponent
  (implies (and (natp a)
                (natp b)
                (integerp p)
                (< 1 p))
           (natp (binomial-exponent a b p)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable binomial-exponent))))

;; The product, over all primes q <= k, of q^(binomial-exponent a b q).

(defund binomial-prime-product (a b k)
  (if (zp k)
      1
    (* (if (dm::primep k) (expt k (binomial-exponent a b k)) 1)
       (binomial-prime-product a b (+ -1 k)))))

(defthm binomial-prime-product-times-legendre-products
  (implies (and (natp a)
                (natp b))
           (equal (* (binomial-prime-product a b k)
                     (legendre-product a k)
                     (legendre-product b k))
                  (legendre-product (+ a b) k)))
  :hints (("Goal" :in-theory (enable binomial-prime-product
                                     legendre-product
                                     binomial-exponent))))

;; For k large enough, binomial-prime-product is the binomial coefficient:
(defthm binomial-prime-product-when-<=
  (implies (and (natp a)
                (natp b)
                (natp k)
                (<= (+ a b) k))
           (equal (binomial-prime-product a b k)
                  (/ (dm::fact (+ a b))
                     (* (dm::fact a) (dm::fact b)))))
  :hints (("Goal" :use binomial-prime-product-times-legendre-products
           :in-theory
           (disable binomial-prime-product-times-legendre-products))))
