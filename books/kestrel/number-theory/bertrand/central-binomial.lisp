; Bounds on the prime powers dividing the central binomial coefficient
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primorial")
(local (include-book "arithmetic-5/top" :dir :system))

;; The exponent of p in (2n)!/(n!)^2 is (legendre-sum 2n p) - 2*(legendre-sum n
;; p).  We analyze the more general quantity (legendre-sum x p) -
;; 2*(legendre-sum y p), where x is 2y or 2y+1, since that form is preserved
;; when x and y are both divided by p.

(local
 (defthm floor-bounds-central-binomial
   (implies (and (rationalp x)
                 (rationalp p)
                 (< 0 p))
            (and (<= (floor x p) (/ x p))
                 (< (/ x p) (+ 1 (floor x p)))))
   :rule-classes :linear))

(local
 (defthm floor-of-double-bounds-aux
   (implies (and (integerp z)
                 (integerp q)
                 (integerp p)
                 (< 1 p)
                 (<= (* 2 p q) z)
                 (< z (* p (+ 2 (* 2 q)))))
            (and (<= (* 2 q) (floor z p))
                 (<= (floor z p) (+ 1 (* 2 q)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable floor-bounds-central-binomial)
            :use ((:instance floor-bounds-central-binomial (x z)))
            :nonlinearp t))))

(local
 (defthm floor-of-double-bounds-aux2
   (implies (and (equal (+ r (* p q)) y)
                 (integerp x)
                 (integerp q)
                 (integerp r)
                 (integerp p)
                 (< 1 p)
                 (<= 0 r)
                 (<= r (+ -1 p))
                 (<= (* 2 y) x)
                 (<= x (+ 1 (* 2 y))))
            (and (<= (* 2 q) (floor x p))
                 (<= (floor x p) (+ 1 (* 2 q)))))
   :rule-classes nil
   :hints (("Goal" :use (:instance floor-of-double-bounds-aux (z x))))))

(local
 (defthm floor-mod-facts-central-binomial
   (implies (and (integerp y)
                 (integerp p)
                 (< 0 p))
            (and (equal (+ (mod y p) (* p (floor y p))) y)
                 (integerp (mod y p))
                 (integerp (floor y p))
                 (<= 0 (mod y p))
                 (<= (mod y p) (+ -1 p))))
   :rule-classes nil))

(local
 (defthm floor-of-double-bounds
   (implies (and (<= (* 2 y) x)
                 (<= x (+ 1 (* 2 y)))
                 (integerp x)
                 (natp y)
                 (integerp p)
                 (< 1 p))
            (and (<= (* 2 (floor y p)) (floor x p))
                 (<= (floor x p) (+ 1 (* 2 (floor y p))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance floor-of-double-bounds-aux2
                                    (q (floor y p))
                                    (r (mod y p)))
                         (:instance floor-mod-facts-central-binomial))
            :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local
 (defun double-induct (x y p)
   (declare (xargs :measure (nfix x)))
   (if (and (posp x)
            (integerp p)
            (< 1 p))
       (double-induct (floor x p) (floor y p) p)
     (list x y))))

(defund central-exponent (x y p)
  (- (legendre-sum x p) (* 2 (legendre-sum y p))))

(defthmd central-exponent-unroll
  (implies (and (natp x)
                (natp y)
                (integerp p)
                (< 1 p))
           (equal (central-exponent x y p)
                  (+ (- (floor x p) (* 2 (floor y p)))
                     (central-exponent (floor x p) (floor y p) p))))
  :hints (("Goal" :in-theory (enable central-exponent)
           :use ((:instance legendre-sum-unroll (m x))
                 (:instance legendre-sum-unroll (m y))))))

(defthm central-exponent-when-<
  (implies (and (< x p)
                (<= y x))
           (equal (central-exponent x y p)
                  0))
  :hints (("Goal" :in-theory (enable central-exponent))))

(local
 (defthm p-times-floor-linear
   (implies (and (rationalp x)
                 (integerp p)
                 (< 0 p))
            (<= (* p (floor x p)) x))
   :rule-classes :linear
   :hints (("Goal" :use (:instance floor-bounds-central-binomial)
            :in-theory (disable floor-bounds-central-binomial)
            :nonlinearp t))))

(local
 (defthmd expt-of-+-1-central-binomial
   (implies (and (integerp i)
                 (rationalp x)
                 (not (equal 0 x)))
            (equal (expt x (+ 1 i))
                   (* x (expt x i))))))

;; Core arithmetic of the inductive step below.
(local
 (defthm expt-of-central-exponent-bound-step-core
   (implies (and (integerp d)
                 (<= 0 d)
                 (<= d 1)
                 (integerp g)
                 (<= (expt p g) xp)
                 (<= (* p xp) x)
                 (integerp p)
                 (< 1 p)
                 (rationalp xp)
                 (rationalp x))
            (<= (expt p (+ d g)) x))
   :rule-classes nil
   :hints (("Goal" :cases ((equal d 0))
            :nonlinearp t
            :use ((:instance expt-of-+-1-central-binomial (x p) (i g)))))))

(local
 (defthm expt-of-central-exponent-bound-step
   (implies (and (<= (expt p (central-exponent (floor x p) (floor y p) p))
                     (floor x p))
                 (<= (* 2 y) x)
                 (<= x (+ 1 (* 2 y)))
                 (natp x)
                 (natp y)
                 (integerp p)
                 (< 1 p))
            (<= (expt p (central-exponent x y p)) x))
   :hints (("Goal" :use ((:instance central-exponent-unroll)
                         (:instance floor-of-double-bounds)
                         (:instance p-times-floor-linear)
                         (:instance expt-of-central-exponent-bound-step-core
                                    (d (- (floor x p) (* 2 (floor y p))))
                                    (g (central-exponent
                                        (floor x p) (floor y p) p))
                                    (xp (floor x p))))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(natp
                                         (:type-prescription floor)
                                         (:type-prescription central-exponent)
                                         (:type-prescription expt)))))))

;; p^(central-exponent x y p) <= x.  This is the key fact that each prime
;; power dividing the central binomial coefficient (2n choose n) is at most 2n.
(defthm expt-of-central-exponent-bound
  (implies (and (<= (* 2 y) x)
                (<= x (+ 1 (* 2 y)))
                (posp x)
                (natp y)
                (integerp p)
                (< 1 p))
           (<= (expt p (central-exponent x y p)) x))
  :hints (("Goal" :induct (double-induct x y p))
          (and stable-under-simplificationp
               '(:use ((:instance floor-of-double-bounds))
                 :cases ((< x p))))))

;; If x < p^2, then p appears at most once.
(defthm central-exponent-bound-when-small
  (implies (and (< x (* p p))
                (<= (* 2 y) x)
                (<= x (+ 1 (* 2 y)))
                (natp x)
                (natp y)
                (integerp p)
                (< 1 p))
           (<= (central-exponent x y p) 1))
  :hints (("Goal" :use ((:instance central-exponent-unroll)
                        (:instance floor-of-double-bounds)
                        (:instance floor-bounds-central-binomial)
                        (:instance central-exponent-when-<
                                   (x (floor x p))
                                   (y (floor y p))))
           :in-theory (disable central-exponent-when-<
                               floor-bounds-central-binomial)
           :nonlinearp t)))

(local
 (defthm floor-when-bounds-central-binomial
   (implies (and (<= (* k p) x)
                 (< x (* (+ 1 k) p))
                 (integerp k)
                 (rationalp x)
                 (rationalp p)
                 (< 0 p))
            (equal (floor x p)
                   k))
   :hints (("Goal" :use (:instance floor-bounds-central-binomial)
            :in-theory (disable floor-bounds-central-binomial)
            :nonlinearp t))))

;; Primes p with 2n/3 < p <= n do not divide the central binomial coefficient
;; (2n choose n), provided p >= 3.
(defthm central-exponent-when-middle-third
  (implies (and (<= p n)
                (< (* 2 n) (* 3 p))
                (<= 3 p)
                (integerp p)
                (natp n))
           (equal (central-exponent (* 2 n) n p)
                  0))
  :hints (("Goal" :use ((:instance central-exponent-unroll (x (* 2 n)) (y n))
                        (:instance floor-when-bounds-central-binomial
                                   (x (* 2 n))
                                   (k 2))
                        (:instance floor-when-bounds-central-binomial
                                   (x n)
                                   (k 1)))
           :in-theory (disable floor-when-bounds-central-binomial))))

(defthm binomial-exponent-same-becomes-central-exponent
  (equal (binomial-exponent n n p)
         (central-exponent (* 2 n) n p))
  :hints (("Goal" :in-theory (enable binomial-exponent central-exponent))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; No primes in a range

;; Checks that no q with lo < q <= hi is prime.
(defund no-primes-between (lo hi)
  (declare (xargs :measure (nfix (- hi lo))))
  (if (and (integerp lo)
           (integerp hi)
           (< lo hi))
      (and (not (dm::primep hi))
           (no-primes-between lo (+ -1 hi)))
    t))

(defthm not-primep-when-no-primes-between
  (implies (and (no-primes-between lo hi)
                (< lo q)
                (<= q hi)
                (integerp lo)
                (integerp hi)
                (integerp q))
           (not (dm::primep q)))
  :hints (("Goal" :in-theory (enable no-primes-between))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Counting the primes q <= k with q^2 <= x

(defund small-prime-count (x k)
  (if (zp k)
      0
    (+ (if (and (dm::primep k)
                (<= (* k k) x))
           1
         0)
       (small-prime-count x (+ -1 k)))))

(local
 (defthm primep-forward-central-binomial
   (implies (dm::primep p)
            (and (integerp p)
                 (< 1 p)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use dm::primep-gt-1))))

(local
 (defthm small-prime-count-upper-bound
   (implies (posp k)
            (<= (small-prime-count x k) (+ -1 k)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable small-prime-count)))))

(local
 (defthm square-monotone-central-binomial
   (implies (and (<= a b)
                 (<= 0 a)
                 (rationalp a)
                 (rationalp b))
            (<= (* a a) (* b b)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

;; If c primes q satisfy q^2 <= x, then (c+1)^2 <= x, since those primes are
;; distinct integers >= 2.
(defthm small-prime-count-squared-bound
  (implies (and (posp x)
                (natp k))
           (<= (* (+ 1 (small-prime-count x k))
                  (+ 1 (small-prime-count x k)))
               x))
  :hints (("Goal" :induct (small-prime-count x k)
           :in-theory (enable small-prime-count))
          (and stable-under-simplificationp
               '(:use ((:instance square-monotone-central-binomial
                                  (a (+ 1 (small-prime-count x (+ -1 k))))
                                  (b (+ -1 k)))
                       (:instance small-prime-count-upper-bound
                                  (k (+ -1 k))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bounding each prime-power factor of the central binomial coefficient

;; An upper bound on the factor q^(binomial-exponent n n q), assuming no primes
;; in (n, 2n]:
(defund central-factor-bound (n q)
  (if (dm::primep q)
      (if (<= (* q q) (* 2 n))
          (* 2 n)
        (if (<= (* 3 q) (* 2 n))
            q
          1))
    1))

(local
 (defthm expt-when-exponent-0-or-1-central-binomial
   (implies (and (natp e)
                 (<= e 1)
                 (integerp q)
                 (< 1 q))
            (<= (expt q e) q))
   :rule-classes nil
   :hints (("Goal" :cases ((equal e 0))))))

(defthm expt-of-binomial-exponent-bound
  (implies (and (no-primes-between n (* 2 n))
                (natp n)
                (<= 3 n)
                (dm::primep q))
           (<= (expt q (binomial-exponent n n q))
               (central-factor-bound n q)))
  :hints (("Goal" :in-theory (enable central-factor-bound)
           :cases ((<= (* q q) (* 2 n))
                   (and (< (* 2 n) (* q q)) (<= (* 3 q) (* 2 n)))
                   (and (< (* 2 n) (* 3 q)) (<= q n))
                   (and (< n q) (<= q (* 2 n)))
                   (< (* 2 n) q)))
          ("Subgoal 5" :use (:instance expt-of-central-exponent-bound
                                       (x (* 2 n))
                                       (y n)
                                       (p q)))
          ("Subgoal 4" :use ((:instance central-exponent-bound-when-small
                                        (x (* 2 n))
                                        (y n)
                                        (p q))
                             (:instance natp-of-binomial-exponent
                                        (a n)
                                        (b n)
                                        (p q))
                             (:instance
                              expt-when-exponent-0-or-1-central-binomial
                                        (e (central-exponent (* 2 n) n q))))
           :in-theory (e/d (central-factor-bound) (natp-of-binomial-exponent)))
          ("Subgoal 3" :use (:instance central-exponent-when-middle-third (p q))
           :nonlinearp t)
          ("Subgoal 2" :use (:instance not-primep-when-no-primes-between
                                       (lo n) (hi (* 2 n))))
          ("Subgoal 1" :use (:instance central-exponent-when-<
                                       (x (* 2 n))
                                       (y n)
                                       (p q)))))

(defund central-product-bound (n k)
  (if (zp k)
      1
    (* (central-factor-bound n k)
       (central-product-bound n (+ -1 k)))))

(local
 (defthm product-step-central-binomial
   (implies (and (<= b w)
                 (<= f g)
                 (<= 0 f)
                 (<= 0 b)
                 (rationalp f)
                 (rationalp g)
                 (rationalp b)
                 (rationalp w))
            (<= (* f b) (* g w)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm natp-of-central-product-bound
  (implies (natp n)
           (natp (central-product-bound n k)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable central-product-bound
                                     central-factor-bound))))

(defthm natp-of-central-factor-bound
  (implies (natp n)
           (natp (central-factor-bound n k)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable central-factor-bound))))

(defthm central-product-bound-when-zp
  (implies (zp k)
           (equal (central-product-bound n k)
                  1))
  :hints (("Goal" :in-theory (enable central-product-bound))))

(defthm binomial-prime-product-when-zp
  (implies (zp k)
           (equal (binomial-prime-product a b k)
                  1))
  :hints (("Goal" :in-theory (enable binomial-prime-product))))

(local
 (defthm binomial-prime-product-bound-by-central-product-bound-step
   (implies (and (<= (binomial-prime-product n n (+ -1 k))
                     (central-product-bound n (+ -1 k)))
                 (posp k)
                 (no-primes-between n (* 2 n))
                 (natp n)
                 (<= 3 n))
            (<= (binomial-prime-product n n k)
                (central-product-bound n k)))
   :hints (("Goal" :expand ((binomial-prime-product n n k)
                            (central-product-bound n k))
            :use ((:instance product-step-central-binomial
                             (f (if (dm::primep k)
                                    (expt k (binomial-exponent n n k))
                                  1))
                             (g (central-factor-bound n k))
                             (b (binomial-prime-product n n (+ -1 k)))
                             (w (central-product-bound n (+ -1 k))))
                  (:instance expt-of-binomial-exponent-bound (q k)))
            :in-theory
            (e/d (central-factor-bound)
                 (expt-of-binomial-exponent-bound
                  binomial-exponent-same-becomes-central-exponent))))))

(defthm binomial-prime-product-bound-by-central-product-bound
  (implies (and (no-primes-between n (* 2 n))
                (natp n)
                (<= 3 n))
           (<= (binomial-prime-product n n k)
               (central-product-bound n k)))
  :hints (("Goal" :induct (central-product-bound n k)
           :in-theory (e/d ((:induction central-product-bound))
                           ((:definition binomial-prime-product)
                            (:definition central-product-bound))))))

;; The product of the primes q <= k with 2n < q^2 and 3q <= 2n.
(defund medium-primes-product (n k)
  (if (zp k)
      1
    (* (if (and (dm::primep k)
                (< (* 2 n) (* k k))
                (<= (* 3 k) (* 2 n)))
           k
         1)
       (medium-primes-product n (+ -1 k)))))

(defthm central-product-bound-decomposition
  (implies (posp n)
           (equal (central-product-bound n k)
                  (* (expt (* 2 n) (small-prime-count (* 2 n) k))
                     (medium-primes-product n k))))
  :hints (("Goal" :in-theory (enable central-product-bound
                                     central-factor-bound
                                     medium-primes-product
                                     small-prime-count))))

(defthm medium-primes-product-bound
  (<= (medium-primes-product n k) (primorial k))
  :hints (("Goal" :in-theory (enable medium-primes-product primorial))
          (and stable-under-simplificationp
               '(:nonlinearp t))))

(local
 (defthm three-times-le-iff
   (implies (and (integerp k)
                 (integerp n))
            (iff (<= (* 3 k) (* 2 n))
                 (<= k (floor (* 2 n) 3))))
   :hints (("Goal" :use (:instance floor-bounds-central-binomial
                                   (x (* 2 n))
                                   (p 3))
            :in-theory (disable floor-bounds-central-binomial)))))

(local
 (defun down-to-induct (k m)
   (declare (xargs :measure (nfix k)))
   (if (and (posp k)
            (natp m)
            (< m k))
       (down-to-induct (+ -1 k) m)
     k)))

(local
 (defthm medium-primes-product-when-big-aux
   (implies (and (< (* 2 n) (* 3 (+ 1 m)))
                 (<= m k)
                 (natp m)
                 (natp k))
            (equal (medium-primes-product n k)
                   (medium-primes-product n m)))
   :hints (("Goal" :induct (down-to-induct k m)
            :in-theory (enable medium-primes-product)))))

(defthm medium-primes-product-when-big
  (implies (and (<= (floor (* 2 n) 3) k)
                (natp k)
                (natp n))
           (equal (medium-primes-product n k)
                  (medium-primes-product n (floor (* 2 n) 3))))
  :hints (("Goal" :use ((:instance medium-primes-product-when-big-aux
                                   (m (floor (* 2 n) 3)))
                        (:instance floor-bounds-central-binomial
                                   (x (* 2 n))
                                   (p 3)))
           :in-theory (disable medium-primes-product-when-big-aux
                               floor-bounds-central-binomial))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Upper bound on (2n choose n) when there is no prime in (n, 2n]

(local
 (defthm scale-left-central-binomial
   (implies (and (<= x y)
                 (<= 0 c)
                 (rationalp x)
                 (rationalp y)
                 (rationalp c))
            (<= (* c x) (* c y)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm binomial-prime-product-central-upper-bound
  (implies (and (no-primes-between n (* 2 n))
                (natp n)
                (<= 3 n))
           (<= (binomial-prime-product n n (* 2 n))
               (* (expt (* 2 n) (small-prime-count (* 2 n) (* 2 n)))
                  (primorial (floor (* 2 n) 3)))))
  :hints (("Goal" :use ((:instance
                         binomial-prime-product-bound-by-central-product-bound
                         (k (* 2 n)))
                        (:instance central-product-bound-decomposition
                                   (k (* 2 n)))
                        (:instance medium-primes-product-when-big (k (* 2 n)))
                        (:instance medium-primes-product-bound
                                   (k (floor (* 2 n) 3)))
                        (:instance scale-left-central-binomial
                                   (c (expt (* 2 n)
                                            (small-prime-count (* 2 n)
                                                               (* 2 n))))
                                   (x (medium-primes-product
                                       n (floor (* 2 n) 3)))
                                   (y (primorial (floor (* 2 n) 3)))))
           :in-theory (disable
                       binomial-prime-product-bound-by-central-product-bound
                       central-product-bound-decomposition
                       medium-primes-product-when-big
                       medium-primes-product-bound
                       binomial-prime-product-when-<=))))

(defthm central-binomial-upper-bound
  (implies (and (no-primes-between n (* 2 n))
                (natp n)
                (<= 3 n))
           (<= (/ (dm::fact (* 2 n))
                  (* (dm::fact n) (dm::fact n)))
               (* (expt (* 2 n) (small-prime-count (* 2 n) (* 2 n)))
                  (primorial (floor (* 2 n) 3)))))
  :hints (("Goal" :use ((:instance binomial-prime-product-central-upper-bound)
                        (:instance binomial-prime-product-when-<=
                                   (a n)
                                   (b n)
                                   (k (* 2 n))))
           :in-theory (disable binomial-prime-product-central-upper-bound
                               binomial-prime-product-when-<=
                               (:definition dm::fact)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lower bound: 4^n <= 2n * (2n choose n), for n >= 1

(local
 (defthm scale-inequality-central-binomial
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
 (defthm central-binomial-lower-bound-mult
   (implies (posp n)
            (<= (* (power-of-4 n) (dm::fact n) (dm::fact n))
                (* 2 n (dm::fact (* 2 n)))))
   :hints (("Goal" :induct (dm::fact n)
            :in-theory (disable (:definition dm::fact)))
           ("Subgoal *1/2"
            :cases ((equal n 1) (< 1 n)))
           ("Subgoal *1/2.2" :expand ((dm::fact 1) (dm::fact 2) (power-of-4 1)))
           ("Subgoal *1/2.1"
            :expand ((dm::fact (* 2 n))
                     (dm::fact (+ -1 (* 2 n)))
                     (dm::fact n)
                     (power-of-4 n))
            :use ((:instance scale-inequality-central-binomial
                             (x (* (power-of-4 (+ -1 n))
                                   (dm::fact (+ -1 n))
                                   (dm::fact (+ -1 n))))
                             (y (* 2 (+ -1 n) (dm::fact (+ -2 (* 2 n)))))
                             (c (* 4 n n))
                             (d (* 2 n (+ -1 (* 2 n)) n (/ (+ -1 n))))))))))

(local
 (defthm posp-of-fact-central-binomial
   (posp (dm::fact n))
   :rule-classes :type-prescription))

(defthm central-binomial-lower-bound
  (implies (posp n)
           (<= (power-of-4 n)
               (* 2 n (/ (dm::fact (* 2 n))
                         (* (dm::fact n) (dm::fact n))))))
  :hints (("Goal" :use central-binomial-lower-bound-mult
           :in-theory (disable central-binomial-lower-bound-mult
                               (:definition dm::fact))
           :nonlinearp t)))
