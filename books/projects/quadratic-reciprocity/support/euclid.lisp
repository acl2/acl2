(in-package "RTL")

;; This book contains proofs of two theorems of Euclid:

;;   (1) There exist infinitely many primes.

;;   (2) If p is a prime divisor of a*b, then p divides either a or b.

(include-book "std/util/defrule" :dir :system)

(include-book "rtl/rel11/support/basic" :dir :system) ;; Properties of fl and mod
(include-book "rtl/rel11/support/util" :dir :system)  ;; Utility macros
(local (include-book "arithmetic-5/top" :dir :system)) ;; It's hard to do any arithmetic without something like this

;; We first list some basic properties of divisibility.

(defn divides (x y)
  (and (acl2-numberp x)
       (not (= x 0))
       (acl2-numberp y)
       (integerp (/ y x))))

(defrule divides-leq
    (implies (and (> x 0)
		  (> y 0)
		  (divides x y))
	     (<= x y))
    :prep-lemmas (
       (defrule lemma0
         (implies (and (acl2-numberp x)
                       (> x 0)
                       (real/rationalp n)
                       (<= 0 n)
                       )
                  (<= 0 (* x n)))
         :rule-classes ())
       (defrule lemma1
         (implies (and (acl2-numberp x)
                       (> x 0)
                       (integerp n)
                       (> (* x n) 0))
                  (<= x (* x n)))
         :use (:instance lemma0 (n (1- n)))))
  :use (:instance lemma1 (n (/ y x)))
  :rule-classes ())

(defthm divides-minus
  (implies (divides x y)
           (divides x (- y)))
  :rule-classes ())

(defthm divides-sum
    (implies (and (divides x y)
		  (divides x z))
	     (divides x (+ y z)))
  :rule-classes ())

(defthm divides-product
    (implies (and (integerp z)
		  (divides x y))
	     (divides x (* y z)))
  :rule-classes ())

(defthm divides-transitive
    (implies (and (divides x y)
		  (divides y z))
	     (divides x z))
  :rule-classes ()
  :hints (("Goal" :use ((:instance divides-product (z (/ z y)))))))

(defthm divides-self
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (divides x x)))

(defthm divides-0
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (divides x 0)))

(defrule divides-mod-equal
    (implies (and (real/rationalp a)
		  (real/rationalp b)
                  (real/rationalp n)
                  (not (= n 0)))
	     (iff (divides n (- a b))
		  (= (mod a n) (mod b n))))
  :use (mod-equal-int mod-equal-int-reverse)
  :rule-classes ())

(defthm divides-mod-0
    (implies (and (acl2-numberp a)
		  (acl2-numberp n)
		  (not (= n 0)))
	     (iff (divides n a)
		  (= (mod a n) 0)))
  :rule-classes ()
  :hints (("Goal" :use (:instance divides-mod-equal (b 0)))))

(in-theory (disable divides))

;; Our definition of primality is based on the following function, which computes
;; the least divisor of a natural number n that is greater than or equal to k.
;; (In the book "mersenne", in which we are concerned with efficiency, we shall
;; introduce an equivalent version that checks for divisors only up to sqrt(n).)

(defn least-divisor (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (integerp n)
	   (integerp k)
	   (< 1 k)
	   (<= k n))
      (if (divides k n)
	  k
	(least-divisor (1+ k) n))
    ()))

(defthm least-divisor-divides
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n))
	     (and (integerp (least-divisor k n))
		  (divides (least-divisor k n) n)
		  (<= k (least-divisor k n))
		  (<= (least-divisor k n) n)))
  :rule-classes ())

(defthm least-divisor-is-least
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n)
		  (integerp d)
		  (divides d n)
		  (<= k d))
	     (<= (least-divisor k n) d))
  :rule-classes ())

(defn primep (n)
  (and (integerp n)
       (>= n 2)
       (equal (least-divisor 2 n) n)))

(defthm primep-gt-1
    (implies (primep p)
	     (and (integerp p)
		  (>= p 2)))
  :rule-classes :forward-chaining)

(defthm primep-no-divisor
    (implies (and (primep p)
		  (integerp d)
		  (divides d p)
		  (> d 1))
	     (= d p))
  :rule-classes ()
  :hints (("Goal" :use ((:instance least-divisor-is-least (n p) (k 2))
			(:instance divides-leq (x d) (y p))))))

(defthm primep-least-divisor
    (implies (and (integerp n)
		  (>= n 2))
	     (primep (least-divisor 2 n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance least-divisor-divides (k 2))
			(:instance least-divisor-divides (k 2) (n (least-divisor 2 n)))
			(:instance divides-transitive
				   (x (least-divisor 2 (least-divisor 2 n)))
				   (y (least-divisor 2 n))
				   (z n))
			(:instance least-divisor-is-least
				   (d (least-divisor 2 (least-divisor 2 n)))
				   (k 2))))))

(in-theory (disable primep))

;; Our formulation of the infinitude of the set of primes is based on a function that
;; returns a prime that is greater than its argument:

(defun fact (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (fact (1- n)))))

(defun greater-prime (n)
  (declare (xargs :guard (natp n)))
  (least-divisor 2 (1+ (fact n))))

(defthm greater-prime-divides
    (divides (greater-prime n) (1+ (fact n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance primep-least-divisor (n (1+ (fact n))))
			(:instance least-divisor-divides (k 2) (n (1+ (fact n))))))))

(defthm divides-fact
    (implies (and (integerp n)
		  (integerp k)
		  (<= 1 k)
		  (<= k n))
	     (divides k (fact n)))
  :hints (("Subgoal *1/4" :use ((:instance divides-product (x k) (y (fact (1- n))) (z n))))
	  ("Subgoal *1/3" :use ((:instance divides-product (x k) (y k) (z (fact (1- k))))))))

(defthm not-divides-fact-plus1
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n))
	     (not (divides k (1+ (fact n)))))
  :rule-classes ()
  :hints (("Goal" :use (divides-fact
			(:instance divides-leq (x k) (y 1))
			(:instance divides-sum (x k) (y (- (fact n))) (z (1+ (fact n))))
			(:instance divides-product (x k) (y (fact n)) (z -1))))))

(defthm infinitude-of-primes
    (implies (integerp n)
	     (and (primep (greater-prime n))
		  (> (greater-prime n) n)))
  :rule-classes ()
  :hints (("Goal" :use (greater-prime-divides
			(:instance primep-least-divisor (n (1+ (fact n))))
			(:instance not-divides-fact-plus1 (k (greater-prime n)))))))

;; Our main theorem of Euclid depends on the properties of the greatest common divisor,
;; which we define according to Euclid's algorithm.

(defun g-c-d-nat (x y)
  (declare (xargs :guard (and (natp x)
                              (natp y))
                  :measure (nfix (+ x y))))
  (if (zp x)
      y
    (if (zp y)
	x
      (if (<= x y)
	  (g-c-d-nat x (- y x))
	(g-c-d-nat (- x y) y)))))

(defun g-c-d (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (g-c-d-nat (abs x) (abs y)))

(defthm g-c-d-nat-pos
    (implies (and (natp x)
		  (natp y)
		  (not (and (= x 0) (= y 0))))
	     (> (g-c-d-nat x y) 0))
  :rule-classes ())

(defthm g-c-d-pos
    (implies (and (integerp x)
		  (integerp y)
		  (not (and (= x 0) (= y 0))))
	     (and (integerp (g-c-d x y))
		  (> (g-c-d x y) 0)))
  :rule-classes ()
  :hints (("Goal" :use (:instance g-c-d-nat-pos (x (abs x)) (y (abs y))))))

(defthm divides-g-c-d-nat
    (implies (and (natp x)
		  (natp y))
	     (and (or (= x 0) (divides (g-c-d-nat x y) x))
		  (or (= y 0) (divides (g-c-d-nat x y) y))))
  :rule-classes ()
  :hints (("Goal" :induct (g-c-d-nat x y))
	  ("Subgoal *1/4" :use (:instance divides-sum (x (g-c-d-nat (- x y) y)) (z (- x y))))
	  ("Subgoal *1/3" :use (:instance divides-sum (x (g-c-d-nat x (- y x) )) (y x) (z (- y x))))))

(defthm g-c-d-divides
    (implies (and (integerp x)
		  (integerp y))
	     (and (or (= x 0) (divides (g-c-d x y) x))
		  (or (= y 0) (divides (g-c-d x y) y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance divides-g-c-d-nat (x (abs x)) (y (abs y)))
			(:instance divides-product (x (g-c-d-nat (abs x) (abs y))) (y (abs x)) (z -1))
			(:instance divides-product (x (g-c-d-nat (abs x) (abs y))) (y (abs y)) (z -1))))))

;; It remains to be shown that the gcd of x and y is divisible by any common
;; divisor of x and y.  This depends on the observation that the gcd may be
;; expressed as a linear combination r*x + s*y.  We construct the coefficients r
;; and s explicitly.

(mutual-recursion

 (defun r-nat (x y)
   (declare (xargs :guard (and (natp x)
                               (natp y))
                   :measure (nfix (+ x y))))
  (if (zp x)
      0
    (if (zp y)
	1
      (if (<= x y)
	  (- (r-nat x (- y x)) (s-nat x (- y x)))
	(r-nat (- x y) y)))))

 (defun s-nat (x y)
   (declare (xargs :guard (and (natp x)
                               (natp y))
                   :measure (nfix (+ x y))))
  (if (zp x)
      1
    (if (zp y)
	0
      (if (<= x y)
	  (s-nat x (- y x))
	(- (s-nat (- x y) y) (r-nat (- x y) y))))))

)

(defthm r-s-nat
    (implies (and (natp x)
		  (natp y))
	     (= (+ (* (r-nat x y) x)
		   (* (s-nat x y) y))
		(g-c-d-nat x y)))
  :rule-classes ())

(defun r-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (if (< x 0)
      (- (r-nat (abs x) (abs y)))
    (r-nat (abs x) (abs y))))

(defun s-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (if (< y 0)
      (- (s-nat (abs x) (abs y)))
    (s-nat (abs x) (abs y))))
#|
(defthm integerp-r-int
    (integerp (r-int x y))
  :rule-classes (:type-prescription))

(defthm integerp-s-int
    (integerp (s-int x y))
  :rule-classes (:type-prescription))
|#
(defthm g-c-d-linear-combination
    (implies (and (integerp x)
		  (integerp y))
	     (= (+ (* (r-int x y) x)
		   (* (s-int x y) y))
		(g-c-d x y)))
  :rule-classes ()
  :hints (("Goal" :use (:instance r-s-nat (x (abs x)) (y (abs y))))))

(in-theory (disable g-c-d r-int s-int))

(defthm divides-g-c-d
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (not (= d 0))
		  (divides d x)
		  (divides d y))
	     (divides d (g-c-d x y)))
  :hints (("Goal" :use (g-c-d-linear-combination
			(:instance divides-sum (x d) (y (* (r-int x y) x)) (z (* (s-int x y) y)))
			(:instance divides-product (x d) (y x) (z (r-int x y)))
			(:instance divides-product (x d) (z (s-int x y)))))))

(defthm g-c-d-prime
    (implies (and (primep p)
		  (integerp a)
		  (not (divides p a)))
	     (= (g-c-d p a) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance g-c-d-divides (x p) (y a))
			(:instance g-c-d-pos (x p) (y a))
			(:instance primep-no-divisor (d (g-c-d p a)))))))

(local-defthm hack
  (implies (and (primep p)
                (integerp a)
                (integerp b)
                (= (+ (* a (s-int p a)) (* p (r-int p a))) 1))
           (equal (+ (* a b (s-int p a)) (* b p (r-int p a)))
                  b)))

;; the main theorem:

(defthm euclid
    (implies (and (primep p)
		  (integerp a)
		  (integerp b)
		  (not (divides p a))
		  (not (divides p b)))
	     (not (divides p (* a b))))
  :rule-classes ()
  :hints (("Goal" :use (g-c-d-prime
			(:instance g-c-d-linear-combination (x p) (y a))
			(:instance divides-sum (x p) (y (* (r-int p a) p b)) (z (* (s-int p a) a b)))
			(:instance divides-product (x p) (y (* a b)) (z (s-int p a)))
			(:instance divides-product (x p) (y p) (z (* b (r-int p a))))))))

