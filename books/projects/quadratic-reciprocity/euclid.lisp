;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")
(include-book "xdoc/top" :dir :system)

(local (include-book "support/euclid"))

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(defsection number-theory
  :parents (acl2::arithmetic)
  :short "Quadratic Reciprocity Theorem and other facts from Number Theory")

(defsection euclid
  :parents (number-theory)
  :short "Definition of prime number and two theorems of Euclid"
  :long "<h3>Overview</h3>

This book contains proofs of two theorems of Euclid:
<ol>
  <li>There exist infinitely many primes.</li>
  <li>If @('p') is a prime divisor of @('a*b'), then @('p') divides either @('a') or @('b').</li>
 </ol>"

"We first list some basic properties of divisibility.
 @(def divides)
 @(thm divides-leq)
 @(thm divides-minus)
 @(thm divides-sum)
 @(thm divides-product)
 @(thm divides-transitive)
 @(thm divides-self)
 @(thm divides-0)
 @(thm divides-mod-equal)
 @(thm divides-mod-0)"

(defn divides (x y)
  (and (acl2-numberp x)
       (not (= x 0))
       (acl2-numberp y)
       (integerp (/ y x))))

(defthm divides-leq
    (implies (and (> x 0)
		  (> y 0)
		  (divides x y))
	     (<= x y))
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
  :rule-classes ())

(defthm divides-self
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (divides x x)))

(defthm divides-0
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (divides x 0)))

(defthm divides-mod-equal
    (implies (and (real/rationalp a)
		  (real/rationalp b)
                  (real/rationalp n)
                  (not (= n 0)))
	     (iff (divides n (- a b))
		  (= (mod a n) (mod b n))))
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

"Our definition of primality is based on the following function, which computes
 the least divisor of a natural number @('n') that is greater than or equal to @('k').
 (In the book @('mersenne'), in which we are concerned with efficiency, we shall
 introduce an equivalent version that checks for divisors only up to @('sqrt(n)').)
 @(def least-divisor)
 @(thm least-divisor-divides)
 @(thm least-divisor-is-least)
 @(def primep)
 @(thm primep-gt-1)
 @(thm primep-no-divisor)
 @(thm primep-least-divisor)"

(defn least-divisor (k n)
  (declare (xargs :measure (:? k n)))
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
  :rule-classes ())

(defthm primep-least-divisor
    (implies (and (integerp n)
		  (>= n 2))
	     (primep (least-divisor 2 n)))
  :rule-classes ())

(in-theory (disable primep))

"Our formulation of the infinitude of the set of primes is based on a function that
 returns a prime that is greater than its argument:
 @(def fact)
 @(def greater-prime)
 @(thm greater-prime-divides)
 @(thm divides-fact)
 @(thm not-divides-fact-plus1)
 @(thm infinitude-of-primes)"

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
  :rule-classes ())

(defthm divides-fact
    (implies (and (integerp n)
		  (integerp k)
		  (<= 1 k)
		  (<= k n))
	     (divides k (fact n))))

(defthm not-divides-fact-plus1
    (implies (and (integerp n)
		  (integerp k)
		  (< 1 k)
		  (<= k n))
	     (not (divides k (1+ (fact n)))))
  :rule-classes ())

(defthm infinitude-of-primes
    (implies (integerp n)
	     (and (primep (greater-prime n))
		  (> (greater-prime n) n)))
  :rule-classes ())

"Our main theorem of Euclid depends on the properties of the greatest common divisor,
 which we define according to Euclid's algorithm.
 @(def g-c-d-nat)
 @(def g-c-d)
 @(thm g-c-d-nat-pos)
 @(thm g-c-d-pos)
 @(thm divides-g-c-d-nat)
 @(thm g-c-d-divides)"

(defun g-c-d-nat (x y)
  (declare (xargs :guard (and (natp x)
                              (natp y))
                  :measure (:? x y)))
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
  :rule-classes ())

(defthm divides-g-c-d-nat
    (implies (and (natp x)
		  (natp y))
	     (and (or (= x 0) (divides (g-c-d-nat x y) x))
		  (or (= y 0) (divides (g-c-d-nat x y) y))))
  :rule-classes ())

(defthm g-c-d-divides
    (implies (and (integerp x)
		  (integerp y))
	     (and (or (= x 0) (divides (g-c-d x y) x))
		  (or (= y 0) (divides (g-c-d x y) y))))
  :rule-classes ())

"It remains to be shown that the gcd of @('x') and @('y') is divisible by any common
 divisor of @('x') and @('y').  This depends on the observation that the gcd may be
 expressed as a linear combination @({r*x + s*y}).  We construct the coefficients @('r')
 and @('s') explicitly.
 @(def r-nat)
 @(def s-nat)
 @(thm r-s-nat)
 @(def r-int)
 @(def s-int)
 @(thm g-c-d-linear-combination)
 @(thm divides-g-c-d)
 @(thm g-c-d-prime)"

(mutual-recursion

 (defun r-nat (x y)
   (declare (xargs :guard (and (natp x)
                               (natp y))
                   :measure (:? x y)))
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
                   :measure (:? x y)))
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
These type-prescription rules are redundant.
ACL2 derives them from definitions.

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
  :rule-classes ())

(in-theory (disable g-c-d r-int s-int))

(defthm divides-g-c-d
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (not (= d 0))
		  (divides d x)
		  (divides d y))
	     (divides d (g-c-d x y))))

(defthm g-c-d-prime
    (implies (and (primep p)
		  (integerp a)
		  (not (divides p a)))
	     (= (g-c-d p a) 1))
  :rule-classes ())

"The main theorem:
 @(thm euclid)"

(defthm euclid
    (implies (and (primep p)
		  (integerp a)
		  (integerp b)
		  (not (divides p a))
		  (not (divides p b)))
	     (not (divides p (* a b))))
  :rule-classes ())

)
