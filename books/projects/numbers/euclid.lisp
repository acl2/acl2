;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")
(include-book "xdoc/top" :dir :system)

(local (include-book "support/euclid"))
(local (include-book "support/fta"))
(local (include-book "support/crt"))

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

(defun least-prime-divisor (n)
  (declare (xargs :guard t))
  (least-divisor 2 n))

(defthm primep-least-prime-divisor
    (implies (and (integerp n)
		  (>= n 2))
	     (primep (least-prime-divisor n)))
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
  (least-prime-divisor (1+ (fact n))))

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
 @(def gcd-nat)
 @(def gcd)
 @(thm gcd-nat-pos)
 @(thm gcd-pos)
 @(thm divides-gcd-nat)
 @(thm gcd-divides)"

(defun gcd-nat (x y)
  (declare (xargs :guard (and (natp x)
                              (natp y))
                  :measure (:? x y)))
  (if (zp x)
      y
    (if (zp y)
	x
      (if (<= x y)
	  (gcd-nat x (- y x))
	(gcd-nat (- x y) y)))))

(defun gcd (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (gcd-nat (abs x) (abs y)))

(defthm gcd-nat-pos
    (implies (and (natp x)
		  (natp y)
		  (not (and (= x 0) (= y 0))))
	     (> (gcd-nat x y) 0))
  :rule-classes ())

(defthmd gcd-commutative
  (implies (and (integerp x) (integerp y))
           (equal (gcd x y) (gcd y x))))

(defthm gcd-pos
    (implies (and (integerp x)
		  (integerp y)
		  (not (and (= x 0) (= y 0))))
	     (and (integerp (gcd x y))
		  (> (gcd x y) 0)))
  :rule-classes ())

(defthm divides-gcd-nat
    (implies (and (natp x)
		  (natp y))
	     (and (or (= x 0) (divides (gcd-nat x y) x))
		  (or (= y 0) (divides (gcd-nat x y) y))))
  :rule-classes ())

(defthm gcd-divides
    (implies (and (integerp x)
		  (integerp y))
	     (and (or (= x 0) (divides (gcd x y) x))
		  (or (= y 0) (divides (gcd x y) y))))
    :rule-classes ())

;; The numerator and denominator of a rational number are relatively prime:

(defthmd gcd-num-den
  (implies (and (rationalp x) (not (= x 0)))
           (equal (gcd (numerator x) (denominator x))
	          1)))

;; The representation of a rational in lowest terms is unique:

(defthm lowest-terms-unique
  (implies (and (posp n) (posp d) (equal (gcd n d) 1)
                (posp p) (posp q) (equal (gcd p q) 1)
                (equal (/ p q) (/ n d)))
           (and (equal n p) (equal d q)))
  :rule-classes ())

"It remains to be shown that the gcd of @('x') and @('y') is divisible by any common
 divisor of @('x') and @('y').  This depends on the observation that the gcd may be
 expressed as a linear combination @({r*x + s*y}).  We construct the coefficients @('r')
 and @('s') explicitly.
 @(def r-nat)
 @(def s-nat)
 @(thm r-s-nat)
 @(def r)
 @(def s)
 @(thm gcd-linear-combination)
 @(thm divides-gcd)
 @(thm gcd-prime)"

;; We do this first for natural numbers x and y, and then extend the definition to integers:

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
		(gcd-nat x y)))
  :rule-classes ())

(defun r (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (if (< x 0)
      (- (r-nat (abs x) (abs y)))
    (r-nat (abs x) (abs y))))

(defun s (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (if (< y 0)
      (- (s-nat (abs x) (abs y)))
    (s-nat (abs x) (abs y))))

(defthm gcd-linear-combination
    (implies (and (integerp x)
		  (integerp y))
	     (= (+ (* (r x y) x)
		   (* (s x y) y))
		(gcd x y)))
  :rule-classes ())

(in-theory (disable gcd r s))

(defthm divides-gcd
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (not (= d 0))
		  (divides d x)
		  (divides d y))
	     (divides d (gcd x y))))

(defthmd rel-prime-no-common-factor
  (implies (and (integerp x)
                (integerp y)
		(integerp d)
		(> d 1)
		(divides d x)
		(= (gcd x y) 1))
	   (not (divides d y))))

(defthmd gcd-prime
    (implies (and (primep p)
		  (integerp a))
	     (equal (gcd p a)
		    (if (divides p a)
			p
		      1))))

(defthmd gcd-quotient-1
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(posp d)
		(divides d x)
		(= (gcd x y) 1))
	   (equal (gcd (/ x d) y) 1)))

(defthmd gcd-quotient-2
  (implies (and (integerp x)
                (integerp y)
		(posp d)
		(divides d x)
		(divides d y))
	   (equal (gcd (/ x d) (/ y d))
	          (/ (gcd x y) d))))

(defthmd gcd-divisor
  (implies (and (integerp x) (integerp y)                
                (integerp d) (not (= d 0))
		(divides d y)
		(= (gcd x y) 1))
	   (equal (gcd x d) 1)))

(defthmd gcd-divisor-2
  (implies (and (integerp x) (integerp y)                
                (integerp c) (not (= c 0))
                (integerp d) (not (= d 0))
		(divides c x)
		(divides d y)
		(= (gcd x y) 1))
	   (equal (gcd c d) 1)))

;; If x and y are not relatively prime, then they have a common prime divisor:

(defund cpd (x y)
  (least-prime-divisor (gcd x y)))

(defthmd cpd-divides
  (implies (and (integerp x) (not (= x 0))
                (integerp y) (not (= y 0))
		(not (= (gcd x y) 1)))
	   (and (primep (cpd x y))
	        (divides (cpd x y) x)
	        (divides (cpd x y) y))))

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

;; The following results are all consequences of euclid.

;; If x is relatively prime to both y and z, then x is relatively prime to (* y z).

(defthmd rel-prime-prod
  (implies (and (integerp x) (not (= x 0))
		(integerp y) (not (= y 0))
		(integerp z) (not (= z 0))
		(= (gcd x y) 1)
		(= (gcd x z) 1))
	   (equal (gcd x (* y z)) 1)))

;; If d divides mn and (gcd d m) = 1, then d divides n.
;; The proof is by induction on d.  The claim is trivial for d = 1.
;; Let p be a prime divisor of d.  Then p does not divide m ,and therefore d divides n.
;; By induction, since d/p divides m(n/p), d/p divides n/p, which implies d divides n.

(defthmd divides-product-divides-factor
  (implies (and (integerp m) (not (= m 0))
		(integerp n) (not (= n 0))
		(integerp d) (not (= d 0))
		(divides d (* m n))
		(= (gcd d m) 1))
	   (divides d n)))

;; If relatively prime integers x and y both divde m, then so does xy.
;; The proof is by induction on x.  The claim is trivial for x = 1.
;; Let p be a prime divisor of x. Then p does not divide y, but since p divides m = (m/y)* y, p divides m/y
;; which implies that y divides m/p.  Thus, m/p is divisible by both x/p and y.  By induction, xy/p
;; divides m/p, and therefore xy divides m.

(defthmd product-rel-prime-divides
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0))
		(= (gcd x y) 1)
		(integerp m)
		(divides x m)
		(divides y m))
	   (divides (* x y) m)))

;; The last result allows us to define the least common multiple as follows:

(defund lcm (x y)
  (/ (* x y) (gcd x y)))

(defthmd integerp-lcm-int
  (implies (and (integerp x) (not (= x 0))
                (integerp y) (not (= y 0)))
           (and (integerp (lcm x y))
	        (not (equal (lcm x y) 0)))))

(defthmd posp-lcm
  (implies (and (posp x)
                (posp y))
           (posp (lcm x y))))

(defthmd lcm-is-common-multiple
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0)))
	   (and (divides x (lcm x y))
	        (divides y (lcm x y)))))

;; product-rel-prime-divides is needed to prove the critical property of lcm that it divides any common multiple
;; of its arguments: Suppose x and y both divide m and let g = (gcd x y), a = x/g, b = y/g, and l = (lcm x y).  Then
;;    m/l = mg/xy = m/gab.
;; Since a and b both divide m/g, ab divides m/g, i.e., m/gab is an integer and l divides m.

(defthmd lcm-is-least
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0))
		(integerp m))
           (iff (and (divides x m)
		     (divides y m))
	        (divides (lcm x y) m))))

;; Every positive integer is a product of powers of distinct primes.
;; This is the existence part of the Fundamental Theorem of Arithmetic:

(defun prime-pow-list-p (l)
  (if (consp l)
      (and (primep (caar l))
	   (posp (cdar l))
	   (prime-pow-list-p (cdr l))
	   (or (null (cdr l)) (< (caar l) (caadr l))))
    (null l)))

(defun pow-prod (l)
  (if (consp l)
      (* (expt (caar l) (cdar l))
	 (pow-prod (cdr l)))
    1))
(defun prime-fact (n)
  (if (and (natp n) (> n 1))
      (let* ((p (least-prime-divisor n))
   	     (l (prime-fact (/ n p))))
	(if (and (consp l) (equal (caar l) p))
	    (cons (cons p (1+ (cdar l))) (cdr l))
	  (cons (cons p 1) l)))
    ()))

(defthmd caar-prime-fact
  (implies (and (natp n) (> n 1))
	   (equal (caar (prime-fact n))
		  (least-prime-divisor n))))

(defthmd caar-prime-pow-list
  (implies (and (prime-pow-list-p l) (consp l))
           (equal (caar l) (least-prime-divisor (pow-prod l)))))

(defthmd rel-prime-pow-list
  (implies (and (prime-pow-list-p l) (>= (len l) 2))
	   (equal (gcd (expt (caar l) (cdar l))
		       (pow-prod (cdr l)))
		  1)))

(defthmd prime-fact-existence
  (implies (posp n)
	   (let ((l (prime-fact n)))
	     (and (prime-pow-list-p l)
		  (equal (pow-prod l) n)))))

;; Uniqueness part of the Fundamental Theorem of Arithmetic:

(defthmd prime-fact-uniqueness
  (implies (and (posp n)
		(prime-pow-list-p l)
		(equal (pow-prod l) n))
	   (equal (prime-fact n) l)))

;; Chinese Remainder Theorem:

(defun rel-prime-all (x l)
  (if (consp l)
      (and (equal (gcd x (car l)) 1)
	   (rel-prime-all x (cdr l)))
    t))

(defun rel-prime-moduli (l)
  (if (consp l)
      (and (integerp (car l))
	   (>= (car l) 2)
	   (rel-prime-all (car l) (cdr l))
	   (rel-prime-moduli (cdr l)))
    (null l)))

(defun congruent-all (x a m)
  (declare (xargs :measure (acl2-count m)))
  (if (consp m)
      (and (equal (mod x (car m)) (mod (car a) (car m)))
	   (congruent-all x (cdr a) (cdr m)))
    t))

(defun int-list-p (l)
  (if (consp l)
      (and (integerp (car l))
	   (int-list-p (cdr l)))
    t))

(defun prod-list (l)
  (if (consp l)
      (* (car l) (prod-list (cdr l)))
    1))

(defund one-mod (x l) (* (s x (prod-list l)) (prod-list l)))

(defun crt1 (a m l)
  (if (consp a)
      (+ (* (car a) (one-mod (car m) (remove1-equal (car m) l)))
         (crt1 (cdr a) (cdr m) l))
    0))

(defund crt (a m) (crt1 a m m))

(defthmd chinese-remainder-theorem
    (implies (and (int-list-p a)
		  (rel-prime-moduli m)
		  (= (len a) (len m)))
	     (and (integerp (crt a m))
		  (congruent-all (crt a m) a m))))
)
