(in-package "DM")

;; This book contains proofs of two theorems of Euclid:

;;   (1) There exist infinitely many primes.

;;   (2) If p is a prime divisor of a*b, then p divides either a or b.

(include-book "std/util/defrule" :dir :system)
(include-book "../portcullis")

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
  :use (rtl::mod-equal-int rtl::mod-equal-int-reverse)
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

(defun least-prime-divisor (n)
  (declare (xargs :guard t))
  (least-divisor 2 n))

(defthm primep-least-prime-divisor
    (implies (and (integerp n)
		  (>= n 2))
	     (primep (least-prime-divisor n)))
  :rule-classes ()
  :hints (("Goal" :use (primep-least-divisor))))

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
  (least-prime-divisor (1+ (fact n))))

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

(defun gcd-nat (x y)
  (declare (xargs :guard (and (natp x)
                              (natp y))
                  :measure (nfix (+ x y))))
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

(defthm gcd-pos
    (implies (and (integerp x)
		  (integerp y)
		  (not (and (= x 0) (= y 0))))
	     (and (integerp (gcd x y))
		  (> (gcd x y) 0)))
  :rule-classes ()
  :hints (("Goal" :use (:instance gcd-nat-pos (x (abs x)) (y (abs y))))))

(local-defthmd gcd-nat-commutative
  (implies (and (natp x) (natp y))
           (equal (gcd-nat x y) (gcd-nat y x))))

(defthmd gcd-commutative
  (implies (and (integerp x) (integerp y))
           (equal (gcd x y) (gcd y x)))
  :hints (("Goal" :in-theory (enable gcd)
                  :use ((:instance gcd-nat-commutative (x (abs x)) (y (abs y)))))))

(defthm divides-gcd-nat
    (implies (and (natp x)
		  (natp y))
	     (and (or (= x 0) (divides (gcd-nat x y) x))
		  (or (= y 0) (divides (gcd-nat x y) y))))
  :rule-classes ()
  :hints (("Goal" :induct (gcd-nat x y))
	  ("Subgoal *1/4" :use (:instance divides-sum (x (gcd-nat (- x y) y)) (z (- x y))))
	  ("Subgoal *1/3" :use (:instance divides-sum (x (gcd-nat x (- y x) )) (y x) (z (- y x))))))

(defthm gcd-divides
    (implies (and (integerp x)
		  (integerp y))
	     (and (or (= x 0) (divides (gcd x y) x))
		  (or (= y 0) (divides (gcd x y) y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance divides-gcd-nat (x (abs x)) (y (abs y)))
			(:instance divides-product (x (gcd-nat (abs x) (abs y))) (y (abs x)) (z -1))
			(:instance divides-product (x (gcd-nat (abs x) (abs y))) (y (abs y)) (z -1))))))

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
#|
(defthm integerp-r
    (integerp (r x y))
  :rule-classes (:type-prescription))

(defthm integerp-s
    (integerp (s x y))
  :rule-classes (:type-prescription))
|#
(defthm gcd-linear-combination
    (implies (and (integerp x)
		  (integerp y))
	     (= (+ (* (r x y) x)
		   (* (s x y) y))
		(gcd x y)))
  :rule-classes ()
  :hints (("Goal" :use (:instance r-s-nat (x (abs x)) (y (abs y))))))

(in-theory (disable gcd r s))

(defthm divides-gcd
    (implies (and (integerp x)
		  (integerp y)
		  (integerp d)
		  (not (= d 0))
		  (divides d x)
		  (divides d y))
	     (divides d (gcd x y)))
  :hints (("Goal" :use (gcd-linear-combination
			(:instance divides-sum (x d) (y (* (r x y) x)) (z (* (s x y) y)))
			(:instance divides-product (x d) (y x) (z (r x y)))
			(:instance divides-product (x d) (z (s x y)))))))

(defthmd rel-prime-no-common-factor
  (implies (and (integerp x)
                (integerp y)
		(integerp d)
		(> d 1)
		(divides d x)
		(= (gcd x y) 1))
	   (not (divides d y)))
  :hints (("Goal" :in-theory (enable divides) :use (divides-gcd))))

(defthmd gcd-quotient-1
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(posp d)
		(divides d x)
		(= (gcd x y) 1))
	   (equal (gcd (/ x d) y) 1))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance gcd-divides (x (/ x d)))
		        (:instance gcd-pos (x (/ x d)))
			(:instance divides-product (x (gcd (/ x d) y)) (y (/ x d)) (z d))
			(:instance divides-gcd (d (gcd (/ x d) y)))))))

(local-defthmd gcd-nat-quotient-2
  (implies (and (natp x)
                (natp y)
		(posp d)
		(divides d x)
		(divides d y))
	   (equal (gcd-nat (/ x d) (/ y d))
	          (/ (gcd-nat x y) d)))
  :hints (("Goal" :induct (gcd-nat x y))
          ("Subgoal *1/4" :in-theory (enable divides)
	                  :use ((:instance divides-minus (x d))
	                        (:instance divides-sum (x d) (y x) (z (- y)))))
          ("Subgoal *1/3" :in-theory (enable divides)
	                  :use ((:instance divides-minus (x d) (y x))
	                        (:instance divides-sum (x d) (z (- x)))))
	  ("Subgoal *1/2" :in-theory (enable divides))))

(defthmd gcd-quotient-2
  (implies (and (integerp x)
                (integerp y)
		(posp d)
		(divides d x)
		(divides d y))
	   (equal (gcd (/ x d) (/ y d))
	          (/ (gcd x y) d)))
  :hints (("Goal" :in-theory (enable divides gcd)
	   :use ((:instance gcd-nat-quotient-2 (x (abs x)) (y (abs y)))))))

(local-defthm gcd-prime-1
  (implies (and (primep p)
                (integerp a)
	        (divides p a))
	   (= (gcd p a) p))
  :rule-classes ()
  :hints (("Goal" :expand ((gcd p 0))
	          :in-theory (enable divides)
	          :use ((:instance gcd-quotient-2 (x a) (y p) (d p))
		        (:instance gcd-pos (x (/ a p)) (y 1))
			(:instance divides-leq (x (gcd a p)) (y 1))
			(:instance gcd-commutative (x a) (y p))
                        (:instance gcd-divides (x (/ a p)) (y 1))))))

(local-defthm gcd-prime-2
    (implies (and (primep p)
		  (integerp a)
		  (not (divides p a)))
	     (= (gcd p a) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance gcd-divides (x p) (y a))
			(:instance gcd-pos (x p) (y a))
			(:instance primep-no-divisor (d (gcd p a)))))))

(defthmd gcd-prime
    (implies (and (primep p)
		  (integerp a))
	     (equal (gcd p a)
		    (if (divides p a)
			p
		      1)))
  :hints (("Goal" :use (gcd-prime-1 gcd-prime-2))))



(local-defthm hack
  (implies (and (primep p)
                (integerp a)
                (integerp b)
                (= (+ (* a (s p a)) (* p (r p a))) 1))
           (equal (+ (* a b (s p a)) (* b p (r p a)))
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
  :hints (("Goal" :use (gcd-prime
			(:instance gcd-linear-combination (x p) (y a))
			(:instance divides-sum (x p) (y (* (r p a) p b)) (z (* (s p a) a b)))
			(:instance divides-product (x p) (y (* a b)) (z (s p a)))
			(:instance divides-product (x p) (y p) (z (* b (r p a))))))))

;; 1st corollary of euclid: If d divides mn and (gcd d m) = 1, then d divides n.
;; The proof is by induction on d.  The claim is trivial for d = 1.
;; Let p be a prime divisor of d.  Then p does not divide m ,and therefore d divides n.
;; By induction, since d/p divides m(n/p), d/p divides n/p, which implies d divides n.

(defun divides-product-divides-factor-induct (d n)
  (declare (xargs :measure (nfix (abs d))
                  :hints (("Goal" :use ((:instance primep-gt-1 (p (least-prime-divisor (abs d))))
		                        (:instance primep-least-divisor (n (abs d))))))))
  (if (or (not (integerp d)) (= d 0) (= d 1) (= d -1))
      (list d n)
    (let ((p (least-prime-divisor (abs d))))
      (divides-product-divides-factor-induct (/ d p) (/ n p)))))

(defthmd divides-product-divides-factor
  (implies (and (integerp m) (not (= m 0))
		(integerp n) (not (= n 0))
		(integerp d) (not (= d 0))
		(divides d (* m n))
		(= (gcd d m) 1))
	   (divides d n))
  :hints (("Goal" :induct (divides-product-divides-factor-induct d n))
          ("Subgoal *1/2" :in-theory (enable divides)
	                  :use ((:instance primep-gt-1 (p (least-prime-divisor (abs d))))
		                (:instance primep-least-divisor (n (abs d)))
			        (:instance least-divisor-divides (k 2) (n (abs d)))
			        (:instance gcd-quotient-1 (d (least-prime-divisor (abs d))) (x d) (y m))
			        (:instance rel-prime-no-common-factor (d (least-prime-divisor (abs d))) (x d) (y m))
			        (:instance euclid (p (least-prime-divisor (abs d))) (a m) (b n))
			        (:instance divides-transitive (x (least-prime-divisor (abs d))) (y d) (z (* m n)))))
	  ("Subgoal *1/1" :in-theory (enable divides))))

;; 2nd corollary of euclid: If relatively prime integers x and y both divde m, then so does xy.
;; The proof is by induction on x.  The claim is trivial for x = 1.
;; Let p be a prime divisor of x. Then p does not divide y, but since p divides m = (m/y)* y, p divides m/y
;; which implies that y divides m/p.  Thus, m/p is divisible by both x/p and y.  By induction, xy/p
;; divides m/p, and therefore xy divides m.

(defun product-rel-prime-divides-induct (x m)
  (declare (xargs :measure (nfix (abs x))
                  :hints (("Goal" :use ((:instance primep-gt-1 (p (least-prime-divisor (abs x))))
		                        (:instance primep-least-divisor (n (abs x))))))))
  (if (or (not (integerp x)) (= x 0) (= x 1) (= x -1))
      x
    (let ((p (least-prime-divisor (abs x))))
      (list m (product-rel-prime-divides-induct (/ x p) (/ m p))))))

(defthmd product-rel-prime-divides
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0))
		(= (gcd x y) 1)
		(integerp m)
		(divides x m)
		(divides y m))
	   (divides (* x y) m))
  :hints (("Goal" :induct (product-rel-prime-divides-induct x m))
          ("Subgoal *1/2" :in-theory (enable divides)
	                  :use ((:instance primep-gt-1 (p (least-prime-divisor (abs x))))
		                (:instance primep-least-divisor (n (abs x)))
				(:instance least-divisor-divides (k 2) (n (abs x)))
				(:instance gcd-quotient-1 (d (least-prime-divisor (abs x))))
				(:instance rel-prime-no-common-factor (d (least-prime-divisor (abs x))))
				(:instance euclid (p (least-prime-divisor (abs x))) (a (/ m y)) (b y))
				(:instance divides-transitive (x (least-prime-divisor (abs x))) (y x) (z m))))
	  ("Subgoal *1/1" :in-theory (enable divides))))

;; The last result allows us to define the least common multiple as follows:

(defund lcm (x y)
  (/ (* x y) (gcd x y)))

(defthmd integerp-lcm-int
  (implies (and (integerp x) (not (= x 0))
                (integerp y) (not (= y 0)))
           (and (integerp (lcm x y))
	        (not (equal (lcm x y) 0))))
  :hints (("Goal" :in-theory (enable divides lcm)
                  :use (gcd-divides gcd-pos))))

(defthmd posp-lcm
  (implies (and (posp x)
                (posp y))
           (posp (lcm x y)))
  :hints (("Goal" :in-theory (enable divides lcm)
                  :use (gcd-divides gcd-pos))))

(defthmd lcm-is-common-multiple
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0)))
	   (and (divides x (lcm x y))
	        (divides y (lcm x y))))
  :hints (("Goal" :in-theory (enable lcm divides)
                  :use (gcd-divides))))

;; product-rel-prime-divides is needed to prove the critical property of lcm that it divides any common multiple
;; of its arguments: Suppose x and y both divide m and let g = (gcd x y), a = x/g, and b = y/g.  Then
;;    m/(lcm x y) = mg/xy = m/gab.
;; Since a and b both divide m/g, ab divides m/g, i.e., m/gab is an integer and (lcm x y) divides m.

(defthmd lcm-is-least
  (implies (and (integerp x)
                (integerp y)
		(not (= x 0))
		(not (= y 0))
		(integerp m))
           (iff (and (divides x m)
		     (divides y m))
	        (divides (lcm x y) m)))
  :hints (("Goal" :in-theory (enable lcm divides)
                  :use (gcd-divides gcd-pos lcm-is-common-multiple
		        (:instance divides-transitive (y (lcm x y)) (z m))
		        (:instance divides-transitive (x y) (y (lcm x y)) (z m))
		        (:instance divides-transitive (x (gcd x y)) (y x) (z m))
		        (:instance gcd-quotient-2 (d (gcd x y)))
			(:instance product-rel-prime-divides (x (/ x (gcd x y))) (y (/ y (gcd x y))) (m (/ m (gcd x y))))))))
		
;;--------------------------------------------------------------------------------------------

(defthmd gcd-diff-1
  (implies (and (posp p) (posp q) (< p q))
           (equal (gcd p (- q p))
	          (gcd p q)))
  :hints (("Goal" :in-theory (enable gcd gcd-nat))))

(defthmd gcd-diff-2
  (implies (and (posp p) (posp q) (< q p))
           (equal (gcd (- p q) q)
	          (gcd p q)))
  :hints (("Goal" :in-theory (enable gcd gcd-nat))))

(defthmd gcd-num-den
  (implies (and (rationalp x) (not (= x 0)))
           (equal (gcd (numerator x) (denominator x))
	          1))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance Lowest-Terms (n (gcd (numerator x) (denominator x)))
                                                (r (/ (numerator x) (gcd (numerator x) (denominator x))))
                                                (q (/ (denominator x) (gcd (numerator x) (denominator x)))))
			(:instance gcd-divides (x (numerator x)) (y (denominator x)))
			(:instance gcd-pos (x (numerator x)) (y (denominator x)))))))

;; The lemma lowest-terms-unique shoiuld not be this hard to prove:

(local-defthm hack-1
  (implies (and (posp n) (posp d) (posp p) (posp q))
           (and (equal (* q d p (/ q)) (* d p))
	        (equal (* q d n (/ d)) (* q n))))
  :rule-classes ())

(local-defthm hack-2
  (implies (and (posp n) (posp d) (posp p) (posp q)
                (equal (/ p q) (/ n d)))
           (equal (* n q) (* d p)))
  :rule-classes ()
  :hints (("Goal" :use (hack-1))))

(local-defthm hack-3
  (implies (and (posp n) (posp d) (posp p) (posp q) (equal (gcd p q) 1)
                (equal (* n q) (* d p)))
           (divides p n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance divides-product-divides-factor (d p) (m q) (n n))))))

(defthm lowest-terms-unique
  (implies (and (posp n) (posp d) (equal (gcd n d) 1)
                (posp p) (posp q) (equal (gcd p q) 1)
                (equal (/ p q) (/ n d)))
           (and (equal n p) (equal d q)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divides)
                  :use (hack-2 hack-3 
		        (:instance hack-3 (p n) (n p) (q d) (d q))
			(:instance hack-3 (p q) (n d) (q p) (d n))
			(:instance hack-3 (p d) (n q) (q n) (d p))
			(:instance divides-leq (x p) (y n))
			(:instance divides-leq (x q) (y d))
			(:instance divides-leq (x n) (y p))
			(:instance divides-leq (x d) (y q))
			(:instance gcd-commutative (x p) (y q))
			(:instance gcd-commutative (x n) (y d))))))
