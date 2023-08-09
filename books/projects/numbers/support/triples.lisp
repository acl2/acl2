(in-package "DM")

(include-book "euclid")
(include-book "fta")
(include-book "rtl/rel11/lib/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(in-theory (enable divides))

;; Given integers m and n with m > n > 0, let a = m^2 - n^2, b = 2mn, and c = m^2 + n^2.
;; It is easiy verified that a, b, and c form a Pythagorean triple, i.e., a^2 + b^2 = c^2:

(defthm pyth-trip-sufficiency
  (implies (and (posp m) (posp n) (> m n))
	   (let ((a (- (* m m) (* n n)))
		 (b (* 2 m n))
		 (c (+ (* m m) (* n n))))
	     (equal (+ (* a a) (* b b))
		    (* c c)))))

;; We shall prove the converse: for every Pythagorean triple a, b, c, there exist m and n
;; that satisfy the above relations, possibly with a and b interchanged.  Clearly, it 
;; suffices to consider only the case where a, b, and c are positive with no common divisor.  
;; Note that this holds whenever a and b have no comon divisor:

(defthmd all-rel-prime
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1)
                (= (+ (* a a) (* b b)) (* c c)))
	   (and (equal (gcd a c) 1)
	        (equal (gcd b c) 1)))
  :hints (("Goal" :use ((:instance cpd-divides (x a) (y c))
			(:instance cpd-divides (x b) (y c))
			(:instance divides-transitive (x (cpd a c)) (y a) (z (* a a)))
			(:instance divides-transitive (x (cpd a c)) (y c) (z (* c c)))
			(:instance divides-transitive (x (cpd b c)) (y c) (z (* c c)))
			(:instance divides-transitive (x (cpd b c)) (y b) (z (* b b)))
			(:instance euclid (p (cpd a c)) (a b))
			(:instance euclid (p (cpd b c)) (b a))
			(:instance divides-sum (x (cpd a c)) (y (* c c)) (z (- (* a a))))
			(:instance divides-sum (x (cpd b c)) (y (* c c)) (z (- (* b b))))
			(:instance divides-gcd (d (cpd a c)) (x a) (y b))
			(:instance divides-gcd (d (cpd b c)) (x a) (y b))))))

;; Either a or b must be odd:

(defthmd a-or-b-odd
  (implies (and (posp a) (posp b) (= (gcd a b) 1))
           (or (oddp a) (oddp b)))
  :hints (("Goal" :use ((:instance divides-gcd (d 2) (x a) (y b))))))

;; We shall assume temporarily that a is odd.  If b were also odd, then c^2 = a^2 + b^2
;; would be 1 mod 4, which is impossible.  Therefore, b is even and c is odd:

(local-defthmd odd-square-mod-4
  (implies (and (integerp a) (oddp a))
           (equal (mod (* a a) 4) 1))
  :hints (("Goal" :use ((:instance rtl::mod-def (rtl::x a) (rtl::y 2))
                        (:instance rtl::mod-mult (rtl::n 4) (rtl::m 1) (rtl::a (* (fl (/ a 2)) (1+ (fl (/ a 2))))))))))

(local-defthmd intp*
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(local-defthmd even-square-mod-4
  (implies (and (integerp a) (evenp a))
           (equal (mod (* a a) 4) 0))
  :hints (("Goal" :use ((:instance intp* (x (/ a 2)) (y (/ a 2)))
                        (:instance rtl::mod-mult (rtl::n 4) (rtl::m 0) (rtl::a (/ (* a a) 4)))))))

(local-defthmd a-odd-b-even
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                (= (+ (* a a) (* b b)) (* c c)))
           (evenp b))
  :hints (("Goal" :use (odd-square-mod-4
                        (:instance odd-square-mod-4 (a b))
                        (:instance odd-square-mod-4 (a c))
                        (:instance even-square-mod-4 (a c))
			(:instance rtl::mod-sum (rtl::a (mod (* a a) 4)) (rtl::b (* b b)) (rtl::n 4))
			(:instance rtl::mod-sum (rtl::a (* b b)) (rtl::b (* a a)) (rtl::n 4))))))

(defthmd b-even-c-odd
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                (= (+ (* a a) (* b b)) (* c c)))
           (and (evenp b) (oddp c)))
  :hints (("Goal" :use (a-odd-b-even
                        (:instance euclid (p 2) (b a))
                        (:instance divides-transitive (x 2) (y b) (z (* b b)))
                        (:instance divides-transitive (x 2) (y c) (z (* c c)))))))

;; We define m and n so that m/n is a reduced fraction and m/n = (a + c)/b:

(defund m$ (a b c)
  (/ (+ a c) (gcd (+ a c) b)))

(defund n$ (a b c)
  (/ b (gcd (+ a c) b)))

(defthmd gcd-m-n
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (and (posp m) (posp n) (equal (gcd m n) 1) (equal (/ m n) (/ (+ a c) b)))))
  :hints (("Goal" :in-theory (enable m$ n$)
                  :use ((:instance gcd-divides (x (+ a c)) (y b))
		        (:instance gcd-pos (x (+ a c)) (y b))
		        (:instance gcd-quotient-2 (x (+ a c)) (y b) (d (gcd (+ a c) b)))))))
                        

;; Since (c - a)(c + a) = b^2, (c - a)/b = b/(c + a) = n/m:

(local-defthmd recip-m/n-1
  (implies (and (integerp c-a) (posp c+a) (posp b) (= (* c-a c+a) (* b b)))
           (equal (/ c-a b) (/ b c+a)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd recip-m/n-2
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                (= (+ (* a a) (* b b)) (* c c)))
           (and (integerp (- c a)) (posp (+ c a)) (= (* (- c a) (+ c a)) (* b b)))))

(local-defthmd recip-m/n-3
  (implies (and (posp m) (posp n) (rationalp x))
           (iff (= (/ m n) x)
	        (= m (* n x))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd recip-m/n-4
  (implies (and (posp m) (posp n) (posp x) (posp y))
           (iff (= (/ m n) (/ x y))
	        (= (* m y) (* n x))))
  :hints (("Goal" :use ((:instance recip-m/n-3 (x (/ x y)))
                        (:instance recip-m/n-3 (m (* x n)) (n y) (x m))))))

(local-defthmd recip-m/n-5
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ n m) (/ b (+ c a)))))
  :hints (("Goal" :use (gcd-m-n
                        (:instance recip-m/n-3 (m (m$ a b c)) (n (n$ a b c)) (x (/ (+ c a) b)))
                        (:instance recip-m/n-3 (n (m$ a b c)) (m (n$ a b c)) (x (/ b (+ c a))))))))

(defthmd recip-m/n
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ n m) (/ (- c a) b))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (recip-m/n-5 recip-m/n-2
                        (:instance recip-m/n-1 (c-a (- c a)) (c+a (+ c a)))))))

;; The last 2 equations may be written as c/b + a/b = m/n and c/b - a/b = n/m.
;; Solve this pair of equations for c/b and a/b:

;;    c/b = 1/2 * (m/n + n/m) = (m^2 + n^2)/2mn

;;    a/b = 1/2 * (m/n - n/m) = (m^2 - n^2)/2mn

(local-defthm c/b-val-1
  (implies (and (rationalp x) (rationalp y) (rationalp a) (rationalp b)
                (= (+ x y) a) (= (- x y) b))
	   (and (equal x (/ (+ a b) 2))
	        (equal y (/ (- a b) 2))))
  :rule-classes ())

(local-defthmd c/b-val-2
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (and (equal (/ c b) (/ (+ (/ m n) (/ n m)) 2))
	          (equal (/ a b) (/ (- (/ m n) (/ n m)) 2)))))
  :hints (("Goal" :use (gcd-m-n recip-m/n
                        (:instance c/b-val-1 (x (/ c b)) (y (/ a b))
                                             (a (/ (m$ a b c) (n$ a b c))) (b (/ (n$ a b c) (m$ a b c))))))))

(local-defthmd c/b-val-3
  (implies (and (posp m) (posp n))
           (and (equal (+ (/ m n) (/ n m))
	               (/ (+ (* m m) (* n n))
		          (* m n)))
	        (equal (- (/ m n) (/ n m))
	               (/ (- (* m m) (* n n))
		          (* m n))))))

(defthmd c/b-val
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ c b) (/ (+ (* m m) (* n n)) (* 2 m n)))))
  :hints (("Goal" :use (c/b-val-2 (:instance c/b-val-3 (m (m$ a b c)) (n (n$ a b c)))))))

(defthmd a/b-val
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ a b) (/ (- (* m m) (* n n)) (* 2 m n)))))
  :hints (("Goal" :use (c/b-val-2 (:instance c/b-val-3 (m (m$ a b c)) (n (n$ a b c)))))))

;; The last equation may be written as 2amn = b(m^2 - n^2).  If m and m were both odd,
;; then the right side would be divisible by 8, which the left side is not.  Thus,
;; exactly one of m and n is even, which implies m^2 - n^2 is odd.  Since m^2 - n^2
;; has no factor in common with either m or n, it follows that a = m^2 - n^2 and
;; b = 2mn, and by c/b-val, c = m^2 + n^2:

(local-defthmd a-b-c-vals-1
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (* 2 c m n)
	            (* b (+ (* m m) (* n n))))))
  :hints (("Goal" :use (c/b-val gcd-m-n
                        (:instance recip-m/n-4 (m c) (n b)
			                       (x (+ (* (m$ a b c) (m$ a b c)) (* (n$ a b c) (n$ a b c))))
					       (y (* 2 (m$ a b c) (n$ a b c))))))))

(local-defthmd a-b-c-vals-2
  (implies (and (posp m) (posp n) (oddp m) (oddp n))
           (evenp (+ (* m m) (* n n))))
  :hints (("Goal" :use ((:instance euclid (p 2) (a m) (b m))
                        (:instance euclid (p 2) (a n) (b n))))))

(local-defthmd a-b-c-vals-3
  (implies (and (posp m) (posp n) (oddp m) (oddp n) (posp b) (evenp b))
           (divides 4 (* b (+ (* m m) (* n n)))))
  :hints (("Goal" :use (a-b-c-vals-2
                        (:instance intp* (x (/ b 2)) (y (/ (+ (* m m) (* n n)) 2)))))))

(local-defthmd a-b-c-vals-4
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (evenp (* c m n))))
  :hints (("Goal" :use (a-b-c-vals-1 gcd-m-n a-odd-b-even
                        (:instance a-b-c-vals-3 (m (m$ a b c)) (n (n$ a b c)))))))

(local-defthmd a-b-c-vals-5
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (iff (evenp m) (oddp n))))
  :hints (("Goal" :use (a-b-c-vals-4 gcd-m-n b-even-c-odd
                        (:instance divides-gcd (x (m$ a b c)) (y (n$ a b c)) (d 2))
			(:instance euclid (p 2) (a c) (b (* (m$ a b c) (n$ a b c))))
			(:instance euclid (p 2) (a (m$ a b c)) (b (n$ a b c)))))))

(local-defthmd a-b-c-vals-6
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (oddp (+ (* m m) (* n n)))))
  :hints (("Goal" :use (a-b-c-vals-5 gcd-m-n
                        (:instance divides-transitive (x 2) (y (m$ a b c)) (z (* (m$ a b c) (m$ a b c))))
                        (:instance divides-transitive (x 2) (y (n$ a b c)) (z (* (n$ a b c) (n$ a b c))))
			(:instance euclid (p 2) (a (m$ a b c)) (b (m$ a b c)))
			(:instance euclid (p 2) (a (n$ a b c)) (b (n$ a b c)))))))

(local-defthmd a-b-c-vals-7
  (implies (and (posp m) (posp n) (= (gcd m n) 1) (primep p) (divides p m))
           (not (divides p (+ (* m m) (* n n)))))
  :hints (("Goal" :use ((:instance divides-transitive (x p) (y m) (z (* m m)))
                        (:instance divides-gcd (d p) (x m) (y n))
			(:instance euclid (a n) (b n))))))

(local-defthmd a-b-c-vals-8
  (implies (and (posp m) (posp n) (= (gcd m n) 1) (oddp (+ (* m m) (* n n))))
           (equal (gcd (+ (* m m) (* n n))
	               (* 2 m n))
		  1))
  :hints (("Goal" :use ((:instance gcd-commutative (x m) (y n))
                        (:instance primep-no-divisor (p 2) (d (cpd (+ (* m m) (* n n)) (* 2 m n))))
                        (:instance euclid (p (cpd (+ (* m m) (* n n)) (* 2 m n))) (a 2) (b (* m n)))
                        (:instance euclid (p (cpd (+ (* m m) (* n n)) (* 2 m n))) (a m) (b n))
			(:instance a-b-c-vals-7 (p (cpd (+ (* m m) (* n n)) (* 2 m n))))
			(:instance a-b-c-vals-7 (p (cpd (+ (* m m) (* n n)) (* 2 m n))) (m n) (n m))
			(:instance cpd-divides (x (+ (* m m) (* n n))) (y (* 2 m n)))))))

(defthm a-b-c-vals
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (and (posp m) (posp n)
	          (equal a (- (* m m) (* n n)))
  	          (equal b (* 2 m n ))
	          (equal c (+ (* m m) (* n n))))))
  :rule-classes ()
  :hints (("Goal" :use (a-b-c-vals-6 gcd-m-n all-rel-prime c/b-val
                        (:instance gcd-commutative (x c) (y b))
                        (:instance a-b-c-vals-8 (m (m$ a b c)) (n (n$ a b c)))
                        (:instance lowest-terms-unique (p (+ (* (m$ a b c) (m$ a b c)) (* (n$ a b c) (n$ a b c))))
			                               (q (* 2 (m$ a b c) (n$ a b c)))
			                               (n c)
						       (d b))))))

;; If a is even, we simply interchange a and b:

(defund pyth-trip-generators (a b c)
  (let ((g (gcd (+ c a) b)))
    (mv (/ (+ c a) g)
	(/ b g))))

(defthm pyth-trip-necessity
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1)
                (= (+ (* a a) (* b b)) (* c c)))
	   (if (oddp a)
	       (mv-let (m n) (pyth-trip-generators a b c)
	         (and (posp m) (posp n)
		      (equal a (- (* m m) (* n n)))
	              (equal b (* 2 m n ))
		      (equal c (+ (* m m) (* n n)))))
	     (mv-let (m n) (pyth-trip-generators b a c)
	       (and (posp m) (posp n)
		    (equal b (- (* m m) (* n n)))
	            (equal a (* 2 m n ))
		    (equal c (+ (* m m) (* n n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable m$ n$ pyth-trip-generators)
                  :use (a-or-b-odd a-b-c-vals
		        (:instance gcd-commutative (x a) (y b))
		        (:instance a-b-c-vals (a b) (b a))))))




     
