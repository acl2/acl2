(in-package "DM")

(include-book "euclid")
(local (include-book "support/triples"))

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
;; suffices to consider only the case where a, b, and c are positive with no common 
;; divisor.  Note that this holds whenever a and b have no comon divisor:

(defthmd all-rel-prime
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1)
                (= (+ (* a a) (* b b)) (* c c)))
	   (and (equal (gcd a c) 1)
	        (equal (gcd b c) 1))))

;; Either a or b must be odd:

(defthmd a-or-b-odd
  (implies (and (posp a) (posp b) (= (gcd a b) 1))
           (or (oddp a) (oddp b))))

;; We shall assume temporarily that a is odd.  If b were also odd, then c^2 = a^2 + b^2
;; would be 1 mod 4, which is impossible.  Therefore, b is even and c is odd:

(defthmd b-even-c-odd
  (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                (= (+ (* a a) (* b b)) (* c c)))
           (and (evenp b) (oddp c))))

;; We define m and n so that m/n is a reduced fraction and m/n = (a + c)/b:

(defund m$ (a b c)
  (/ (+ a c) (gcd (+ a c) b)))

(defund n$ (a b c)
  (/ b (gcd (+ a c) b)))

(defthmd gcd-m-n
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (and (posp m) (posp n)
		  (equal (gcd m n) 1)
		  (equal (/ m n) (/ (+ a c) b))))))
                        

;; Since (c - a)(c + a) = b^2, (c - a)/b = b/(c + a) = n/m:

(defthmd recip-m/n
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ n m) (/ (- c a) b)))))

;; The last 2 equations may be written as c/b + a/b = m/n and c/b - a/b = n/m.
;; Solve this pair of equations for c/b and a/b:

;;    c/b = 1/2 * (m/n + n/m) = (m^2 + n^2)/2mn

;;    a/b = 1/2 * (m/n - n/m) = (m^2 - n^2)/2mn

(defthmd c/b-val
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ c b) (/ (+ (* m m) (* n n)) (* 2 m n))))))

(defthmd a/b-val
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (equal (/ a b) (/ (- (* m m) (* n n)) (* 2 m n))))))

;; The last equation may be written as 2amn = b(m^2 - n^2).  If m and m were both odd,
;; then the right side would be divisible by 8, which the left side is not.  Thus,
;; exactly one of m and n is even, which implies m^2 - n^2 is odd.  Since m^2 - n^2
;; has no factor in common with either m or n, it follows that a = m^2 - n^2 and
;; b = 2mn, and by c/b-val, c = m^2 + n^2:

(defthm a-b-c-vals
  (let ((m (m$ a b c)) (n (n$ a b c)))
    (implies (and (posp a) (posp b) (posp c) (= (gcd a b) 1) (oddp a)
                  (= (+ (* a a) (* b b)) (* c c)))
             (and (posp m) (posp n)
	          (equal a (- (* m m) (* n n)))
  	          (equal b (* 2 m n ))
	          (equal c (+ (* m m) (* n n))))))
  :rule-classes ())

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
  :rule-classes ())




     
