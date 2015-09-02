;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "basic")

(local
 (defthm floor-m+1-1
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (= (fl (- (/ (1+ m) n)))
		(+ (- (floor (/ m n) 1)) (fl (- (/ (1+ (rem m n)) n))))))
   :rule-classes ())
 )

(local
  (defthm floor-m+1-2
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (= (fl (- (/ (1+ m) n)))
		(+ (- (fl (/ m n))) (fl (- (/ (1+ (rem m n)) n))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fl)
		  :use ((:instance floor-m+1-1)))))
  )

(local
(defthm floor-m+1-3
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= (nonnegative-integer-quotient m n) (/ m n)))
  :rule-classes ())
)

(local
(defthm floor-m+1-4
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (= (denominator (* m (/ n))) 1))
	     (<= (floor m n) (/ m n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-3)
			(:instance floor (i m) (j n))
			(:instance rational-implies2 (x (* m (/ n)))))
		  :in-theory (disable rational-implies2))))
)

(local
(defthm floor-m+1-5
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= (floor m n) (/ m n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-3 (m (numerator (* m (/ n))))
						(n (denominator (* m (/ n)))))
			(:instance floor (i m) (j n))
			(:instance floor-m+1-4)))))
)

(defthm REM>=0
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= 0 (rem m n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-5)))))

(local
(defthm floor-m+1-6
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (> (nonnegative-integer-quotient m n) (1- (/ m n))))
  :rule-classes ())
)

(local
(defthm floor-m+1-7
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (= (denominator (* m (/ n))) 1))
	     (> (floor m n) (1- (/ m n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-6)
			(:instance floor (i m) (j n))
			(:instance rational-implies2 (x (* m (/ n)))))
		  :in-theory (disable rational-implies2))))
)

(local
(defthm floor-m+1-8
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (> (floor m n) (1- (/ m n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-6 (m (numerator (* m (/ n))))
						(n (denominator (* m (/ n)))))
			(:instance floor (i m) (j n))
			(:instance floor-m+1-7)))))
)

(defthm REM<N
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (< (rem m n) n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-8)))))

(local
(defthm floor-m+1-9
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= (1+ (rem m n)) n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem<n)))))
)

(local
(defthm floor-m+1-10
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (<= x y)
		  (> z 0))
	     (<= (/ x z) (/ y z)))
  :rule-classes ())
)

(local
(defthm floor-m+1-11
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= (/ (1+ (rem m n)) n) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-9)
			(:instance floor-m+1-10 (x (1+ (rem m n))) (y n) (z n))))))
)

(local
(defthm floor-m+1-12
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (> (/ (1+ (rem m n)) n) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem>=0)))))
)

(local
(defthm floor-m+1-13
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (fl (- (/ (1+ (rem m n)) n)))
		-1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-unique (n -1) (x (- (/ (1+ (mod m n)) n))))
			(:instance floor-m+1-11)
			(:instance floor-m+1-12)))))
)

(defthm FLOOR-M+1
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (fl (- (/ (1+ m) n)))
		(1- (- (fl (/ m n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-13)
			(:instance floor-m+1-2)))))

(defthm REM-FL
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (+ (* n (fl (/ m n))) (rem m n))
		m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fl))))

(defthm FLOOR-FL
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (= (floor m n) (fl (/ m n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1-5)
			(:instance floor-m+1-8)
			(:instance fl-unique (x (/ m n)) (n (floor x n)))))))

(defthm REM+
    (implies (and (integerp m)
		  (integerp n)
		  (integerp a)
		  (> n 0)
		  (>= a 0)
		  (>= m 0))
	     (= (rem (+ m (* a n)) n)
		(rem m n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl)
			(:instance rem-fl (m (+ m (* a n))))
			(:instance fl+int (x (/ m n)) (n a))))))

(defthm REM<
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0)
		  (< m n))
	     (= (rem m n) m))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl)
			(:instance fl-unique (x (/ m n)) (n 0))))))

(defthm INTEGERP-REM
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable rem))))

(defthm RATIONALP-REM
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable rem))))

(in-theory (disable rem))



