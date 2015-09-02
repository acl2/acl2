;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/proofs"))


;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

(in-theory (disable fl cg))

(defthm int-fl
    (implies (rationalp x)
	     (integerp (fl x))))

(defthm int-cg
    (implies (rationalp x)
	     (integerp (cg x))))

(defthm fl-int-2
    (implies (rationalp x)
	     (iff (equal (fl x) x)
		  (integerp x))))

(defthm cg-int-2
    (implies (rationalp x)
	     (iff (equal (cg x) x)
		  (integerp x))))

(defthm fl-def
    (implies (rationalp x)
	     (and (<= (fl x) x)
		  (< x (1+ (fl x)))))
  :rule-classes ())

(defthm cg-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes ())

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

(defthm cg-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())

(defthm cg-def
    (implies (rationalp x)
	     (and (>= (cg x) x)
		  (> (1+ x) (cg x))))
  :rule-classes ())

(defthm fl-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (fl x) (fl y)))
  :rule-classes ())

(defthm n<=fl
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x))
	     (<= n (fl x)))
  :rule-classes ())

(defthm n>=cg
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x))
	     (>= n (cg x)))
  :rule-classes ())

(defthm fl+int
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (fl (+ x n)) (+ (fl x) n))))

(defthm cg+int
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (cg (+ x n)) (+ (cg x) n))))

(defthm fl/int
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (fl (/ (fl x) n))
		    (fl (/ x n)))))

(defthm fl-cg
    (implies (and (rationalp x)
		  (not (integerp x)))
	     (equal (cg x) (1+ (fl x))))
  :rule-classes ())

(defthm cg/int
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (cg (/ (cg x) n))
		    (cg (/ x n)))))

(defthm floor-m+1
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (fl (- (/ (1+ m) n)))
		(1- (- (fl (/ m n))))))
  :rule-classes ())

(defthm floor-2
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ())

(defthm floor-fl
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (= (floor m n) (fl (/ m n))))
  :rule-classes ())


;;;**********************************************************************
;;;                       EXPONENTIATION
;;;**********************************************************************

(defthm expt-pos
    (implies (integerp x)
	     (> (expt 2 x) 0)))

(in-theory (disable expt-pos))

(defthm expt-non-neg
    (implies (integerp n)
	     (not (< (expt 2 n) 0))))

(defthm integerp-expt
    (implies (and (integerp n)
		  (>= n 0))
	     (integerp (expt 2 n))))

(in-theory (disable integerp-expt))

(defthm expt>=1
    (implies (and (integerp n)
		  (>= n 0))
	     (and (integerp (expt 2 n))
		  (>= (expt 2 n) 1)))
  :rule-classes ())

(defthm expt-monotone
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m))
	     (<= (expt 2 n) (expt 2 m)))
  :rule-classes ())

(defthm expt-strong-monotone
    (implies (and (integerp n)
		  (integerp m))
	     (iff (< n m) (< (expt 2 n) (expt 2 m))))
  :rule-classes ())

(defthm expt-
    (implies (and (integerp a)
		  (integerp b))
	     (= (/ (expt 2 a) (expt 2 b)) (expt 2 (- a b))))
  :rule-classes ())

(defthm expo+
    (implies (and (integerp n)
		  (integerp m))
	     (= (expt 2 (+ m n))
		(* (expt 2 m) (expt 2 n))))
  :rule-classes ())


;;;**********************************************************************
;;;                         REMAINDERS
;;;**********************************************************************

(in-theory (disable rem))

(defthm rem>=0
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (<= 0 (rem m n)))
  :rule-classes ())

(defthm rem<n
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (< (rem m n) n))
  :rule-classes ())

(defthm rem<=m
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (<= (rem m n) m))
  :rule-classes ())

(defthm rem-fl
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (+ (* n (fl (/ m n))) (rem m n))
		m))
  :rule-classes ())

(defthm rem+
    (implies (and (integerp m)
		  (integerp n)
		  (integerp a)
		  (> n 0)
		  (>= a 0)
		  (>= m 0))
	     (= (rem (+ m (* a n)) n)
		(rem m n)))
  :rule-classes ())

(defthm rem-minus-rem
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a b)
		  (>= b 0)
		  (> n 0))
	     (= (rem (- a (rem b n)) n)
		(rem (- a b) n)))
  :rule-classes ())

(defthm rem<
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0)
		  (< m n))
	     (= (rem m n) m))
  :rule-classes ())

(defthm integerp-rem
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n)))
  :rule-classes (:type-prescription))

(defthm rationalp-rem
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n)))
  :rule-classes (:type-prescription))

(defthm rem-rem
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp b)
		  (> b 0)
		  (integerp a)
		  (>= a b))
	     (= (rem x (expt 2 b))
		(rem (rem x (expt 2 a)) (expt 2 b))))
  :rule-classes ())

(defthm rem-m=n
    (implies (and (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n 0)
		  (< m (* 2 n))
		  (= (rem m n) 0))
	     (= m n))
  :rule-classes ())

(defthm rem**
    (implies (and (integerp m)
		  (>= m 0)
		  (integerp n)
		  (> n 0)
		  (integerp k)
		  (> k 0))
	     (= (rem (* k m) (* k n))
		(* k (rem m n))))
  :rule-classes ())

(defthm rem-squeeze
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp a) (>= a 0)
		  (integerp r) (>= r 0)
		  (<= (* a n) m)
		  (< m (+ (* a n) r)))
	     (< (rem m n) r))
  :rule-classes ())

(defthm rem-squeeze-2
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp a) (>= a 0)
		  (> (* (1+ a) n) m)
		  (>= m (* a n)))
	     (= (rem m n) (- m (* a n))))
  :rule-classes ())

(defthm rem=rem
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (integerp (/ (- a b) n)))
  :rule-classes ())

(defthm fl-rem-0
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (iff (= (rem m n) 0)
		  (= m (* (fl (/ m n)) n))))
  :rule-classes ())

(defthm fl-rem-1
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (>= m (* (fl (/ m n)) n)))
  :rule-classes ())

(defthm fl-rem-5
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp p) (> p 0))
	     (iff (= (rem m (* n p)) 0)
		  (and (= (rem m n) 0)
		       (= (rem (fl (/ m n)) p) 0))))
  :rule-classes ())

(defthm divides-rem-0
    (implies (and (integerp n)
		  (integerp a)
		  (> n 0)
		  (>= a 0))
	     (= (rem (* a n) n)
		0))
  :rule-classes ())

(defthm rem+rem
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a 0)
		  (>= b 0)
		  (> n 0))
	     (= (rem (+ a (rem b n)) n)
		(rem (+ a b) n)))
  :rule-classes ())

(defthm rem=rem<n
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (< (abs (- a b)) n)
		  (= (rem a n) (rem b n)))
	     (= a b))
  :rule-classes ())

(defthm nk>=k
    (implies (and (integerp n)
		  (integerp k)
		  (> k 0)
		  (not (= (* n k) 0)))
	     (>= (abs (* n k)) k))
  :rule-classes ())

(defthm rem012
    (implies (and (integerp x)
		  (>= x 0))
	     (or (= (rem x 2) 0)
		 (= (rem x 2) 1)))
  :rule-classes ())

(defthm rem+1-2
    (implies (and (integerp x)
		  (>= x 0))
	     (not (= (rem x 2) (rem (1+ x) 2))))
  :rule-classes ())

(defthm x-or-x/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ())

(defthm rem-2*i
    (implies (integerp i)
	     (equal (rem (* 2 i) 2) 0))
  :rule-classes ())

(defthm rem-2*i+1
    (implies (integerp i)
	     (not (equal (rem (1+ (* 2 i)) 2) 0)))
  :rule-classes ())

(defun fl-half (x)
  (1- (fl (/ (1+ x) 2))))

(in-theory (disable fl-half))

(defthm fl-half-lemma
    (implies (and (integerp x)
		  (not (integerp (/ x 2))))
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ())
