;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/proofs"))

(defun fl (x) (floor x 1))

(defun bits (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(in-theory (disable fl bits))


;;;**********************************************************************
;;;                       SGN, SIG, and EXPO
;;;**********************************************************************

(defun expo1 (x)
  (declare (xargs :measure (:? x)))
  (if (and (rationalp x) (< 0 x) (< x 1))
      (1- (expo1 (* x 2)))
    0))

(defun expo2 (x)
  (declare (xargs :measure (:? x)))
  (if (and (rationalp x) (>= x 2))
      (1+ (expo2 (/ x 2)))
    0))

(defun expo (x)
  (cond ((not (rationalp x)) 0)
	((>= (abs x) 1) (expo2 (abs x)))
	(t (expo1 (abs x)))))

(defun sgn (x)
  (if (= x 0)
      0
    (if (< x 0) -1 +1)))

(defun sig (x)
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(in-theory (disable sgn sig expo))

(defthm sgn*
    (implies (and (rationalp x) (rationalp y))
	     (= (sgn (* x y)) (* (sgn x) (sgn y))))
  :rule-classes ())

(defthm fp-rep
    (implies (rationalp x)
	     (equal x (* (sgn x) (sig x) (expt 2 (expo x)))))
  :rule-classes ())

(defthm fp-abs
    (implies (rationalp x)
	     (equal (abs x) (* (sig x) (expt 2 (expo x)))))
  :rule-classes ())

(defthm expo-2**n
    (implies (integerp n)
	     (equal (expo (expt 2 n))
		    n)))

(defthm expo-lower-bound
    (implies (and (rationalp x)
		  (not (= x 0)))
	     (<= (expt 2 (expo x)) (abs x)))
  :rule-classes ())

(defthm expo-upper-bound
    (implies (and (rationalp x)
		  (not (= x 0)))
	     (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm expo>=
    (implies (and (rationalp x)
		  (integerp n)
		  (>= x (expt 2 n)))
	     (>= (expo x) n))
  :rule-classes ())

(defthm expo<=
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (< x (* 2 (expt 2 n))))
	     (<= (expo x) n))
  :rule-classes ())

(defthm expo-squeeze
    (implies (and (rationalp x)
		  (integerp n)
		  (<= (expt 2 n) (abs x))
		  (< (abs x) (expt 2 (1+ n))))
	     (= (expo x) n))
  :rule-classes ())

(defthm expo-minus
    (implies (rationalp x)
	     (= (expo (- x))
		(expo x)))
  :rule-classes ())

(defthm sig-minus
    (implies (rationalp x)
	     (= (sig (- x))
		(sig x)))
  :rule-classes ())

(defthm sig-lower-bound
    (implies (and (rationalp x)
		  (not (= x 0)))
	     (<= 1 (sig x)))
  :rule-classes ())

(defthm sig-upper-bound
    (implies (and (rationalp x)
		  (not (= x 0)))
	     (< (sig x) 2))
  :rule-classes ())

(defthm expo-unique
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (<= (expt 2 n) (abs x))
		  (< (abs x) (expt 2 (1+ n))))
	     (equal n (expo x)))
  :rule-classes ())

(defthm expo-monotone
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (<= (abs x) (abs y)))
	     (<= (expo x) (expo y)))
  :rule-classes ())

(defthm fp-rep-unique
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp m)
		  (<= 1 m)
		  (< m 2)
		  (integerp e)
		  (= (abs x) (* m (expt 2 e))))
	     (and (= m (sig x))
		  (= e (expo x))))
  :rule-classes ())

(defthm sig-expo-shift
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n))
	     (and (= (sig (* (expt 2 n) x)) (sig x))
		  (= (expo (* (expt 2 n) x)) (+ n (expo x)))))
  :rule-classes ())

(defthm expo-prod-lower
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (<= (+ (expo x) (expo y)) (expo (* x y))))
  :rule-classes ())

(defthm expo-prod-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
  :rule-classes ())

(defthm rem-expo
    (implies (and (integerp x)
		  (> x 0))
	     (= (rem x (expt 2 (expo x)))
		(- x (expt 2 (expo x)))))
  :rule-classes ())


;;;**********************************************************************
;;;                            EXACTP
;;;**********************************************************************

(defun exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defthm exactp2
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (exactp x n)
		    (integerp (* x (expt 2 (- (1- n) (expo x))))))))

(in-theory (disable exactp exactp2))

(defthm exact-neg
    (implies (and (rationalp x)
		  (integerp n))
	     (iff (exactp x n) (exactp (abs x) n)))
  :rule-classes ())

(defthm exactp-
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (- x) n))
  :rule-classes ())

(defthm exactp-shift
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (exactp x m))
	     (exactp (* (expt 2 n) x) m)))

(defthm exactp-prod
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp n)
		  (exactp x m)
		  (exactp y n))
	     (exactp (* x y) (+ m n)))
  :rule-classes ())

(defthm exactp-x2
    (implies (and (rationalp x)
		  (integerp k)
		  (exactp x k)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :rule-classes ())

(defthm exactp-<=
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp m)
		  (<= m n)
		  (exactp x m))
	     (exactp x n))
  :rule-classes ())

(defthm expo-diff
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (integerp n)
		  (> n 0)
		  (> n k)
		  (exactp x n)
		  (exactp y n)
		  (<= (+ k (expo (- x y))) (expo x))
		  (<= (+ k (expo (- x y))) (expo y)))
	     (exactp (- x y) (- n k)))
  :rule-classes ())

(defthm expo-diff-0
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (<= (expo (- x y)) (expo x))
		  (<= (expo (- x y)) (expo y)))
	     (exactp (- x y) n))
  :rule-classes ())

(defthm expo-diff-cor
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (<= (abs (- x y)) (abs x))
		  (<= (abs (- x y)) (abs y)))
	     (exactp (- x y) n))
  :rule-classes ())

(defthm expo-diff-min
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (not (= y x)))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :rule-classes ())

(defthm expo-diff-abs-any
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ())

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defthm fp+1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= y (fp+ x n)))
  :rule-classes ())

(defthm fp+2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (fp+ x n) n))
  :rule-classes ())

(defthm exactp-2**n
    (implies (and (integerp n)
		  (integerp m)
		  (> m 0))
	     (exactp (expt 2 n) m))
  :rule-classes ())

(defthm exact-bits-a-b
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :rule-classes ())

(defthm exact-bits-a-c
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (= (bits x (1- n) k)
		     (/ x (expt 2 k)))))
  :rule-classes ())

(defthm exact-bits-a-d
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (= (bits x (1- k) 0)
		     0)))
  :rule-classes ())
