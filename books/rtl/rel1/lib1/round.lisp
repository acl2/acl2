;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/proofs"))

(local (include-book "float"))

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

(in-theory (disable fl cg))

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

(defun exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(in-theory (disable exactp))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))


;;;**********************************************************************
;;;                            TRUNC
;;;**********************************************************************

(defun trunc (x n)
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(in-theory (disable trunc))

(defthm trunc-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (trunc x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

(in-theory (disable trunc-rewrite))

(defthm trunc-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) 0))
  :rule-classes ())

(defthm trunc-neg
    (implies (and (rationalp x)
		  (< x 0)
		  (integerp n)
		  (> n 0))
	     (< (trunc x n) 0))
  :rule-classes ())

(defthm trunc-minus
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (trunc (- x) n) (- (trunc x n))))
  :rule-classes ())

(defthm trunc-zero
    (implies (and (integerp n)
		  (> n 0))
	     (= (trunc 0 n) 0))
  :rule-classes ())

(defthm sgn-trunc
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (trunc x n))
		    (sgn x))))

(defthm abs-trunc
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (abs (trunc x n))
		    (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))

(in-theory (disable abs-trunc))

(defthm trunc-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (abs (trunc x n)) (abs x)))
  :rule-classes ())

(defthm trunc-upper-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (<= (trunc x n) x))
  :rule-classes ())

(defthm expo-trunc
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (expo (trunc x n)) (expo x))))

(defthm trunc-shift
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (trunc (* x (expt 2 k)) n)
		(* (trunc x n) (expt 2 k))))
  :rule-classes ())

(defthm trunc-lower-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (> (abs (trunc x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ())

(defthm trunc-lower-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes ())

(defthm trunc-lower-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes ())

(defthm trunc-lower-4
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (trunc x n) (- x (* (abs x) (expt 2 (- 1 n))))))
  :rule-classes ())

(defthm trunc-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ())

(defthm trunc-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (trunc x n))
		  (exactp x n)))
  :rule-classes ())

(defthm trunc-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (trunc x n) n)))

(defthm trunc-exactp-c
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (trunc x n))))

(defthm trunc-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> x 0)
		  (> y 0)
		  (> n 0)
		  (<= x y))
	     (<= (trunc x n) (trunc y n)))
  :rule-classes ())

(defthm trunc-trunc
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (trunc (trunc x n) m)
		    (trunc x m)))
  :rule-classes ())

(defthm plus-trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (> n 0)
		  (exactp x n))
	     (= (+ x (trunc y k))
		(trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())

(defthm trunc-plus
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e))
		  (integerp m)
		  (> m 0)
		  (integerp k)
		  (> k 0)
		  (<= m (1+ k)))
	     (= (trunc (+ (expt 2 e) (trunc y k)) m)
		(trunc (+ (expt 2 e) y) m)))
  :rule-classes ())

(defthm trunc-n+k
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  ;;this isn't really needed, but it won't hurt me.
		  (not (exactp x n))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n))
		  (= y (- x (trunc x n))))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (1- (sig (trunc (+ (expt 2 e) z) (1+ k))))
		   (expt 2 e))))
  :rule-classes ())

(defthm bits-trunc
    (implies (and (integerp x) (> x 0)
		  (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (>= x (expt 2 (1- n)))
		  (< x (expt 2 n)))
	     (= (trunc x k)
		(logand x (- (expt 2 m) (expt 2 (- n k))))))
  :rule-classes ())

(defthm int-trunc
    (implies (and (rationalp x)
		  (integerp n)
		  (>= (expo x) n)
		  (> n 0))
	     (integerp (trunc x n)))
  :rule-classes ())

(defthm trunc-away-a
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
  :rule-classes ())


;;;**********************************************************************
;;;                            AWAY
;;;**********************************************************************

(defun away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(in-theory (disable away))

(defthm away-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (away x n)
		    (* (sgn x)
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

(in-theory (disable away-rewrite))

(defthm away-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (away x n) 0))
  :rule-classes ())

(defthm away-neg
    (implies (and (rationalp x)
		  (< x 0)
		  (integerp n)
		  (> n 0))
	     (< (away x n) 0))
  :rule-classes ())

(defthm away-minus
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (away (- x) n) (- (away x n))))
  :rule-classes ())

(defthm away-zero
    (implies (and (integerp n)
		  (> n 0))
	     (= (away 0 n) 0))
  :rule-classes ())

(defthm sgn-away
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (away x n))
		    (sgn x))))

(defthm abs-away
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (abs (away x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))

(in-theory (disable abs-away))

(defthm away-lower-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (away x n)) (abs x)))
  :rule-classes ())

(defthm away-lower-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (>= (away x n) x))
  :rule-classes ())

(defthm expo-away-lower-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (expo (away x n)) (expo x)))
  :rule-classes ())

(defthm away-upper-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (away x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ())

(defthm away-upper-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (< (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes ())

(defthm away-upper-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes ())

(defthm away-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (away x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm away-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- (away x n) x) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm away-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes ())

(defthm away-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (away x n))
		  (exactp x n)))
  :rule-classes ())

(defthm away-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (away x n) n)))

(defthm away-exactp-c
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (away x n))))

(defthm away-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> x 0)
		  (> y 0)
		  (> n 0)
		  (<= x y))
	     (<= (away x n) (away y n)))
  :rule-classes ())

(defthm away-exactp-d
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm expo-away
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
	     (= (expo (away x n)) (expo x)))
  :rule-classes ())

(defthm away-shift
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (away (* x (expt 2 k)) n)
		(* (away x n) (expt 2 k))))
  :rule-classes ())

(defthm away-away
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m)))
  :rule-classes ())

(defthm away-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (= (away x n)
		(trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)))
  :rule-classes ())

(defthm trunc-away-b
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ())

(defthm trunc-away
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ())

(defthm minus-trunc-4
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (away (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ())

(defthm minus-trunc-5
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ())


;;;**********************************************************************
;;;                            NEAR
;;;**********************************************************************

(defun re (x)
  (- x (fl x)))

(defun near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))

(in-theory (disable near))

(defthm near1-a
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (< (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (trunc x n)))
  :rule-classes ())

(defthm near1-b
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (away x n)))
  :rule-classes ())

(defthm near-choice
    (or (= (near x n) (trunc x n))
	(= (near x n) (away x n)))
  :rule-classes ())

(defthm near2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n))
	     (>= (abs (- x y)) (abs (- x (near x n)))))
  :rule-classes ())

(defthm exactp-near
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (near x n) n)))

(defthm near-exactp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x n))
	     (equal (near x n) x))
  :rule-classes ())

(defthm near-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (near x n) 0))
  :rule-classes ())

(defthm near-neg
    (implies (and (rationalp x)
		  (< x 0)
		  (integerp n)
		  (> n 0))
	     (< (near x n) 0))
  :rule-classes ())

(defthm near-minus
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (near (- x) n) (- (near x n))))
  :rule-classes ())

(defthm near-0-0
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= (near x n) 0)
		  (= x 0)))
  :rule-classes ())

(defthm sgn-near
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (near x n)
		(* (sgn x) (near (abs x) n))))
  :rule-classes ())

(defthm monotone-near
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (near y n))))

(defthm near<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (away x n)))
  :rule-classes ())

(defthm near>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (near x n) (trunc x n)))
  :rule-classes ())

(defthm near-shift
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (near (* x (expt 2 k)) n)
		(* (near x n) (expt 2 k))))
  :rule-classes ())

(defun near-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (near x n) (near y n)) 2)
    (expt 2 (expo y))))

(in-theory (disable near-witness))

(defthm near-near-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near x n) (near y n))))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)
		  (exactp (near-witness x y n) (1+ n))))
  :rule-classes ())

(defthm near-near
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (<= (near y k) (near x k)))
  :rule-classes ())

(defthm near-est
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())

(defthm near-a-a
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ())

(defthm near-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near x n) a))
  :rule-classes ())

(defthm near-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near x n) a))
  :rule-classes ())

(defthm near-exact
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (near x n) (1- n)))
  :rule-classes ())

(defthm near-power-a
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm near-power-b
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm near-trunc
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ())


;;;**********************************************************************
;;;                           STICKY
;;;**********************************************************************

(defun sticky (x n)
  (cond ((= n 1)
	 (* (sgn x) (expt 2 (expo x))))
	((exactp x (1- n))
	 x)
	(t
	 (+ (trunc x (1- n))
	    (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(in-theory (disable sticky))

(defthm sticky-pos
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (> (sticky x n) 0))
  :rule-classes ())

(defthm sticky-neg
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (sticky (- x) n) (- (sticky x n))))
  :rule-classes ())

(defthm sticky-shift
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (sticky (* (expt 2 k) x) n)
		(* (expt 2 k) (sticky x n))))
  :rule-classes ())

(defthm sticky-exactp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
  :rule-classes ())

(defthm sticky-exactp-n-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (iff (exactp (sticky x n) (1- n))
		  (exactp x (1- n))))
  :rule-classes ())

(defthm expo-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ())

(defthm trunc-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (trunc (sticky x n) m)
		(trunc x m)))
  :rule-classes ())

(defthm away-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ())

(defthm near-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ())

(defthm sticky-sticky
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ())

(defthm sticky-plus
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ())

(defthm sticky-minus
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ())

(defthm sticky-lemma
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ())


;;;**********************************************************************
;;;                              ODD
;;;**********************************************************************

(defun odd (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x)))))
    (if (evenp z)
	(* (sgn x) (1+ z) (expt 2 (- (1+ (expo x)) n)))
      (* (sgn x) z (expt 2 (- (1+ (expo x)) n))))))

(in-theory (disable odd))

(defthm odd-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (odd x n) 0))
  :rule-classes ())

(defthm odd>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (odd x n) (trunc x n)))
  :rule-classes ())

(defthm odd-rewrite
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (equal (odd x n)
		    (let ((z (fl (* (expt 2 (- (1- n) (expo x))) x))))
		      (if (evenp z)
			  (* (1+ z) (expt 2 (- (1+ (expo x)) n)))
			(* z (expt 2 (- (1+ (expo x)) n)))))))
  :rule-classes ())

(defthm odd-other
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (odd x n)
		(+ (trunc x (1- n))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ())

(defthm expo-odd
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (equal (expo (odd x n)) (expo x))))

(defthm exactp-odd
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (exactp (odd x n) n))
  :rule-classes ())

(defthm not-exactp-odd
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (not (exactp (odd x n) (1- n))))
  :rule-classes ())

(defthm trunc-odd
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (> n m))
	     (= (trunc (odd x n) m)
		(trunc x m)))
  :rule-classes ())

(defun kp (k x y)
  (+ k (- (expo (+ x y)) (expo y))))

(defthm odd-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (> x 0)
		  (> y 0)
		  (> k 1)
		  (> (+ (1- k) (- (expo x) (expo y))) 0)
		  (exactp x (+ (1- k) (- (expo x) (expo y)))))
	     (= (+ x (odd y k))
		(odd (+ x y) (kp k x y))))
  :rule-classes ())

(defthm trunc-trunc-odd
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (trunc x k) (trunc (odd y m) k)))
  :rule-classes ())

(defthm away-away-odd
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (away x k) (away (odd y m) k)))
  :rule-classes ())

(defthm near-near-odd
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (near x k) (near (odd y m) k)))
  :rule-classes ())


;;;**********************************************************************
;;;                         IEEE Rounding
;;;**********************************************************************

(defun inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defun minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defun ieee-mode-p (mode)
  (member mode '(trunc inf minf near)))

(defun rnd (x mode n)
  (case mode
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))))

(defthm expo-rnd
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (= (expo (rnd x mode n))
		(expo x)))
  :rule-classes ())

(defthm rnd-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode))
	     (> (rnd x mode n) 0))
  :rule-classes ())

(defthm rnd-shift
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ())

(defun flip (m)
  (case m
    (inf 'minf)
    (minf 'inf)
    (t m)))

(defthm rnd-flip
    (implies (and (rationalp x)
		  (ieee-mode-p m)
		  (integerp n)
		  (> n 0))
	     (= (rnd (- x) (flip m) n)
		(- (rnd x m n))))
  :rule-classes ())

(defun rnd-const (e mode n)
  (case mode
    (near (expt 2 (- e n)))
    (inf (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defthm rnd-const-thm
    (implies (and (ieee-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
		(if (and (eql mode 'near)
			 (exactp x (1+ n))
			 (not (exactp x n)))
		    (trunc (+ x (rnd-const (expo x) mode n)) (1- n))
		  (trunc (+ x (rnd-const (expo x) mode n)) n))))
  :rule-classes ())

(defthm rnd-sticky
    (implies (and (ieee-mode-p mode)
		  (rationalp x) (> x 0)
		  (integerp k) (> k 0)
		  (integerp n) (> n (1+ k)))
	     (= (rnd x mode k)
		(rnd (sticky x n) mode k)))
  :rule-classes ())


