(in-package "ACL2")

(local (include-book "../support/fadd/add3"))

(include-book "float")

(include-book "bits")


;;Three-Input Addition:

(defthm add3
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp y)
		  (>= y 0)
		  (integerp z)
		  (>= z 0))
	     (= (+ x y z)
		(+ (logxor x (logxor y z))
		   (* 2 (logior (logand x y)
				(logior (logand x z)
					(logand y z)))))))
  :rule-classes ())


;;Trailing One Prediction:

(defun sigm (a b c n)
  (if (= c 0)
      (comp1 (logxor a b) n)
    (logxor a b)))

(defun kap (a b c)
  (if (= c 0)
      (* 2 (logior a b))
    (* 2 (logand a b))))

(defun tau (a b c n)
  (comp1 (logxor (sigm a b c n) (kap a b c)) (1+ n)))

(defthm sigm-bnds
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp a)
		  (>= a 0)
		  (< a (expt 2 n))
		  (integerp b)
		  (>= b 0)
		  (< b (expt 2 n)))
	     (and (integerp (sigm a b c n))
		  (>= (sigm a b c n) 0)
		  (< (sigm a b c n) (expt 2 n))))
  :rule-classes ())

(defthm kap-bnds
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp a)
		  (>= a 0)
		  (< a (expt 2 n))
		  (integerp b)
		  (>= b 0)
		  (< b (expt 2 n)))
	     (and (integerp (kap a b c))
		  (>= (kap a b c) 0)
		  (< (kap a b c) (expt 2 (1+ n)))))
  :rule-classes ())

(defthm tau-bnds
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp a)
		  (>= a 0)
		  (< a (expt 2 n))
		  (integerp b)
		  (>= b 0)
		  (< b (expt 2 n)))
	     (and (integerp (tau a b c n))
		  (>= (tau a b c n) 0)
		  (< (tau a b c n) (expt 2 (1+ n)))))
  :rule-classes ())

(defthm stick-lemma
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp a)
		  (>= a 0)
		  (< a (expt 2 n))
		  (integerp b)
		  (>= b 0)
		  (< b (expt 2 n))
		  (integerp k)
		  (>= k 0)
		  (< k n)
		  (or (= c 0) (= c 1)))
	     (iff (= (rem (+ a b c) (expt 2 (1+ k))) 0)
		  (= (rem (tau a b c n) (expt 2 (1+ k))) 0)))
  :rule-classes ())


;;Leading One Prediction:

(defthm lop-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (= e (expo a))
		  (< (expo b) e)
		  (= lambda
		     (logior (* 2 (rem a (expt 2 e)))
			     (comp1 (* 2 b) (1+ e)))))
	     (or (= (expo (- a b)) (expo lambda))
		 (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())

(defun lamt (a b e)
  (logxor a (comp1 b (1+ e))))

(defun lamg (a b e)
  (logand a (comp1 b (1+ e))))

(defun lamz (a b e)
  (comp1 (logior a (comp1 b (1+ e))) (1+ e)))

(defun lam1 (a b e)
  (logand (bits (lamt a b e) e 2)
	  (logand (bits (lamg a b e) (1- e) 1)
		  (comp1 (bits (lamz a b e) (- e 2) 0) (1- e)))))

(defun lam2 (a b e)
  (logand (comp1 (bits (lamt a b e) e 2) (1- e))
	  (logand (bits (lamz a b e) (1- e) 1)
		  (comp1 (bits (lamz a b e) (- e 2) 0) (1- e)))))

(defun lam3 (a b e)
  (logand (bits (lamt a b e) e 2)
	  (logand (bits (lamz a b e) (1- e) 1)
		  (comp1 (bits (lamg a b e) (- e 2) 0) (1- e)))))

(defun lam4 (a b e)
  (logand (comp1 (bits (lamt a b e) e 2) (1- e))
	  (logand (bits (lamg a b e) (1- e) 1)
		  (comp1 (bits (lamg a b e) (- e 2) 0) (1- e)))))

(defun lam0 (a b e)
  (logior (lam1 a b e)
	  (logior (lam2 a b e)
		  (logior (lam3 a b e)
			  (lam4 a b e)))))

(defun lamb (a b e)
  (+ (* 2 (lam0 a b e))
     (comp1 (bitn (lamt a b e) 0) 1)))

(defthm lop-thm-3
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb a b e)))
		      (= (expo (- a b)) (1- (expo (lamb a b e)))))))
  :rule-classes ())
