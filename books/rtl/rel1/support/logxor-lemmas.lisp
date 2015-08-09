;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "logxor-def")

(include-book "loglemmas")

(defthm COMP1-COMP1
    (implies (and (integerp n)
		  (integerp x))
	     (= (comp1 (comp1 x n) n)
		x))
  :rule-classes ())

(local (defthm integerp-expt
    (implies (and (integerp n)
		  (>= n 0))
	     (integerp (expt 2 n)))
  :rule-classes ()))

(local (defthm fl-comp1-1
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (/ (comp1 x n) (expt 2 k))
		(+ (expt 2 (- n k))
		   (/ (- -1 x) (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a10)
		  :use ((:instance expo+ (m k) (n (- n k)))
			(:instance integerp-expt (n (- n k)))
			(:instance integerp-expt (n k))
			(:instance expt-pos (x k)))))))

(local (defthm fl=
    (implies (equal x y)
	     (equal (fl x) (fl y)))
  :rule-classes ()))

(local (defthm fl-comp1-2
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(fl (+ (expt 2 (- n k))
		       (/ (- -1 x) (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a10)
		  :use ((:instance fl-comp1-1)
			(:instance fl=
				   (x (/ (comp1 x n) (expt 2 k)))
				   (y (+ (expt 2 (- n k))
					 (/ (- -1 x) (expt 2 k))))))))))

(local (defthm fl-comp1-3
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(+ (expt 2 (- n k))
		   (fl (/ (- -1 x) (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a10)
		  :use ((:instance fl-comp1-2)
			(:instance fl+int (n (expt 2 (- n k))) (x (/ (- (- x) 1) (expt 2 k))))
			(:instance integerp-expt (n (- n k)))
			(:instance integerp-expt (n k))
			(:instance expt-pos (x k)))))))

(defthm FL-COMP1
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(comp1 (fl (/ x (expt 2 k))) (- n k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a10)
		  :use ((:instance fl-comp1-3)
			(:instance integerp-expt (n (- n k)))
			(:instance integerp-expt (n k))
			(:instance expt-pos (x k))
			(:instance floor-m+1 (m x) (n (expt 2 k)))))))

(local
(defthm rem=rem-1
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (= (- a (* n (fl (/ a n))))
		(- b (* n (fl (/ b n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m a))
			(:instance rem-fl (m b)))))))

(local
(defthm rem=rem-2
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (= (- a b) (* n (- (fl (/ a n)) (fl (/ b n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem=rem-1))))))

(local
(defthm hack-m10
    (implies (and (rationalp a) (rationalp b) (rationalp c) (> b 0) (= a (* b c)))
	     (= (/ a b) c))
  :rule-classes ()))

(local
(defthm rem=rem-3
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (= (/ (- a b) n) (- (fl (/ a n)) (fl (/ b n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem=rem-2)
			(:instance hack-m10 (a (- a b)) (b n) (c (- (fl (/ a n)) (fl (/ b n))))))))))

(local (defthm rem=rem
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (integerp (/ (- a b) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem=rem-3))))))

(local (defthm rem-comp1-1
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x))
	     (not (integerp (+ (expt 2 (1- n)) (- x) -1/2))))
  :rule-classes ()))

(local (defthm rem-comp1-2
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x))
	     (not (integerp (/ (- (comp1 x n) x) 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (1- n)) (n 1))
			(:instance rem-comp1-1))))))

(defthm REM-COMP1
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n)))
	     (not (= (rem (comp1 x n) 2)
		     (rem x 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-comp1-2)
			(:instance rem=rem (a (comp1 x n)) (b x) (n 2))))))

(local (defthm bitn-comp1-1
    (implies (= x y)
	     (= (rem x 2) (rem y 2)))
  :rule-classes ()))

(local (defthm bitn-comp1-2
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (rem (fl (/ (comp1 x n) (expt 2 k))) 2)
		(rem (comp1 (fl (/ x (expt 2 k))) (- n k)) 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-comp1)
			(:instance bitn-comp1-1
				   (x (fl (/ (comp1 x n) (expt 2 k))))
				   (y (comp1 (fl (/ x (expt 2 k))) (- n k)))))))))

(local (defthm bitn-comp1-3
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n))
		  (integerp k)
		  (>= k 0)
		  (< k n))
	     (< (/ x (expt 2 k)) (expt 2 (- n k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a2 a9 a8 *-strongly-monotonic)
		  :use ((:instance *-strongly-monotonic
				   (x (/ (expt 2 k)))
				   (y x)
				   (y+ (expt 2 n)))
			(:instance expo+ (m (- n k)) (n k))
			(:instance expt-pos (x k)))))))

(local (defthm bitn-comp1-4
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n))
		  (integerp k)
		  (>= k 0)
		  (< k n))
	     (not (= (rem (fl (/ (comp1 x n) (expt 2 k))) 2)
		     (rem (fl (/ x (expt 2 k))) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1)
		  :use ((:instance rem-comp1 (x (fl (/ x (expt 2 k)))) (n (- n k)))
			(:instance bitn-comp1-3)
			(:instance fl-def (x (/ x (expt 2 k))))
			(:instance expt-pos (x k))
			(:instance bitn-comp1-2))))))

(defthm BITN-COMP1
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n))
		  (integerp k)
		  (>= k 0)
		  (< k n))
	     (not (= (bitn (comp1 x n) k)
		     (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-comp1-4)
			(:instance bitn-def)
			(:instance bitn-def (x (comp1 x n)))))))

(local (defthm logxor-rewrite-1
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logior (logand (fl (/ x 2)) (comp1 (fl (/ y 2)) (1- n)))
			(logand (fl (/ y 2)) (comp1 (fl (/ x 2)) (1- n))))
		(logior (logand (fl (/ x 2)) (fl (/ (comp1 y n) 2)))
			(logand (fl (/ y 2)) (fl (/ (comp1 x n) 2))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1)
		  :use ((:instance fl-comp1 (k 1))
			(:instance fl-comp1 (k 1) (x y)))))))

(local (defthm integerp-comp1
    (implies (and (integerp n)
		  (integerp x)
		  (> n 0))
	     (integerp (comp1 x n)))
  :rule-classes (:type-prescription)))

(local (defthm comp1-nat
    (implies (and (integerp n) (> n 0)
		  (integerp x) (< x (expt 2 n)))
	     (not (< (comp1 x n) 0)))))

(local (defthm logxor-rewrite-2
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logior (logand (fl (/ x 2)) (fl (/ (comp1 y n) 2)))
			(logand (fl (/ y 2)) (fl (/ (comp1 x n) 2))))
		(logior (fl (/ (logand x (comp1 y n)) 2))
			(fl (/ (logand y (comp1 x n)) 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand-fl-rewrite comp1)
		  :use ((:instance logand-fl (y (comp1 y n)))
			(:instance logand-fl (x y) (y (comp1 x n))))))))

(local (defthm logxor-rewrite-3
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logior (logand (fl (/ x 2)) (comp1 (fl (/ y 2)) (1- n)))
			(logand (fl (/ y 2)) (comp1 (fl (/ x 2)) (1- n))))
		(logior (fl (/ (logand x (comp1 y n)) 2))
			(fl (/ (logand y (comp1 x n)) 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logxor-rewrite-1)
			(:instance logxor-rewrite-2))))))

(local (defthm logxor-rewrite-4
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logior (fl (/ (logand x (comp1 y n)) 2))
			(fl (/ (logand y (comp1 x n)) 2)))
		(fl (/ (logior (logand x (comp1 y n))
			       (logand y (comp1 x n)))
		       2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logior-fl
				   (i (logand x (comp1 y n)))
				   (j (logand y (comp1 x n)))))))))

(local (defthm logxor-rewrite-5
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logior (logand (fl (/ x 2)) (comp1 (fl (/ y 2)) (1- n)))
			(logand (fl (/ y 2)) (comp1 (fl (/ x 2)) (1- n))))
		(fl (/ (logior (logand x (comp1 y n))
			       (logand y (comp1 x n)))
		       2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logxor-rewrite-3)
			(:instance logxor-rewrite-4))))))

(local (defthm logxor-rewrite-6
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n))
		  (= (logxor (fl (/ x 2)) (fl (/ y 2)))
		     (logior (logand (fl (/ x 2)) (comp1 (fl (/ y 2)) (1- n)))
			     (logand (fl (/ y 2)) (comp1 (fl (/ x 2)) (1- n))))))
	     (= (fl (/ (logxor x y) 2))
		(fl (/ (logior (logand x (comp1 y n))
			       (logand y (comp1 x n)))
		       2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logxor-rewrite-5)
			(:instance logxor-fl (i x) (j y)))))))

(local (defthm logxor-rewrite-7
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n)))
	     (= (rem (comp1 x n) 2)
		(comp1 (rem x 2) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-comp1-4 (k 0))
			(:instance rem012)
			(:instance rem012 (x (comp1 x n))))))))

(local (defthm logxor-rewrite-8
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (rem (logxor x y) 2)
		(logior (logand (rem x 2) (comp1 (rem y 2) 1))
			(logand (rem y 2) (comp1 (rem x 2) 1)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logxor)
		  :use ((:instance logxor-rem (i x) (j y))
			(:instance rem012)
			(:instance rem012 (x y)))))))

(local (defthm logxor-rewrite-9
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (rem (logxor x y) 2)
		(logior (logand (rem x 2) (rem (comp1 y n) 2))
			(logand (rem y 2) (rem (comp1 x n) 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1 logxor)
		  :use ((:instance logxor-rewrite-8)
			(:instance logxor-rewrite-7)
			(:instance logxor-rewrite-7 (x y)))))))

(local (defthm logxor-rewrite-10
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (rem (logxor x y) 2)
		(logior (rem (logand x (comp1 y n)) 2)
			(rem (logand y (comp1 x n)) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logxor)
		  :use ((:instance logxor-rewrite-9)
			(:instance logand-rem (y (comp1 y n)))
			(:instance logand-rem (x y) (y (comp1 x n))))))))

(local (defthm logxor-rewrite-11
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (rem (logxor x y) 2)
		(rem (logior (logand x (comp1 y n))
			     (logand y (comp1 x n)))
		     2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logxor)
		  :use ((:instance logxor-rewrite-10)
			(:instance logior-rem (i (logand x (comp1 y n))) (j (logand y (comp1 x n)))))))))

(local (defthm logxor-rewrite-12
    (implies (and (integerp n) (> n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n))
		  (= (logxor (fl (/ x 2)) (fl (/ y 2)))
		     (logior (logand (fl (/ x 2)) (comp1 (fl (/ y 2)) (1- n)))
			     (logand (fl (/ y 2)) (comp1 (fl (/ x 2)) (1- n))))))
	     (= (logxor x y)
		(logior (logand x (comp1 y n))
			(logand y (comp1 x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logxor)
		  :use ((:instance logxor-rewrite-6)
			(:instance logxor-rewrite-11)
			(:instance rem-fl
				   (m (logxor x y))
				   (n 2))
			(:instance logxor-nat (i x) (j y))
			(:instance rem-fl
				   (m (logior (logand x (comp1 y n))
					      (logand y (comp1 x n))))
				   (n 2)))))))

(defthm LOGXOR-0
    (implies (integerp y)
	     (equal (logxor 0 y) y))
  :hints (("Goal" :in-theory (enable logior logand))))

(defthm LOGXOR-0-2
    (implies (integerp x)
	     (equal (logxor x 0) x))
  :hints (("Goal" :in-theory (enable logior logand))))

(local
(defun logxor-induct (x y n)
  (if (and (integerp n) (>= n 1))
      (if (= n 1)
	  (list x y)
	(logxor-induct (fl (/ x 2)) (fl (/ y 2)) (1- n)))
    ())))

(local (defthm x01
    (implies (and (integerp x)
		  (>= x 0)
		  (< x 2))
	     (or (= x 0) (= x 1)))
  :rule-classes ()))

(defthm LOGXOR-REWRITE
    (implies (and (integerp n) (>= n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logxor x y)
		(logior (logand x (comp1 y n))
			(logand y (comp1 x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1 logxor)
		  :induct (logxor-induct x y n))
	  ("Subgoal *1/2" :use (logxor-rewrite-12))
	  ("Subgoal *1/1" :in-theory (enable comp1)
			  :use ((:instance x01)
				(:instance x01 (x y))
				(:instance fl-comp1 (x 0) (k 1))))))

(defthm LOGXOR-COMMUTATIVE
    (implies (and (integerp x)
		  (integerp y))
	     (= (logxor x y) (logxor y x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-c
				   (x (LOGIOR (+ -1 (* -1 Y)) X))
				   (y (LOGIOR (+ -1 (* -1 X)) Y)))))))

(local
(defun log-induct-3 (x y z)
  (if (and (integerp x) (>= x 0)
	   (integerp y) (>= y 0)
	   (integerp z) (>= z 0))
      (if (or (= x 0) (= y 0) (= z 0))
	  ()
	(log-induct-3 (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    ())))

(local (defthm logxor-fl-rewrite
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (fl (* 1/2 (logxor x y)))
		    (logxor (fl (/ x 2)) (fl (/ y 2)))))
  :hints (("Goal" :use ((:instance logxor-fl (i x) (j y)))))))

(local (defthm logxor-rem-rewrite
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (rem (logxor x y) 2)
		    (logxor (rem x 2) (rem y 2))))
  :hints (("Goal" :use ((:instance logxor-rem (i x) (j y)))))))

(local (defthm logxor-nat-rewrite
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (>= (logxor x y) 0))
  :hints (("Goal" :use ((:instance logxor-nat (i x) (j y)))))))

(local (defthm fl-rem-equal
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (= (fl (/ x 2)) (fl (/ y 2)))
		  (= (rem x 2) (rem y 2)))
	     (= x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n 2))
			(:instance rem-fl (m y) (n 2)))))))

(local
(defthm logxor-assoc-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (EQUAL (LOGXOR (LOGXOR (REM X 2) (REM Y 2))
			    (REM Z 2))
		    (LOGXOR (REM X 2)
			    (LOGXOR (REM Y 2) (REM Z 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance rem012 (x z)))))))

(defthm LOGXOR-ASSOC
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logxor (logxor x y) z)
		(logxor x (logxor y z))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logxor)
		  :induct (log-induct-3 x y z))
	  ("Subgoal *1/2.1" :use ((:instance logxor-assoc-1)
				  (:instance fl-rem-equal
					      (x (logxor (logxor x y) z))
					      (y (logxor x (logxor y z))))))))

(local
(defthm logxor-x-x-1
    (implies (and (integerp x) (>= x 0))
	     (equal (logxor (rem x 2) (rem x 2)) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012))))))

(local
(defun log-induct (x y)
  (if (and (integerp x) (>= x 0)
	   (integerp y) (>= y 0))
      (if (or (= x 0) (= y 0))
	  ()
	(log-induct (fl (/ x 2)) (fl (/ y 2))))
    ())))

(defthm LOGXOR-X-X
    (implies (and (integerp x) (>= x 0))
	     (equal (logxor x x) 0))
  :hints (("Goal" :in-theory (disable logxor)
		  :induct (log-induct x x))
	  ("Subgoal *1/2.1" :use ((:instance logxor-x-x-1)
				  (:instance fl-rem-equal (x 0) (y (logxor x x)))))))

(local
(defun op-dist-induct (x y n)
  (if (and (integerp n) (>= n 0))
      (if  (= n 0)
	  (list x y)
	(op-dist-induct (fl (/ x 2)) (fl (/ y 2)) (1- n)))
    ())))

(in-theory (disable logxor))

(defthm BITN-LOGXOR
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logxor x y) n)
		(logxor (bitn x n) (bitn y n))))
  :rule-classes ()
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/1" :use ((:instance logxor-rem (i x) (j y))
				(:instance bitn-alt-0)
				(:instance bitn-alt-0 (x y))
				(:instance bitn-alt-0 (x (logxor x y)))))
	  ("Subgoal *1/2" :use ((:instance bitn-alt-pos (k n))
				(:instance bitn-alt-pos (k n) (x y))
				(:instance bitn-alt-pos (k n) (x (logxor x y)))
				(:instance logxor-fl (i x) (j y))))))

(defthm LOGXOR<2**N
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (< y (expt 2 n)))
	     (< (logxor x y) (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/2" :use ((:instance logxor-def)
				(:instance rem012)
				(:instance rem012 (x y))))))

(defthm COMP1-BNDS
    (implies (and (integerp n) (> n 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (and (< (comp1 x n) (expt 2 n))
		  (>=  (comp1 x n) 0)))
  :rule-classes ())