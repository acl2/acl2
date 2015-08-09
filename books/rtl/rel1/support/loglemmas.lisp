;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "logdefs")

(local
(defun log-induct (x y)
  (if (and (integerp x) (>= x 0)
	   (integerp y) (>= y 0))
      (if (or (= x 0) (= y 0))
	  ()
	(log-induct (fl (/ x 2)) (fl (/ y 2))))
    ())))

(defthm BIT-BASIC-A
    (implies (and (integerp x) (>= x 0))
	     (= (logand x 0)
		0))
  :rule-classes ())

(defthm BIT-BASIC-B
    (implies (and (integerp x) (>= x 0))
	     (= (logior x 0)
		x))
  :rule-classes ())

(defthm BIT-BASIC-C
    (implies (and (integerp x)
		  (integerp y))
	     (= (logand x y) (logand y x)))
  :rule-classes ())

(defthm BIT-BASIC-D
    (implies (and (integerp x)
		  (integerp y))
	     (= (logior x y) (logior y x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-c (x (lognot x)) (y (lognot y)))))))

(local
(defun log-induct-3 (x y z)
  (if (and (integerp x) (>= x 0)
	   (integerp y) (>= y 0)
	   (integerp z) (>= z 0))
      (if (or (= x 0) (= y 0) (= z 0))
	  ()
	(log-induct-3 (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    ())))

(defthm LOGAND-FL-REWRITE
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (fl (* 1/2 (logand x y)))
		    (logand (fl (/ x 2)) (fl (/ y 2)))))
  :hints (("Goal" :use ((:instance logand-fl)))))

(defthm LOGAND-REM-REWRITE
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (rem (logand x y) 2)
		    (logand (rem x 2) (rem y 2))))
  :hints (("Goal" :use ((:instance logand-rem)))))

(defthm LOGAND-NAT-REWRITE
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (>= (logand x y) 0))
  :hints (("Goal" :use ((:instance logand-nat (i x) (j y))))))

(local
 (defthm fl-rem-equal
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (= (fl (/ x 2)) (fl (/ y 2)))
		  (= (rem x 2) (rem y 2)))
	     (= x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n 2))
			(:instance rem-fl (m y) (n 2)))))))

(local
(defthm bit-basic-e-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (EQUAL (LOGAND (LOGAND (REM X 2) (REM Y 2))
			    (REM Z 2))
		    (LOGAND (REM X 2)
			    (LOGAND (REM Y 2) (REM Z 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance rem012 (x z)))))))

(defthm BIT-BASIC-E
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand (logand x y) z)
		(logand x (logand y z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2.1" :use ((:instance bit-basic-e-1)
				  (:instance fl-rem-equal
					      (x (logand (logand x y) z))
					      (y (logand x (logand y z))))))))

(in-theory (disable logior))

(local
(defthm bit-basic-f-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (EQUAL (LOGIOR (LOGIOR (REM X 2) (REM Y 2))
			    (REM Z 2))
		    (LOGIOR (REM X 2)
			    (LOGIOR (REM Y 2) (REM Z 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance rem012 (x z)))))))

(local
(defthm logior-fl-rewrite
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (fl (* 1/2 (logior x y)))
		    (logior (fl (/ x 2)) (fl (/ y 2)))))
  :hints (("Goal" :use ((:instance logior-fl (i x) (j y)))))))

(defthm LOGIOR-REM-REWRITE
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (rem (logior x y) 2)
		    (logior (rem x 2) (rem y 2))))
  :hints (("Goal" :use ((:instance logior-rem (i x) (j y))))))

(defthm LOGIOR-NAT-REWRITE
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (>= (logior x y) 0))
  :hints (("Goal" :use ((:instance logior-nat (i x) (j y))))))

(defthm LOGIOR-0
    (implies (integerp x)
	     (equal (logior x 0) x))
  :hints (("Goal" :in-theory (enable logior))))

(defthm LOGIOR-0-2
    (implies (integerp x)
	     (equal (logior 0 x) x))
  :hints (("Goal" :in-theory (enable logior))))

(defthm BIT-BASIC-F
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logior (logior x y) z)
		(logior x (logior y z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2.1" :use ((:instance bit-basic-f-1)
				  (:instance fl-rem-equal
					      (x (logior (logior x y) z))
					      (y (logior x (logior y z))))))))

(local
(defthm bit-basic-g-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (equal (logior (rem x 2)
			    (logand  (rem y 2) (rem z 2)))
		    (logand (logior (rem x 2) (rem y 2))
			    (logior (rem x 2) (rem z 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance rem012 (x z)))))))

(local
(defthm bit-basic-g-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (equal (logand (logior (rem x 2) (rem y 2)) (rem x 2))
		    (rem x 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y)))))))

(local
(defthm logand-x-x-1
    (implies (and (integerp x) (>= x 0))
	     (equal (logand (rem x 2) (rem x 2)) (rem x 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012))))))

(defthm LOGAND-X-X
    (implies (and (integerp x) (>= x 0))
	     (equal (logand x x) x))
  :hints (("Goal" :induct (log-induct x x))
	  ("Subgoal *1/2.1" :use ((:instance logand-x-x-1)
				  (:instance fl-rem-equal (y (logand x x)))))))

(local
(defthm bit-basic-g-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (logand (logior x y) x)
		x))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct x y))
	  ("Subgoal *1/2.2" :use ((:instance bit-basic-g-2)
				  (:instance fl-rem-equal
					      (y (logand (logior x y) x))))))))

(defthm BIT-BASIC-G
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logior x (logand y z))
		(logand (logior x y) (logior x z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2.1" :use ((:instance bit-basic-g-1)
				  (:instance fl-rem-equal
					      (x (logior x (logand y z)))
					      (y (logand (logior x y) (logior x z))))))
	  ("Subgoal *1/1" :use ((:instance bit-basic-g-3)
				(:instance bit-basic-c (y (logior x z)))
				(:instance bit-basic-g-3 (y z))))))

(local
(defthm bit-basic-h-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (equal (logand (rem x 2)
			    (logior  (rem y 2) (rem z 2)))
		    (logior (logand (rem x 2) (rem y 2))
			    (logand (rem x 2) (rem z 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance rem012 (x z)))))))

(defthm BIT-BASIC-H
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand x (logior y z))
		(logior (logand x y) (logand x z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2.1" :use ((:instance bit-basic-h-1)
				  (:instance fl-rem-equal
					      (x (logand x (logior y z)))
					      (y (logior (logand x y) (logand x z))))))))

(local
(defun op-dist-induct (x y n)
  (if (and (integerp n) (>= n 0))
      (if  (= n 0)
	  (list x y)
	(op-dist-induct (fl (/ x 2)) (fl (/ y 2)) (1- n)))
    ())))

(defthm OR-DIST-A
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (< y (expt 2 n)))
	     (< (logior x y) (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/2" :use ((:instance logior-def (i x) (j y))
				(:instance rem012)
				(:instance rem012 (x y))))))

(local
(defthm or-dist-b-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (< y (expt 2 n)))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* 2 (logior (fl (* (expt 2 (1- n)) x))
				(fl (/ y 2))))
		   (logior (rem (* (expt 2 n) x) 2)
			   (rem y 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logior-def (i (* (expt 2 n) x)) (j y)))))))

(local
(defthm or-dist-b-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (< y (expt 2 n)))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* 2 (logior (* (expt 2 (1- n)) x)
				(fl (/ y 2))))
		   (rem y 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-b-1)
			(:instance fl-int (x (* (expt 2 (1- n)) x)))
			(:instance rem-2*i (i (* (expt 2 (1- n)) x))))))))

(local
(defthm or-dist-b-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (< y (expt 2 n))
		  (= (logior (* (expt 2 (1- n)) x)
			     (fl (/ y 2)))
		     (+ (* (expt 2 (1- n)) x)
			(fl (/ y 2)))))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x)
		   (* 2	(fl (/ y 2)))
		   (rem y 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-b-2))))))

(local
(defthm or-dist-b-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (< y (expt 2 n))
		  (= (logior (* (expt 2 (1- n)) x)
			     (fl (/ y 2)))
		     (+ (* (expt 2 (1- n)) x)
			(fl (/ y 2)))))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-b-3)
			(:instance rem-fl (m y) (n 2)))))))

(local
(defun or-dist-induct (y n)
  (if (and (integerp n) (>= n 0))
      (if (= n 0)
	  y
	(or-dist-induct (fl (/ y 2)) (1- n)))
    ())))

(defthm OR-DIST-B
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< y (expt 2 n)))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :induct (or-dist-induct y n))
	  ("Subgoal *1/2" :use ((:instance or-dist-b-4)))))

(local
(defthm or-dist-c-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(+ (* 2 (logior (* (expt 2 (1- n)) x)
				(* (expt 2 (1- n)) y)))
		   (logior (rem (* (expt 2 n) x) 2)
			   (rem (* (expt 2 n) y) 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logior-def (i (* (expt 2 n) x)) (j (* (expt 2 n) y))))))))

(local
(defthm or-dist-c-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* 2 (logior (* (expt 2 (1- n)) x)
			     (* (expt 2 (1- n)) y)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-c-1)
			(:instance rem-2*i (i (* (expt 2 (1- n)) x)))
			(:instance rem-2*i (i (* (expt 2 (1- n)) y))))))))

(local
(defthm or-dist-c-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (= (logior (* (expt 2 (1- n)) x)
			     (* (expt 2 (1- n)) y))
		     (* (expt 2 (1- n)) (logior x y))))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n)
		   (logior x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-c-2))))))

(defthm OR-DIST-C
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat n))
	  ("Subgoal *1/1" :use ((:instance or-dist-c-3)))))

(local
(defthm or-dist-d-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logior x y)
		(logior (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
				(rem x (expt 2 n)))
			(logior (* (expt 2 n) (fl (/ y (expt 2 n))))
				(rem y (expt 2 n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n (expt 2 n)))
			(:instance rem-fl (m y) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem<n (m y) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n)))
			(:instance or-dist-b (x (fl (/ x (expt 2 n)))) (y (rem x (expt 2 n))))
			(:instance or-dist-b (x (fl (/ y (expt 2 n)))) (y (rem y (expt 2 n)))))))))

(local
(defthm or-dist-d-2
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp c) (>= c 0)
		  (integerp d) (>= d 0))
	     (= (logior (logior a b) (logior c d))
		(logior (logior a c) (logior b d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-f (x (logior a b)) (y c) (z d))
			(:instance bit-basic-f (x a) (y b) (z c))
			(:instance bit-basic-d (x b) (y c))
			(:instance bit-basic-f (x a) (y c) (z b))
			(:instance bit-basic-f (x (logior a c)) (y b) (z d)))))))

(defthm FL-NONNEG
    (implies (and (integerp n)
		  (rationalp x)
		  (>= x 0))
	     (not (< (* (EXPT 2 N) (FL (* X (/ (EXPT 2 N))))) 0)))
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-pos (x n))
			(:instance n<=fl (x (* X (/ (EXPT 2 N)))) (n 0))))))

(local
(defthm or-dist-d-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logior x y)
		(logior (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
				(* (expt 2 n) (fl (/ y (expt 2 n)))))
			(logior (rem x (expt 2 n))
				(rem y (expt 2 n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n)))
			(:instance or-dist-d-1)
			(:instance or-dist-d-2
				   (a (* (expt 2 n) (fl (/ x (expt 2 n)))))
				   (b (rem x (expt 2 n)))
				   (c (* (expt 2 n) (fl (/ y (expt 2 n)))))
				   (d (rem y (expt 2 n)))))))))

(local
(defthm or-dist-d-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logior x y)
		(+ (* (expt 2 n)
		      (logior (fl (/ x (expt 2 n)))
			      (fl (/ y (expt 2 n)))))
		   (logior (rem x (expt 2 n))
			   (rem y (expt 2 n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-d-3)
			(:instance or-dist-c (x (fl (/ x (expt 2 n)))) (y (fl (/ y (expt 2 n)))))
			(:instance or-dist-b
				   (x (logior (fl (/ x (expt 2 n)))
					      (fl (/ y (expt 2 n)))))
				   (y (logior (rem x (expt 2 n))
					      (rem y (expt 2 n)))))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem<n (m y) (n (expt 2 n)))
			(:instance or-dist-a (x (rem x (expt 2 n))) (y (rem y (expt 2 n))))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n))))))))

(local
(defthm or-dist-d-5
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (rem (logior x y) (expt 2 n))
		(rem (logior (rem x (expt 2 n)) (rem y (expt 2 n)))
		     (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-d-4)
			(:instance rem+
				   (m (logior (rem x (expt 2 n)) (rem y (expt 2 n))))
				   (n (expt 2 n))
				   (a (logior (fl (/ x (expt 2 n)))
					      (fl (/ y (expt 2 n))))))
			(:instance n<=fl (x (/ x (expt 2 n))) (n 0))
			(:instance n<=fl (x (/ y (expt 2 n))) (n 0))
			(:instance logior-nat (i (fl (/ x (expt 2 n)))) (j (fl (/ y (expt 2 n)))))
			(:instance logior-nat (i (rem x (expt 2 n))) (j (rem y (expt 2 n))))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n))))))))

(defthm OR-DIST-D
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (rem (logior x y) (expt 2 n))
		(logior (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance or-dist-d-5)
			(:instance rem<
				   (m (logior (rem x (expt 2 n)) (rem y (expt 2 n))))
				   (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n)))
			(:instance logior-nat (i (rem x (expt 2 n))) (j (rem y (expt 2 n))))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem<n (m y) (n (expt 2 n)))
			(:instance or-dist-a (x (rem x (expt 2 n))) (y (rem y (expt 2 n))))))))

(local
(defthm and-dist-a-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (<= (logand (rem x 2) (rem y 2)) (rem x 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012)
			(:instance rem012 (x y)))))))

(defthm AND-DIST-A
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (<= (logand x y) x))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct x y))
	  ("Subgoal *1/2" :use ((:instance and-dist-a-1)
				(:instance rem-fl (m (logand x y)) (n 2))
				(:instance rem-fl (m x) (n 2))))))

(local
(defthm and-dist-b-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logand (* (expt 2 n) x) y)
		(* 2 (logand (* (expt 2 (1- n)) x)
			     (fl (/ y 2))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-def (x (* (expt 2 n) x)))
			(:instance rem-2*i (i (* (expt 2 (1- n)) x))))))))

(local
(defthm and-dist-b-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (= (logand (* (expt 2 (1- n)) x) (fl (/ y 2)))
		     (* (expt 2 (1- n)) (logand x (fl (/ (fl (/ y 2)) (expt 2 (1- n))))))))
	     (= (logand (* (expt 2 n) x) y)
		(* 2
		   (* (expt 2 (1- n))
		      (logand x
			      (fl (/ (fl (/ y 2)) (expt 2 (1- n)))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-b-1))))))

(local
(defthm and-dist-b-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (= (logand (* (expt 2 (1- n)) x) (fl (/ y 2)))
		     (* (expt 2 (1- n)) (logand x (fl (/ (fl (/ y 2)) (expt 2 (1- n))))))))
	     (= (logand (* (expt 2 n) x) y)
		(* 2
		   (* (expt 2 (1- n))
		      (logand x
			      (fl (/ y (expt 2 n))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-b-2)
			(:instance fl/int (x (/ y 2)) (n (expt 2 (1- n)))))))))

(defthm AND-DIST-B
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :induct (or-dist-induct y n))
	  ("Subgoal *1/2" :use ((:instance and-dist-b-3)))))

(local
(defthm and-dist-c-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0))
	     (= x (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
			  (rem x (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n (expt 2 n)))
			(:instance or-dist-b (x (fl (/ x (expt 2 n)))) (y (rem x (expt 2 n))))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n))))))))

(local
(defthm and-dist-c-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(logior (logand (* (expt 2 n) (fl (/ x (expt 2 n))))
				y)
			(logand (rem x (expt 2 n))
				y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-1)
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance bit-basic-h
				   (x y)
				   (y (* (expt 2 n) (fl (/ x (expt 2 n)))))
				   (z (rem x (expt 2 n))))
			(:instance bit-basic-c (x (* (expt 2 n) (fl (/ x (expt 2 n))))))
			(:instance bit-basic-c (x (rem x (expt 2 n))))
			(:instance bit-basic-c
				   (x (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
					      (rem x (expt 2 n))))))))))

(local
 (defthm and-dist-c-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(logior (* (expt 2 n)
			   (logand (fl (/ x (expt 2 n)))
				   (fl (/ y (expt 2 n)))))
			(logand (rem x (expt 2 n))
				y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-2)
			(:instance and-dist-b (x (fl (/ x (expt 2 n))))))))))

(local
(defthm and-dist-c-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(+ (* (expt 2 n)
		      (logand (fl (/ x (expt 2 n)))
			      (fl (/ y (expt 2 n)))))
		   (logand (rem x (expt 2 n))
			   y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-3)
			(:instance or-dist-b
				   (x (logand (fl (/ x (expt 2 n)))
					      (fl (/ y (expt 2 n)))))
				   (y (logand (rem x (expt 2 n))
					      y)))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance and-dist-a (x (rem x (expt 2 n)))))))))

(defthm AND-DIST-C
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-4)
			(:instance rem+
				   (m (logand (rem x (expt 2 n)) y))
				   (n (expt 2 n))
				   (a (logand (fl (/ x (expt 2 n))) (fl (/ y (expt 2 n))))))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance and-dist-a (x (rem x (expt 2 n))))
			(:instance rem< (m (logand (rem x (expt 2 n)) y)) (n (expt 2 n)))))))

(defthm AND-DIST-D
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c (x y) (y x))
			(:instance bit-basic-c)
			(:instance bit-basic-c (y (rem y (expt 2 n))))
			(:instance and-dist-a)
			(:instance rem< (m (logand x y)) (n (expt 2 n)))))))

(defthm BIT-DIST-A
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logand x y) n)
		(logand (bitn x n) (bitn y n))))
  :rule-classes ()
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/1" :use ((:instance logand-rem)
				(:instance bitn-alt-0)
				(:instance bitn-alt-0 (x y))
				(:instance bitn-alt-0 (x (logand x y)))))
	  ("Subgoal *1/2" :use ((:instance bitn-alt-pos (k n))
				(:instance bitn-alt-pos (k n) (x y))
				(:instance bitn-alt-pos (k n) (x (logand x y)))
				(:instance logand-fl)))))

(defthm BIT-DIST-B
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logior x y) n)
		(logior (bitn x n) (bitn y n))))
  :rule-classes ()
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/1" :use ((:instance logior-rem)
				(:instance bitn-alt-0)
				(:instance bitn-alt-0 (x y))
				(:instance bitn-alt-0 (x (logior x y)))))
	  ("Subgoal *1/2" :use ((:instance bitn-alt-pos (k n))
				(:instance bitn-alt-pos (k n) (x y))
				(:instance bitn-alt-pos (k n) (x (logior x y)))
				(:instance logior-fl)))))

(defthm AND-BITS-A
    (implies (and (integerp x) (>= x 0)
		  (integerp k) (>= k 0))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :induct (or-dist-induct x k))
	  ("Subgoal *1/1" :use ((:instance logand-def (y 1))
				(:instance rem012)
				(:instance bitn-alt-0)))
	  ("Subgoal *1/2" :use ((:instance logand-def (y (expt 2 k)))
				(:instance rem-2*i (i (expt 2 (1- k))))
				(:instance fl-int (x (expt 2 (1- k))))
				(:instance bitn-alt-pos)))))

(defthm AND-BITS-B
    (implies (and (integerp x) (>= x 0)
		  (integerp k) (>= k 0))
	     (= (logior x (expt 2 k))
		(+ x
		   (* (expt 2 k)
		      (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("Goal" :induct (or-dist-induct x k))
	  ("Subgoal *1/1" :use ((:instance logior-def (i x) (j 1))
				(:instance rem012)
				(:instance rem-fl (m x) (n 2))
				(:instance bitn-alt-0)))
	  ("Subgoal *1/2" :use ((:instance logior-def (i x) (j (expt 2 k)))
				(:instance rem-2*i (i (expt 2 (1- k))))
				(:instance rem-fl (m x) (n 2))
				(:instance fl-int (x (expt 2 (1- k))))
				(:instance bitn-alt-pos)))))

(local
 (defthm fl-2**n-1/2
    (implies (and (integerp n) (> n 0))
	     (= (fl (/ (1- (expt 2 n)) 2))
		(1- (expt 2 (1- n)))))
  :rule-classes ()))

(local
(defthm rem-2**n-1/2
    (implies (and (integerp n) (> n 0))
	     (= (rem (1- (expt 2 n)) 2)
		1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-2*i+1 (i (1- (expt 2 (1- n)))))
			(:instance rem012 (x (1- (expt 2 n)))))))))

(local
(defthm and-bits-c-<-0-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (> n 0)
		  (< x (expt 2 n)))
	     (= (logand x (- (expt 2 n) 1))
		x))
  :rule-classes ()
  :hints (("Goal" :induct (or-dist-induct x n))
	  ("Subgoal *1/2" :use ((:instance logand-def (y (1- (expt 2 n))))
				(:instance fl-2**n-1/2)
				(:instance rem-fl (m x) (n 2))
				(:instance rem012)
				(:instance rem-2**n-1/2))))))

(local
(defthm and-bits-c-<-0
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (> n 0)
		  (< x (expt 2 n)))
	     (= (logand x (- (expt 2 n) 1))
		(bits x (1- n) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-0-1)
			(:instance rem< (m x) (n (expt 2 n))))))))

(local
(defthm and-bits-c-<-pos-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* 2 (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-def (y (- (expt 2 n) (expt 2 k))))
			(:instance expt-monotone (n k) (m n))
			(:instance rem-2*i (i (- (expt 2 (1- n)) (expt 2 (1- k))))))))))

(local
(defthm and-bits-c-<-pos-2
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits (fl (/ x 2)) (- n 2) (1- k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-pos-1))))))

(local
(defthm and-bits-c-<-pos-3
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (fl (/ (rem (fl (/ x 2)) (expt 2 (1- n))) (expt 2 (1- k)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-pos-2))))))

(local
(defthm and-bits-c-<-pos-4
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (rem (fl (/ x 2)) (expt 2 (1- n)))
		(fl (/ x 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem< (m (fl (/ x 2))) (n (expt 2 (1- n))))
			(:instance fl-def (x (/ x 2))))))))

(local
(defthm and-bits-c-<-pos-5
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (fl (/ (fl (/ x 2)) (expt 2 (1- k)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-pos-3)
			(:instance and-bits-c-<-pos-4))))))

(local
(defthm and-bits-c-<-pos-6
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (fl (/ x (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-pos-5)
			(:instance fl/int (x (/ x 2)) (n (expt 2 (1- k)))))))))

(local
(defthm and-bits-c-<-pos-7
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n))
	     (= (fl (/ x (expt 2 k)))
		(bits x (1- n) k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem< (m x) (n (expt 2 n))))))))

(local
(defthm and-bits-c-<-pos
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-<-pos-6)
			(:instance and-bits-c-<-pos-7))))))

(local
(defun and-bits-induct (x n k)
  (if (and (integerp k) (>= k 0))
      (if (= k 0)
	  (list x n k)
	(and-bits-induct (fl (/ x 2)) (1- n) (1- k)))
    ())))

(local
(defthm and-bits-c-<
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (>= k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :induct (and-bits-induct x n k))
	  ("Subgoal *1/1" :use ((:instance and-bits-c-<-0)))
	  ("Subgoal *1/2" :use ((:instance and-bits-c-<-pos))))))

(local
(defthm and-bits-c-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(logand (rem x (expt 2 n)) (- (expt 2 n) (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-d (x (- (expt 2 n) (expt 2 k))) (y x))
			(:instance expt-monotone (n k) (m n))
			(:instance bit-basic-c (y (- (expt 2 n) (expt 2 k))))
			(:instance bit-basic-c (x (rem x (expt 2 n))) (y (- (expt 2 n) (expt 2 k)))))))))

(local
(defthm and-bits-c-2
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits (rem x (expt 2 n)) (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-1)
			(:instance and-bits-c-< (x (rem x (expt 2 n))))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n))))))))

(defthm AND-BITS-C
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c-2)
			(:instance rem-bits (y (rem x (expt 2 n))) (i n) (j k))
			(:instance rem-rem (a n) (b n))))))