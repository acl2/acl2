;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "divsqrt")

(include-book "logxor-lemmas")

(include-book "rnd")

(local (defun nat-induct (k)
  (if (and (integerp k) (>= k 0))
      (if (= k 0)
	  0
	(nat-induct (1- k)))
    0)))

(defthm integerp-expt
    (implies (and (integerp n)
		  (>= n 0))
	     (integerp (expt 2 n))))

(local (defthm ahack1
    (implies (and (integerp m)
		  (integerp x)
		  (integerp k)
		  (>= m 0))
	     (INTEGERP (+ X (* -1 (EXPT 2 M)) (* K (EXPT 2 M)))))
  :rule-classes ()))

(local (defthm ahack2
    (implies (and (integerp m)
		  (integerp x)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (>= m 0))
	     (>= (+ X (* K (EXPT 2 M)))
                 0))
  :rule-classes ()))

(local (defthm ahack3
    (implies (and (integerp m)
		  (integerp x)
		  (integerp k)
		  (>= x 0)
		  (>= k 1)
		  (>= m 0))
	     (>= (+ X (* -1 (EXPT 2 M)) (* K (EXPT 2 M)))
                 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a14)
		  :use ((:instance ahack2 (k (1- k))))))))

(defthm BIT+*K
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (>= x 0)
		  (> m n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n)))
  :rule-classes ()
  :hints (("Goal" :induct (nat-induct k))
	  ("Subgoal *1/2" :use ((:instance integerp-expt (n m))
				(:instance bit+-b (x (+ x (* (1- k) (expt 2 m)))))))
;;	  ("Subgoal *1/2.2" :use (ahack1))  ;; RBK:
	  ("Subgoal *1/2'''" :use (ahack3))))  ;; RBK:

(in-theory (disable rem expt-pos))

(defthm BITN-REM
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (> k j))
	     (equal (bitn (rem x (expt 2 k)) j)
		    (bitn x j)))
  :hints (("Goal" :use ((:instance rem-fl (m x) (n (expt 2 k)))
			(:instance n<=fl (n 0) (x (* X (EXPT 2 (* -1 K)))))
			(:instance expt-pos (x (- k)))
			(:instance rem>=0 (m x) (n (expt 2 k)))
			(:instance bit+*k
				   (x (rem x (expt 2 k)))
				   (m k)
				   (n j)
				   (k (fl (/ x (expt 2 k)))))))))

(local (defthm bitn-rewrite
    (implies (and (integerp x)
		  (integerp k)
		  (>= x 0)
		  (>= k 0))
	     (equal (bitn x k)
		    (rem (fl (/ x (expt 2 k)))
			 2)))
  :hints (("Goal" :use (bitn-def)))))

(local (in-theory (disable bitn-rewrite)))

(defthm BITN-N+K
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0))
	     (= (bitn (* x (expt 2 k)) (+ n k))
		(bitn x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-rewrite)
		  :use ((:instance expo+ (m k))))))

(local (defthm rem-n+1-1
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (< (/ (rem a (expt 2 (1+ n))) (expt 2 n))
		2))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable *-weakly-monotonic)
		  :use ((:instance rem<n (m a) (n (expt 2  (1+ n))))
			(:instance expt-pos (x (1+ n)))
			(:instance expt-pos (x n))
			(:instance *-weakly-monotonic
				   (x (expt 2 n))
				   (y 2)
				   (y+ (/ (rem a (expt 2 (1+ n))) (expt 2 n)))))))))

(local (defthm rem-n+1-2
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (< (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n)))
		2))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-1)))))

(local (defthm rem-n+1-3
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (<= 0 (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem>=0 (m a) (n (expt 2 (1+ n))))
			(:instance expt-pos (x (1+ n)))
			(:instance expt-pos (x n)))))))

(local (defthm rem-n+1-4
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (or (= (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n))) 0)
		 (= (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n))) 1)))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-2
			rem-n+1-3)))))

(local (defthm rem-n+1-5
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (= (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n)))
		(rem (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n))) 2)))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-4)))))

(local (defthm rem-n+1-6
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (= (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n)))
		(bitn (rem a (expt 2 (1+ n))) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-5
			(:instance rem>=0 (m a) (n (expt 2 (1+ n))))
			(:instance bitn-def (x (rem a (expt 2 (1+ n)))) (k n)))))))

(local (defthm rem-n+1-7
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (>= n 0))
	     (= (fl (/ (rem a (expt 2 (1+ n))) (expt 2 n)))
		(bitn a n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-6
			(:instance bitn-rem (x a) (k (1+ n)) (j n)))))))

(local (defthm rem-n+1-8
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (> n 0))
	     (= (rem (rem a (expt 2 (1+ n))) (expt 2 n))
		(rem a (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-rem (x a) (a (1+ n)) (b n)))))))

(defthm REM-N+1
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (> n 0))
	     (= (rem a (expt 2 (1+ n)))
		(+ (* (bitn a n) (expt 2 n))
		   (rem a (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1-8
			rem-n+1-7
			(:instance rem>=0 (m a) (n (expt 2 (1+ n))))
			(:instance rem-fl (m (rem a (expt 2 (1+ n)))) (n (expt 2 n)))))))

(defthm INTEGERP-COMP1
    (implies (and (integerp n)
		  (integerp x)
		  (>= n 0))
	     (integerp (comp1 x n)))
  :rule-classes (:type-prescription))

(defthm REM-N-N+1
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (> n 0))
	     (iff (= (rem a (expt 2 (1+ n))) 0)
		  (and (= (rem a (expt 2 n)) 0)
		       (= (bitn a n) 0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-n+1)
			(:instance rem>=0 (m a) (n (expt 2 n)))
			(:instance bitn-0-1 (x a))))))

(defthm REM-X-Y-X-2
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp y)
		  (>= y 0))
	     (iff (= (rem (+ x y) 2) (rem x 2))
		  (= (rem y 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012 (x y))
			(:instance rem+rem (a x) (b y) (n 2))
			(:instance rem+1-2)))))

(defthm BITN-N+K
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0))
	     (= (bitn (* x (expt 2 k)) (+ n k))
		(bitn x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-rewrite)
		  :use ((:instance expo+ (m k))))))

(defthm REM-M=N
    (implies (and (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n 0)
		  (< m (* 2 n))
		  (= (rem m n) 0))
	     (= m n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem<)
			(:instance rem< (m (- m n)))
			(:instance rem+ (m (- m n)) (a 1))))))


(defthm BITN-0-LOGXOR-+
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp b)
		  (>= b 0))
	     (= (bitn (+ a b) 0)
		(bitn (logxor a b) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-rewrite)
		  :use ((:instance rem012 (x a))
			(:instance rem012 (x b))
			(:instance bitn-logxor (x a) (y b) (n 0))
			(:instance rem+rem (n 2))
			(:instance rem+rem (n 2) (a (rem b 2)) (b a))))))

(defthm BITS-REWRITE
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (< x (expt 2 (1+ n))))
	     (equal (bits x n 0)
		    x))
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance rem< (m x) (n (expt 2 (1+ n))))))))

(defthm BITS-0-REM
    (implies (and (integerp x)
		  (integerp n)
		  (>= n 0))
	     (equal (bits x n 0)
		    (rem x (expt 2 (1+ n)))))
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance integerp-expt (n (1+ n)))
			(:instance integerp-rem (m x) (n (expt 2 (1+ n))))))))

(in-theory (disable bits-0-rem))

(local (defthm hack6
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp c)
		  (rationalp ap)
		  (rationalp k)
		  (= (+ a b) c)
		  (= (+ ap (* k b)) (* k c)))
	     (= ap (* k a)))
    :rule-classes ()))

(defthm REM**
    (implies (and (integerp m)
		  (>= m 0)
		  (integerp n)
		  (> n 0)
		  (integerp k)
		  (> k 0))
	     (= (rem (* k m) (* k n))
		(* k (rem m n))))
  :rule-classes ()
  :hints (("Goal" :use (rem-fl
			(:instance hack6
				   (a (rem m n)) (b (* n (fl (/ m n)))) (c m) (ap (rem (* k m) (* k n))))
			(:instance rem-fl (m (* k m)) (n (* k n)))))))

(local (defthm rem-expo-1
    (implies (and (integerp x)
		  (> x 0))
	     (= (fl (/ x (expt 2 (expo x))))
		1))
  :rule-classes ()
  :hints (("Goal" :use (expo-upper-bound
			expo-lower-bound
			(:instance *-weakly-monotonic
				   (x (expt 2 (expo x)))
				   (y 2)
				   (y+ (* x (expt 2 (- (expo x))))))
			(:instance fl-unique (x (/ x (expt 2 (expo x)))) (n 1))
			(:instance expo-monotone (x 1) (y x)))))))

(defthm REM-EXPO
    (implies (and (integerp x)
		  (> x 0))
	     (= (rem x (expt 2 (expo x)))
		(- x (expt 2 (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use (rem-expo-1
			(:instance rem-fl (m x) (n (expt 2 (expo x))))
			(:instance expo-monotone (x 1) (y x))))))

(defmacro local-defthm (&rest body)
  (list 'local (cons 'defthm body)))

(local-defthm rem-minus-rem-1
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a b)
		  (>= b 0)
		  (> n 0))
	     (= (- a (rem b n))
		(+ (- a b) (* n (fl (/ b n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m b))))))

(local-defthm hack16
    (implies (= x y)
	     (= (rem x n) (rem y n)))
  :rule-classes ())

(local-defthm rem-minus-rem-2
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a b)
		  (>= b 0)
		  (> n 0))
	     (= (rem (- a (rem b n)) n)
		(rem (+ (- a b) (* n (fl (/ b n)))) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-minus-rem-1
			(:instance hack16 (x (- a (rem b n))) (y (+ (- a b) (* n (fl (/ b n))))))))))

(defthm REM-MINUS-REM
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a b)
		  (>= b 0)
		  (> n 0))
	     (= (rem (- a (rem b n)) n)
		(rem (- a b) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-minus-rem-2
			(:instance rem+ (m (- a b)) (a (fl (/ b n))))))))

(defthm EXPT>=1
    (implies (and (integerp n)
		  (>= n 0))
	     (and (integerp (expt 2 n))
		  (>= (expt 2 n) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-pos (x n))
			integerp-expt))))

(local-defthm rem-comp1-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (comp1 x m)
		(+ (comp1 x n) (* (expt 2 n) (1- (expt 2 (- m n)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- m n)))))))

(local-defthm rem-comp1-2
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (rem (comp1 x m) (expt 2 n))
		(rem (+ (comp1 x n) (* (expt 2 n) (1- (expt 2 (- m n))))) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use (rem-comp1-1))))

(local-defthm rem-comp1-3
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (rem (comp1 x m) (expt 2 n))
		(rem (comp1 (rem x (expt 2 n)) m) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt)
		  :use ((:instance rem-minus-rem (a (1- (expt 2 m))) (b x) (n (expt 2 n)))
			(:instance integerp-expt (n (- m n)))
			(:instance expt-pos (x (- m n)))
			(:instance expt-monotone)
			(:instance integerp-expt)
			(:instance integerp-expt (n m))
			(:instance comp1-bnds (n m))
			(:instance rem+ (m (comp1 x n)) (n (expt 2 n)) (a (1- (expt 2 (- m n)))))))))

(local-defthm rem-comp1-4
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 n)))
	     (= (rem (comp1 x m) (expt 2 n))
		(rem (comp1 x n) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt)
		  :use (rem-comp1-2
			(:instance integerp-expt (n (- m n)))
			(:instance expt-pos (x (- m n)))
			(:instance expt-monotone)
			(:instance integerp-expt)
			(:instance integerp-expt (n m))
			(:instance comp1-bnds (n m))
			(:instance rem+ (m (comp1 x n)) (n (expt 2 n)) (a (1- (expt 2 (- m n)))))))))

(local-defthm rem-comp1-5
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (rem (comp1 x m) (expt 2 n))
		(rem (comp1 (rem x (expt 2 n)) n) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use (rem-comp1-3
			(:instance rem-comp1-4 (x (rem x (expt 2 n))))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n)))))))

(defthm COMP1-REM
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (rem (comp1 x m) (expt 2 n))
		(comp1 (rem x (expt 2 n)) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-comp1-5
			(:instance rem< (m (comp1 (rem x (expt 2 n)) n)) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n)))))))


(local-defthm logxor-rewrite
    (implies (and (integerp n) (>= n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logxor x y)
		(logior (logand x (comp1 y n))
			(logand y (comp1 x n)))))
  :rule-classes ())

(local-defthm rem-logxor-1
    (implies (and (integerp n) (>= n 1)
		  (integerp m) (>= m n)
		  (integerp x) (>= x 0) (< x (expt 2 m))
		  (integerp y) (>= y 0) (< y (expt 2 m)))
	     (= (rem (logxor x y) (expt 2 n))
		(logior (rem (logand x (comp1 y m)) (expt 2 n))
			(rem (logand y (comp1 x m)) (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logxor-rewrite (n m))
			(:instance or-dist-d
				   (x (logand x (comp1 y m)))
				   (y (logand y (comp1 x m))))
			(:instance logand-nat (i x) (j (comp1 y m)))
			(:instance logand-nat (i y) (j (comp1 x m)))))))

(defthm REM-LOGAND
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-c
			(:instance and-dist-d (x (rem x (expt 2 n))))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))))))

(local-defthm rem-logxor-2
    (implies (and (integerp n) (>= n 1)
		  (integerp m) (>= m n)
		  (integerp x) (>= x 0) (< x (expt 2 m))
		  (integerp y) (>= y 0) (< y (expt 2 m)))
	     (= (rem (logxor x y) (expt 2 n))
		(logior (logand (rem x (expt 2 n))
				(rem (comp1 y m) (expt 2 n)))
			(logand (rem y (expt 2 n))
				(rem (comp1 x m) (expt 2 n))))))
  :rule-classes ()
  :hints (("Goal" :use (rem-logxor-1
			(:instance rem-logand (y (comp1 y m)))
			(:instance rem-logand (x y) (y (comp1 x m)))))))

(local-defthm rem-logxor-3
    (implies (and (integerp n) (>= n 1)
		  (integerp m) (>= m n)
		  (integerp x) (>= x 0) (< x (expt 2 m))
		  (integerp y) (>= y 0) (< y (expt 2 m)))
	     (= (rem (logxor x y) (expt 2 n))
		(logior (logand (rem x (expt 2 n))
				(comp1 (rem y (expt 2 n)) n))
			(logand (rem y (expt 2 n))
				(comp1 (rem x (expt 2 n)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1)
		  :use (rem-logxor-2
			(:instance comp1-rem)
			(:instance comp1-rem (x y))))))

(local-defthm rem-logxor-4
    (implies (and (integerp n) (>= n 1)
		  (integerp m) (>= m n)
		  (integerp x) (>= x 0) (< x (expt 2 m))
		  (integerp y) (>= y 0) (< y (expt 2 m)))
	     (= (rem (logxor x y) (expt 2 n))
		(logxor (rem x (expt 2 n))
			(rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable comp1)
		  :use (rem-logxor-3
			(:instance logxor-rewrite (x (rem x (expt 2 n))) (y (rem y (expt 2 n))))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance rem>=0 (m y) (n (expt 2 n)))
			(:instance rem<n (m x) (n (expt 2 n)))
			(:instance rem<n (m y) (n (expt 2 n)))))))

(defthm REM-LOGXOR
    (implies (and (integerp n) (>= n 1)
		  (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (rem (logxor x y) (expt 2 n))
		(logxor (rem x (expt 2 n))
			(rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-logxor-4 (m (max n (max (1+ (expo x)) (1+ (expo y))))))
			(:instance expo>= (n (max n (max (1+ (expo x)) (1+ (expo y))))))
			(:instance expo>= (n (max n (max (1+ (expo x)) (1+ (expo y))))) (x y))))))

(local-defthm bits-rem-0-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (>= m 0)
		  (integerp n)
		  (>= n 0))
	     (iff (= (rem x (expt 2 (+ m n 1))) 0)
		  (and (= (rem (fl (/ x (expt 2 n))) (expt 2 (1+ m))) 0)
		       (= (rem x (expt 2 n)) 0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-pos (x (1+ m)))
			(:instance fl-rem-5 (m x) (n (expt 2 n)) (p (expt 2 (1+ m))))))))

(defthm BITS-REM-0
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (>= m 0)
		  (integerp n)
		  (>= n 0))
	     (iff (= (rem x (expt 2 (+ m n 1))) 0)
		  (and (= (bits x (+ m n) n) 0)
		       (= (rem x (expt 2 n)) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use (bits-rem-0-1
			(:instance bit-bits-a (k n) (i (+ m n)) (j n))))))

(defthm BITS-BITN
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (iff (= (bits x n 0) 0)
		  (and (= (bitn x n) 0)
		       (= (bits x (1- n) 0) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use ((:instance bitn-def (k n))
			(:instance fl-rem-5 (m x) (n (expt 2 n)) (p 2))))))

(local-defthm bits-bits-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(fl (/ (+ (rem (rem x (expt 2 m)) (expt 2 n))
			  (* (expt 2 n) (fl (/ (rem x (expt 2 m)) (expt 2 n)))))
		       (expt 2 r)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance rem-fl (m (rem x (expt 2 m))) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 m)))
			(:instance rem<n (m x) (n (expt 2 m)))))))

(local-defthm bits-bits-2
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(fl (/ (+ (rem x (expt 2 n))
			  (* (expt 2 n) (fl (/ (rem x (expt 2 m)) (expt 2 n)))))
		       (expt 2 r)))))
  :rule-classes ()
  :hints (("Goal" :use (bits-bits-1
			(:instance rem-rem (a m) (b n))))))

(local-defthm bits-bits-3
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(fl (+ (/ (rem x (expt 2 n)) (expt 2 r))
		       (* (expt 2 (- n r)) (fl (/ (rem x (expt 2 m)) (expt 2 n))))))))
  :rule-classes ()
  :hints (("Goal" :use (bits-bits-2
			(:instance expt- (a n) (b r))))))

(local-defthm bits-bits-4
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (INTEGERP (* (EXPT 2 (+ N (* -1 R)))
                                (FL (* (/ (EXPT 2 N))
                                       (REM X (* 2 (EXPT 2 (+ -1 M)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt)
		  :use ((:instance integerp-expt (n (- n r)))))))

(local-defthm bits-bits-5
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(+ (fl (/ (rem x (expt 2 n)) (expt 2 r)))
		   (* (expt 2 (- n r)) (fl (/ (rem x (expt 2 m)) (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl+int a10)
		  :use (bits-bits-4
			bits-bits-3
			(:instance fl+int
				   (x (/ (rem x (expt 2 n)) (expt 2 r)))
				   (n (* (expt 2 (- n r)) (fl (/ (rem x (expt 2 m)) (expt 2 n))))))))))

(defthm BITS-BITS
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(+ (bits x (1- n) r)
		   (* (expt 2 (- n r)) (bits x (1- m) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use (bits-bits-5))))

(local-defthm bits+bitn-0
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (= (bits x n 0)
		(+ (* (bitn x n) (expt 2 n))
		   (bits x (1- n) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use ((:instance rem-n+1 (a x))))))

(local-defthm hack5
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp k)
		  (>= k 0)
		  (integerp r)
		  (>= r 0))
	     (equal (* X (/ (EXPT 2 K)) (/ (EXPT 2 R)))
		    (* X (/ (EXPT 2 (+ k r)))))))

(defthm BITN-FL
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp k)
		  (>= k 0)
		  (integerp r)
		  (>= r 0))
	     (= (bitn (fl (/ x (expt 2 r))) k)
		(bitn x (+ k r))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (x (fl (/ x (expt 2 r)))))
			(:instance bitn-def (k (+ k r)))
			(:instance expt-pos (x (- r)))
			(:instance n<=fl (n 0) (x (* x (expt 2 (- r)))))
			(:instance fl/int (x (/ x (expt 2 r))) (n (expt 2 k)))))))

(defthm BITS+BITN
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (>= m 0)
		  (integerp n)
		  (> n m))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-a (i n) (j m) (k m))
			(:instance bits+bitn-0 (x (fl (/ x (expt 2 m)))) (n (- n m)))
			(:instance expt-pos (x (- m)))
			(:instance n<=fl (n 0) (x (* x (expt 2 (- m)))))
			(:instance bit-bits-a (i (1- n)) (j m) (k m))
			(:instance bitn-fl (r m) (k (- n m)))))))

(defthm LOGAND-2**N-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x (1- (expt 2 n)))
		x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use ((:instance and-bits-c (k 0))
			(:instance rem< (m x) (n (expt 2 n)))))))

(defthm REM<=M
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (<= (rem m n) m))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl)
			(:instance n<=fl (n 0) (x (/ m n)))))))

(local-defthm bitn+bits-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (+ (* (expt 2 (1+ m)) (bits x n (1+ m)))
		   (* (expt 2 m) (bitn x m)))
		(- (bits x n 0)
		   (bits x (1- m) 0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-bits (m (1+ n)) (r 0) (n (1+ m)))
			(:instance bits+bitn (n m) (m 0))))))

(local-defthm bitn+bits-2
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (* (expt 2 m)
		   (+ (* 2 (bits x n (1+ m)))
		      (bitn x m)))
		(- (bits x n 0)
		   (bits x (1- m) 0))))
  :rule-classes ()
  :hints (("Goal" :use (bitn+bits-1
			(:instance expo+ (n 1))))))

(local-defthm bitn+bits-3
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (* (expt 2 m)
		   (+ (* 2 (bits x n (1+ m)))
		      (bitn x m)))
		(* (expt 2 m)
		   (bits x n m))))
  :rule-classes ()
  :hints (("Goal" :use (bitn+bits-2
			(:instance bits-bits (r 0) (m (1+ n)) (n m))))))

(local-defthm bitn+bits-4
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (* (expt 2 (- m))
		   (expt 2 m)
		   (+ (* 2 (bits x n (1+ m)))
		      (bitn x m)))
		(* (expt 2 (- m))
		   (expt 2 m)
		   (bits x n m))))
  :rule-classes ()
  :hints (("Goal" :use (bitn+bits-3))))

(defthm BITN+BITS
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ()
  :hints (("Goal" :use (bitn+bits-4
			(:instance expo+ (n (- m)))))))

(defthm EXPO-RND
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (= (expo (rnd x mode n))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p near rnd)
		  :use (expo-trunc expo-away))))

(defthm RND-POS
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode))
	     (> (rnd x mode n) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p near rnd)
		  :use (trunc-pos away-pos))))

(in-theory (disable bits))

(defthm BITS+2**K-2
    (implies (and (integerp m)
		  (>= m 0)
		  (integerp n)
		  (>= n m)
		  (integerp k)
		  (>= k 0)
		  (<= k m)
		  (integerp y)
		  (>= y 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 k)))
	     (= (bits (+ x (* y (expt 2 k))) n m)
		(bits y (- n k) (- m k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-a
				   (x (+ x (* y (expt 2 k))))
				   (i n)
				   (j m))
			(:instance expt-pos (x (- k)))
			(:instance fl-unique (x (/ (+ x (* y (expt 2 k))) (expt 2 k))) (n y))))))

(defthm BIT+*K-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (< x (expt 2 m))
		  (>= x 0)
		  (<= m n)
		  (>= m 0)
		  (integerp k)
		  (>= k 0))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn k (- n m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-unique (x (/ (+ x (* k (expt 2 m))) (expt 2 m))) (n k))
			(:instance expt-pos (x (- m)))
			(:instance bitn-fl
				   (x (+ x (* k (expt 2 m))))
				   (r m)
				   (k (- n m)))))))

(defthm AWAY-MINUS
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (away (- x) n) (- (away x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn away-rewrite)
		  :use (expo-minus))))

(defthm NEAR-MINUS
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (near (- x) n) (- (near x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near)
		  :use (trunc-minus away-minus sig-minus))))

(defun FLIP (m)
  (case m
    (inf 'minf)
    (minf 'inf)
    (t m)))

(defthm RND-FLIP
    (implies (and (rationalp x)
		  (ieee-mode-p m)
		  (integerp n)
		  (> n 0))
	     (= (rnd (- x) (flip m) n)
		(- (rnd x m n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ieee-mode-p rnd flip)
		  :use (trunc-minus
			away-minus
			near-minus))))

(defthm RND-SHIFT
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (ieee-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-shift
			away-shift
			near-shift
			(:instance expt-pos (x k))))))

(defthm sticky-sticky-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (exactp x (1- n)))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky)))))

(defthm sticky-sticky-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (not (exactp x (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-<= (m (1- m)) (n (1- n)))))))

(defthm sticky-sticky-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (not (exactp (sticky x n) (1- m))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-exactp-n-1
			(:instance exactp-<= (x (sticky x n)) (m (1- m)) (n (1- n)))))))

(defthm sticky-sticky-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (= (sticky (sticky x n) m)
		(+ (trunc (sticky x n) (1- m))
		   (expt 2 (1+ (- (expo x) m))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn)
		  :use (expo-sticky
			sticky-pos
			sticky-sticky-3
			(:instance sticky (x (sticky x n)) (n m))))))

(defthm sticky-sticky-5
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (= (sticky (sticky x n) m)
		(+ (trunc x (1- m))
		   (expt 2 (1+ (- (expo x) m))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn)
		  :use (sticky-sticky-4
			(:instance trunc-sticky (m (1- m)))))))

(defthm sticky-sticky-6
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn)
		  :use (sticky-sticky-5
		      sticky-sticky-2
		      (:instance sticky (n m))))))

(defthm STICKY-STICKY
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-6
			sticky-sticky-1))))
