;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "fp")

(defun cg (x) (- (fl (- x))))

(defthm fl-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (fl x) (fl y)))
  :rule-classes ())

(defthm cg-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes ())


(defthm int-fl
    (implies (rationalp x)
	     (integerp (fl x))))

(defthm int-cg
    (implies (rationalp x)
	     (integerp (cg x))))

(defthm fl-int
    (implies (integerp x)
	     (equal (fl x) x)))

(defthm fl-int-2
    (implies (rationalp x)
	     (iff (equal (fl x) x)
		  (integerp x))))

(defthm cg-int
    (implies (integerp x)
	     (equal (cg x) x)))

(defthm cg-int-2
    (implies (rationalp x)
	     (iff (equal (cg x) x)
		  (integerp x))))

(defthm fl-def
    (implies (rationalp x)
	     (and (<= (fl x) x)
		  (< x (1+ (fl x)))))
  :rule-classes ())

(defthm cg-def
    (implies (rationalp x)
	     (and (>= (cg x) x)
		  (> (1+ x) (cg x))))
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

(defthm fl/int-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (fl (/ (fl x) n))
		 (fl (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def)))))

(defthm fl/int-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (fl (/ (fl x) n))
		 (fl (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def)
			(:instance n<=fl (n (* n (fl (/ x n)))))
			(:instance n<=fl (n (fl (/ x n))) (x (/ (fl x) n)))
			(:instance fl-def (x (/ x n)))
			(:instance fl-def (x (/ (fl x) n)))))))

(defthm fl/int
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (fl (/ (fl x) n))
		    (fl (/ x n))))
  :hints (("Goal" :use ((:instance fl/int-1)
			(:instance fl/int-2)))))

(defthm fl-cg
    (implies (and (rationalp x)
		  (not (integerp x)))
	     (equal (cg x) (1+ (fl x))))
  :rule-classes ())

(defthm cg/int-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (cg (/ (cg x) n))
		 (cg (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cg-def)
			(:instance cg-monotone (x (/ x n)) (y (/ (cg x) n)))))))

(defthm cg/int-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (cg (/ (cg x) n))
		 (cg (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance n>=cg (n (* n (cg (/ x n)))))
			(:instance n>=cg (n (cg (/ x n))) (x (/ (cg x) n)))
			(:instance cg-def (x (/ x n)))))))

(defthm cg/int
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (cg (/ (cg x) n))
		    (cg (/ x n))))
  :hints (("Goal" :use ((:instance cg/int-1)
			(:instance cg/int-2)))))

(defthm delta1-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (* y d) (* (- x y) d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x d) (y+ (- x y)))))))


(defthm delta1-a
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (>= (- x (* y (+ 1 d)))
		 (* (- x y) (- 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta1-b
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (- x (* y (- 1 d)))
		 (* (- x y) (+ 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta2
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= (* x d) 0))
	     (>= (+ x (* y (- 1 d)))
		 (* (+ x y) (- 1 d))))
  :rule-classes ())

(defthm expt-pos
    (implies (integerp x)
	     (> (expt 2 x) 0)))

(defthm expt-monotone-1
    (implies (and (integerp n)
		  (integerp k)
		  (>= k 0))
	     (<= (expt 2 n) (expt 2 (+ n k))))
  :rule-classes ())

(defthm expt-monotone
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m))
	     (<= (expt 2 n) (expt 2 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-monotone-1 (k (- m n)))))))

(defthm expt-strong-monotone-1
    (implies (and (integerp n)
		  (integerp k)
		  (> k 0))
	     (< (expt 2 n) (expt 2 (+ n k))))
  :rule-classes ())

(defthm expt-strong-monotone-2
    (implies (and (integerp n)
		  (integerp m)
		  (< n m))
	     (< (expt 2 n) (expt 2 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-strong-monotone-1 (k (- m n)))))))

(defthm expt-strong-monotone
    (implies (and (integerp n)
		  (integerp m))
	     (iff (< n m) (< (expt 2 n) (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-strong-monotone-2)
			(:instance expt-strong-monotone-2 (n m) (m n))))))

(defthm expt-
    (implies (and (integerp a)
		  (integerp b))
	     (= (/ (expt 2 a) (expt 2 b)) (expt 2 (- a b))))
  :rule-classes ())

(defthm expt-non-neg
    (implies (integerp n)
	     (not (< (expt 2 n) 0))))

(defthm expo+
    (implies (and (integerp n)
		  (integerp m))
	     (= (expt 2 (+ m n))
		(* (expt 2 m) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance my-exponents-add (r 2) (i m) (j n))))))



(defthm exp+1-1
    (implies (and (integerp m)
		  (integerp n)
		  (<= n m))
	     (<= (+ (expt 2 m) (expt 2 n))
		 (expt 2 (1+ m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-monotone)
			(:instance expo+ (n 1))))))


(defthm exp+1
    (implies (and (integerp m)
		  (integerp n)
		  (<= n m))
	     (> (* (- 1 (expt 2 m)) (- 1 (expt 2 n)))
		(- 1 (expt 2 (1+ m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance exp+1-1)
			(:instance expt-pos (x (+ m n)))))))

(defthm exp+2-1
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (<= (* (expt 2 m) (expt 2 n))
		 (expt 2 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-monotone (n (+ m n)))
			(:instance expo+)))))

(defthm exp+2-2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (<= (+ (expt 2 m) (expt 2 n) (* (expt 2 m) (expt 2 n)))
		 (* 3 (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-monotone)
			(:instance exp+2-1)))))

(defthm exp+2-3
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (+ (expt 2 m) (expt 2 n) (* (expt 2 m) (expt 2 n)))
		 (* 4 (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-pos (x m))
			(:instance exp+2-2)
			(:instance *-strongly-monotonic (x (expt 2 m)) (y 3) (y+ 4))))))

(defthm exp+2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (* (1+ (expt 2 m)) (1+ (expt 2 n)))
		(1+ (expt 2 (+ m 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exp+2-3)
			(:instance expo+ (n 2))))))


(defthm exp-invert-1
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (* (expt 2 n) (expt 2 (1+ n)))
		 (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-monotone (n (1+ n)) (m 0))
			(:instance *-weakly-monotonic (x (expt 2 n)) (y (expt 2 (1+ n))) (y+ 1))))))

(defthm exp-invert-2
    (implies (and (integerp n)
		  (<= n -1))
	     (>= (* (- 1 (expt 2 n))
		    (1+ (expt 2 (1+ n))))
		 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m 1))
			(:instance exp-invert-1)))))

(defthm cancel-x
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (<= 1 (* x y)))
	     (<= (/ x) y))
  :rule-classes ())

(defthm exp-invert
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (/ (- 1 (expt 2 n)))
		 (1+ (expt 2 (1+ n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cancel-x (x (- 1 (expt 2 n))) (y (1+ (expt 2 (1+ n)))))
			(:instance exp-invert-1)
			(:instance expt-monotone (m -1))))))

(defthm *-doubly-monotonic
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (rationalp b)
		  (<= 0 x)
		  (<= 0 y)
		  (<= 0 a)
		  (<= 0 b)
		  (<= x y)
		  (<= a b))
	     (<= (* x a) (* y b)))
  :rule-classes ())

(defthm sq-sq-1
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* (* a b) (* a b))
		 (* (expt 2 (- (* 2 n) 2)) (* p p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-doubly-monotonic
				   (x (* a a)) (a (* b b))
				   (y p) (b (* (expt 2 (- (* 2 n) 2)) p)))))))

(defthm sqrt<=
    (implies (and (rationalp x)
		  (rationalp a)
		  (>= a 0)
		  (<= (* x x) (* a a)))
	     (<= x a))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-strongly-monotonic (y a) (y+ x))
			(:instance *-strongly-monotonic (x a) (y a) (y+ x))))))

(defthm sq-sq-2
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* (* (expt 2 (1- n)) p) (* (expt 2 (1- n)) p))
		 (* (expt 2 (- (* 2 n) 2)) (* p p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (1- n)) (n (1- n)))))))


(defthm sq-sq-3
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (expt 2 (1- n)) p) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-pos (x (1- n)))))))

(defthm sq-sq-4
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* a b)
		 (* (expt 2 (1- n)) p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-1)
			(:instance sq-sq-3)
			(:instance sqrt<= (x (* a b)) (a (* (expt 2 (1- n)) p)))
			(:instance sq-sq-2)))))

(defthm sq-sq-5
    (implies (and (rationalp x)
		  (rationalp p)
		  (integerp n)
		  (<= x (* (expt 2 (1- n)) p)))
	     (<= (* 2 x) (* (expt 2 n) p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable *-weakly-monotonic)
		  :use ((:instance expo+ (m (1- n)) (n 1))
			(:instance *-weakly-monotonic (x 2) (y x) (y+ (* (expt 2 (1- n)) p)))))))


(defthm sq-sq-6
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (<= (* 2 a b)
		 (* (expt 2 n) p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-4)
			(:instance sq-sq-5 (x (* a b)))))))

(defthm sq-sq-7
    (implies (and (rationalp a)
		  (rationalp b))
	     (>= (* (- a b) (- a b))
		 (- (* a a) (* 2 a b))))
  :rule-classes ())

(defthm sq-sq-8
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (>= p 0)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (- a b) (- a b))
		 (- (* (- 1 (expt 2 n)) p)
		    (* (expt 2 n) p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-6)
			(:instance sq-sq-7)))))

(defthm sq-sq-9
    (implies (and (rationalp p)
		  (integerp n))
	     (= (- (* (- 1 (expt 2 n)) p)
		   (* (expt 2 n) p))
		(* (- 1 (expt 2 (1+ n))) p)))
  :rule-classes ())

(defthm sq-sq
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp p)
		  (integerp n)
		  (<= (* (- 1 (expt 2 n)) p) (* a a))
		  (<= (* a a) p)
		  (<= (* b b) (* (expt 2 (- (* 2 n) 2)) p)))
	     (>= (* (- a b) (- a b))
		 (* (- 1 (expt 2 (1+ n))) p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sq-sq-8)
			(:instance sq-sq-9)))))