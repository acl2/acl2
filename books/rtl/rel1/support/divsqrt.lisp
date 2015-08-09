;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "odd")
(include-book "loglemmas")


;;;basic

(defun fl-half (x)
  (1- (fl (/ (1+ x) 2))))

(defthm FL-HALF-LEMMA
    (implies (and (integerp x)
		  (not (integerp (/ x 2))))
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance x-or-x/2)
			(:instance fl-int (x (/ (1+ x) 2)))))))

(in-theory (disable fl-half))

(defthm FL-REM-0
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (iff (= (rem m n) 0)
		  (= m (* (fl (/ m n)) n))))
  :rule-classes ()
  :hints (("Goal" :use (rem-fl))))

(defthm FL-REM-1
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0))
	     (>= m (* (fl (/ m n)) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem-fl rem>=0))))

(local
(defthm fl-rem-2
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp p) (> p 0))
	     (= (* (fl (/ m (* n p)))
		   (* n p))
		(* (* (fl (/ (fl (/ m n)) p))
		      p)
		   n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl/int (x (/ m n)) (n p)))))))

(local
(defthm fl-rem-3
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp p) (> p 0))
	     (<= (* (fl (/ m (* n p)))
		    (* n p))
		 (* (fl (/ m n)) n)))
  :rule-classes ()
  :hints (("Goal" :use (fl-rem-2
			(:instance fl-rem-1 (m (fl (/ m n))) (n p)))))))

(local
(defthm fl-rem-4
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp p) (> p 0))
	     (iff (= (* (fl (/ m (* n p)))
			(* n p))
		     m)
		  (and (= (* (fl (/ (fl (/ m n)) p)) p)
			  (fl (/ m n)))
		       (= (* (fl (/ m n)) n)
			  m))))
  :rule-classes ()
  :hints (("Goal" :use (fl-rem-2 fl-rem-3 fl-rem-1)))))

(defthm FL-REM-5
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp p) (> p 0))
	     (iff (= (rem m (* n p)) 0)
		  (and (= (rem m n) 0)
		       (= (rem (fl (/ m n)) p) 0))))
  :rule-classes ()
  :hints (("Goal" :use (fl-rem-4
			fl-rem-0
			(:instance fl-rem-0 (n (* n p)))
			(:instance fl-rem-0 (m (fl (/ m n))) (n p))))))

(defthm DIVIDES-REM-0
    (implies (and (integerp n)
		  (integerp a)
		  (> n 0)
		  (>= a 0))
	     (= (rem (* a n) n)
		0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem+ (m 0))
			(:instance rem< (m 0))))))

(defthm REM+REM
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (>= a 0)
		  (>= b 0)
		  (> n 0))
	     (= (rem (+ a (rem b n)) n)
		(rem (+ a b) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m b))
			(:instance rem>=0 (m b))
			(:instance rem+ (m (+ a (rem b n))) (a (fl (/ b n))))))))

(defthm REM-SQUEEZE
    (implies (and (integerp m) (>= m 0)
		  (integerp n) (> n 0)
		  (integerp a) (>= a 0)
		  (integerp r) (>= r 0)
		  (<= (* a n) m)
		  (< m (+ (* a n) r)))
	     (< (rem m n) r))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl)
			(:instance n<=fl (x (/ m n)) (n a))))))

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

(defthm REM=REM
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (= (rem a n) (rem b n)))
	     (integerp (/ (- a b) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem=rem-3)))))

(local (defthm nk>=k-1
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp k)
		  (> k 0)
		  (not (= (* n k) 0)))
	     (>= (* n k) k))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat n)))))

(local (defthm nk>=k-2
    (implies (and (integerp n)
		  (>= n 0)
		  (integerp k)
		  (> k 0)
		  (not (= (* n k) 0)))
	     (>= (abs (* n k)) k))
  :rule-classes ()
  :hints (("Goal" :use (nk>=k-1)))))

(local (defthm nk>=k-3
    (implies (and (integerp n)
		  (<= n 0)
		  (integerp k)
		  (> k 0)
		  (not (= (* n k) 0)))
	     (>= (abs (* n k)) k))
  :rule-classes ()
  :hints (("Goal" :use ((:instance nk>=k-2 (n (- n))))))))

(defthm NK>=K
    (implies (and (integerp n)
		  (integerp k)
		  (> k 0)
		  (not (= (* n k) 0)))
	     (>= (abs (* n k)) k))
  :rule-classes ()
  :hints (("Goal" :use (nk>=k-2 nk>=k-3))))

(defthm REM=REM<N
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp n) (> n 0)
		  (< (abs (- a b)) n)
		  (= (rem a n) (rem b n)))
	     (= a b))
  :rule-classes ()
  :hints (("Goal" :use (rem=rem
			(:instance nk>=k (k n) (n (/ (- a b) n)))
			(:instance *cancell (x a) (y b) (z n))))))

(defthm REM-SQUEEZE-2
    (implies (and (integerp m)
		  (>= m 0)
		  (integerp n)
		  (> n 0)
		  (integerp a)
		  (>= a 0)
		  (> (* (1+ a) n) m)
		  (>= m (* a n)))
	     (= (rem m n) (- m (* a n))))
  :rule-classes nil :hints
  (("goal" :use
	   ((:instance rem-fl)
	    (:instance fl-unique (x (/ m n)) (n a))))))

(local (defthm floor-2-pos
    (implies (and (integerp m)
		  (>= m 0))
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-m+1 (n 2)))))))

(local (defthm floor-2-neg-1
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(fl (- (- (/ (1+ (- m)) 2)) m))))
  :rule-classes ()))

(local (defthm floor-2-neg-2
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(- (fl (- (/ (1+ (- m)) 2))) m)))
  :rule-classes ()
  :hints (("Goal" :use (floor-2-neg-1)))))

(local (defthm floor-2-neg-3
    (implies (and (integerp m)
		  (<= m 0))
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (+ m (fl (/ (- m) 2)))))))
  :rule-classes ()
  :hints (("Goal" :use (floor-2-neg-2
			(:instance floor-2-pos (m (- m))))))))

(local (defthm floor-2-neg
    (implies (and (integerp m)
		  (<= m 0))
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ()
  :hints (("Goal" :use (floor-2-neg-3)))))

(defthm FLOOR-2
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ()
  :hints (("Goal" :use (floor-2-neg
			floor-2-pos))))

(defthm ABS-+
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z))
	     (<= (abs (- x y))
		 (+ (abs (- x z))
		    (abs (- y z)))))
  :rule-classes ())

(defthm ABS->=
    (implies (and (rationalp x)
		  (rationalp y))
	     (>= (abs (- y x)) (- (abs x) (abs y))))
  :rule-classes ())

(local (defthm ABS+
    (implies (and (rationalp x)
		  (rationalp y))
	     (<= (abs (+ x y))
		 (+ (abs x) (abs y))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable abs)))))

(defthm ABS-
    (implies (and (rationalp x)
		  (rationalp y))
	     (<= (abs (- x y))
		 (+ (abs x) (abs y))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable abs))))


;;;bit-vectors

(defthm BITN-0
    (implies (and (integerp k)
		  (>= k 0))
	     (= (bitn 0 k) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (x 0))))))

(defthm BITN-0-1
    (or (= (bitn x n) 0) (= (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn))))

(local
(defthm bit-expo-c-1
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (<= (1- (expt 2 (- n k))) (/ x (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- n k)) (n k))
			(:instance *-weakly-monotonic
				   (y (- (expt 2 n) (expt 2 k)))
				   (y+ x)
				   (x (/ (expt 2 k)))))))))

(local
(defthm bit-expo-c-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< x (expt 2 n)))
	     (< (/ x (expt 2 k)) (expt 2 (- n k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable *-strongly-monotonic)
		  :use ((:instance expo+ (m (- n k)) (n (- k)))
			(:instance expt-pos (x (- k)))
			(:instance *-strongly-monotonic
				   (y x)
				   (y+ (expt 2 n))
				   (x (/ (expt 2 k)))))))))

(local
(defthm bit-expo-c-3
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (= (fl (/ x (expt 2 k)))
		(1- (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt)
		  :use ((:instance bit-expo-c-1)
			(:instance bit-expo-c-2)
			(:instance integerp-expt (n (- n k)))
			(:instance fl-unique (x (/ x (expt 2 k))) (n (1- (expt 2 (- n k))))))))))

(local
(defthm bit-expo-c-4
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (= (fl (/ x (expt 2 k)))
		(1+ (* 2 (1- (expt 2 (1- (- n k))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-expo-c-3))))))

(local
(defthm bit-expo-c-5
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (= (rem (fl (/ x (expt 2 k))) 2)
		(rem 1 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable INTEGERP-EXPT-TYPE  ;; RBK: t-s and lin
                                      A14  ;; RBK: t-s and lin
                                      expt-pos integerp-expt)
		  :use ((:instance bit-expo-c-4)
			(:instance integerp-expt (n (1- (- n k))))
			(:instance expt-pos (x (1- (- n k))))
			(:instance rem+ (m 1) (n 2) (a (1- (expt 2 (1- (- n k)))))))))))

(local
(defthm bit-expo-c-6
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (= (rem (fl (/ x (expt 2 k))) 2)
		1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-expo-c-5)
			(:instance rem< (m 1) (n 2)))))))

(defthm BIT-EXPO-C
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def)
			(:instance bit-expo-c-6)))))

(defthm BIT-EXPO-D
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-expo-c)
			(:instance expt-monotone (n k) (m n))))))

(defthm BIT-BASIC-H-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand  (logior y z) x)
		(logior (logand y x) (logand z x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-h)
			(:instance bit-basic-c (y (logior y z)))
			(:instance bit-basic-c)
			(:instance bit-basic-c (y z))))))

(defthm BIT-EXPO-B
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0)
		  (<= (expt 2 n) x)
		  (< x (expt 2 (1+ n))))
	     (equal (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (k n))
			(:instance rem< (m (fl (/ x (expt 2 n)))) (n 2))
			(:instance fl-unique (x (/ x (expt 2 n))) (n 1))))))

(defthm BITN-2**N
    (implies (and (integerp n)
		  (>= n 0))
	     (= (bitn (expt 2 n) n) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-expo-b (x (expt 2 n)))
			(:instance expt-pos (x n))
			(:instance integerp-expt)))))

(local
(defthm and-bits-e-1
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits (- (1- (expt 2 n)) (expt 2 l)) (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-bits-c (x (- (1- (expt 2 n)) (expt 2 l))))
			(:instance expt-strong-monotone (n l) (m n)))))))

(local
(defthm and-bits-e-2
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (fl (/ (rem (- (1- (expt 2 n)) (expt 2 l)) (expt 2 n)) (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance and-bits-e-1))))))

(local
(defthm and-bits-e-3
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (rem (- (1- (expt 2 n)) (expt 2 l)) (expt 2 n))
		(- (1- (expt 2 n)) (expt 2 l))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-strong-monotone (n l) (m n))
			(:instance expt-pos (x l))
			(:instance rem< (m (- (1- (expt 2 n)) (expt 2 l))) (n (expt 2 n))))))))

(local
(defthm hack-m4
    (implies (= x y)
	     (= (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k)))))
  :rule-classes ()))

(local
(defthm and-bits-e-4
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (fl (/ (rem (- (1- (expt 2 n)) (expt 2 l)) (expt 2 n))
		       (expt 2 k)))
		(fl (/ (- (1- (expt 2 n)) (expt 2 l))
		       (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-e-3
			(:instance hack-m4
				   (x (rem (- (1- (expt 2 n)) (expt 2 l)) (expt 2 n)))
				   (y (- (1- (expt 2 n)) (expt 2 l)))))))))

(local
(defthm and-bits-e-5
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (fl (/ (- (1- (expt 2 n)) (expt 2 l)) (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :hands-off (expt rem fl)
		  :use ((:instance and-bits-e-2)
			(:instance and-bits-e-4))))))

(local
(defthm and-bits-e-6
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (fl (/ (- (1- (expt 2 n)) (expt 2 l)) (expt 2 k)))
		(fl (- (expt 2 (- n k)) (/ (1+ (expt 2 l)) (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- n k)) (n k)))))))

(local (defthm hack-l2
    (implies (and (integerp x)
		  (integerp y)
		  (< 0 x)
		  (<= x y))
	     (and (> (/ x y) 0)
		  (<= (/ x y) 1)))
  :rule-classes ()))

(local
(defthm and-bits-e-7
    (implies (and (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k))
	     (and (> (/ (1+ (expt 2 l)) (expt 2 k)) 0)
		  (<= (/ (1+ (expt 2 l)) (expt 2 k)) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-pos (x l))
			(:instance expt-pos (x k))
			(:instance integerp-expt (n l))
			(:instance integerp-expt (n k))
			(:instance hack-l2 (x (1+ (expt 2 l))) (y (expt 2 k)))
			(:instance expt-strong-monotone (n l) (m k)))))))

(local
(defthm and-bits-e-8
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (fl (- (expt 2 (- n k)) (/ (1+ (expt 2 l)) (expt 2 k))))
		(- (expt 2 (- n k)) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt)
		  :use (and-bits-e-6
			and-bits-e-7
			(:instance integerp-expt (n (- n k)))
			(:instance fl-unique
				   (x (- (expt 2 (- n k)) (/ (1+ (expt 2 l)) (expt 2 k))))
				   (n (- (expt 2 (- n k)) 1))))))))

(local
(defthm and-bits-e-9
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (fl (/ (- (1- (expt 2 n)) (expt 2 l)) (expt 2 k)))
		(- (expt 2 (- n k)) 1)))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-e-8
			and-bits-e-6)))))

(local
(defthm and-bits-e-10
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (- (expt 2 (- n k)) 1))))
  :rule-classes ()
  :hints (("Goal" :hands-off (expt rem fl)
		  :use ((:instance and-bits-e-5)
			(:instance and-bits-e-9))))))

(defthm AND-BITS-E
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(- (expt 2 n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :hands-off (expt rem fl)
		  :use ((:instance and-bits-e-10)
			(:instance expo+ (m (- n k)) (n k))))))

(defthm BITS-NAT
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (bits x i j))
		  (>= (bits x i j) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance integerp-expt (n (1+ i)))
			(:instance integerp-expt (n j))
			(:instance expt-pos (x (1+ i)))
			(:instance expt-pos (x j))
			(:instance rem>=0 (m x) (n (expt 2 (1+ i))))
			(:instance fl-def (x (/ (rem x (expt 2 (1+ i))) (expt 2 j))))))))

(defthm BITS-0
    (implies (and (integerp i)
		  (integerp j)
		  (>= i 0))
	     (equal (bits 0 i j) 0))
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance rem< (m 0) (n (expt 2 (1+ i))))
			(:instance expt-pos (x (1+ i)))
			(:instance integerp-expt (n (1+ i)))))))

(defthm BITN-0-REWRITE
    (implies (and (integerp k) (>= k 0))
	     (equal (bitn 0 k) 0))
  :hints (("Goal" :use (bitn-0))))

(defthm BITS<
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (< (bits x i j) (expt 2 (- (1+ i) j))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance rem<n (m x) (n (expt 2 (1+ i))))
			(:instance expt-pos (x (- j)))
			(:instance expt-pos (x (1+ i)))
			(:instance integerp-expt (n (1+ i)))
			(:instance *-strongly-monotonic
				   (x (expt 2 (- j)))
				   (y (rem x (expt 2 (1+ i))))
				   (y+ (expt 2 (1+ i))))
			(:instance expo+ (m (1+ i)) (n (- j)))
			(:instance fl-def (x (/ (rem x (expt 2 (1+ i))) (expt 2 j))))))))

;;;float

(defthm SGN*
    (implies (and (rationalp x) (rationalp y))
	     (= (sgn (* x y)) (* (sgn x) (sgn y))))
  :rule-classes ())

(local
 (defthm eb-hack
    (implies (and (integerp n) (integerp k))
	     (= (expt 2 (+ -1 N (* -1 K) (* -1 (+ -1 N))))
		(expt 2 (- k))))
  :rule-classes ()))

(defthm EXACT-BITS-A-B
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance eb-hack)
			(:instance exactp2 (n (- n k)))))))

(defthm EXACT-BITS-A-C
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (= (bits x (1- n) k)
		     (/ x (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-int (x (/ x (expt 2 k))))
			(:instance rem< (m x) (n (expt 2 n)))
			(:instance expo-upper-bound)))))

(defthm EXACT-BITS-A-D
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (integerp (/ x (expt 2 k)))
		  (= (bits x (1- k) 0)
		     0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n (expt 2 k)))))))

(defthm EXACT-BITS-B-D
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (= (expo x) (1- n))
		  (< k n))
	     (iff (exactp x (- n k))
		  (= (bits x (1- k) 0)
		     0)))
  :rule-classes ()
  :hints (("Goal" :use (exact-bits-a-d exact-bits-a-b))))

(defthm EXPO-MINUS
    (implies (rationalp x)
	     (= (expo (- x))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expo))))

(defthm SIG-MINUS
    (implies (rationalp x)
	     (= (sig (- x))
		(sig x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sig)
		  :use (expo-minus))))

(defthm EXPO>=
    (implies (and (rationalp x)
		  (integerp n)
		  (>= x (expt 2 n)))
	     (>= (expo x) n))
  :rule-classes ()
  :hints (("Goal" :use (expo-upper-bound
			(:instance expt-monotone (n (1+ (expo x))) (m n))))))

(defthm EXPO<=
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (< x (* 2 (expt 2 n))))
	     (<= (expo x) n))
  :rule-classes ()
  :hints (("Goal" :use (expo-lower-bound
			(:instance expo+ (m 1))
			(:instance expt-monotone (n (1+ n)) (m (expo x)))))))

(defthm EXACTP-
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (- x) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sig exactp)
		  :use (expo-))))


;;;round

(local
 (defthm bt-hack
    (implies (and (integerp e)
		  (integerp n)
		  (integerp k)
		  (= e (1- n)))
	     (= (expt 2 (- (1- k) e))
		(expt 2 (- k n))))
  :rule-classes ()))

(local
 (defthm bits-trunc-1
    (implies (and (integerp x) (> x 0)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (= (expo x) (1- n)))
	     (= (trunc x k)
		(* (fl (/ x (expt 2 (- n k))))
		   (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-rewrite))
	  ("Subgoal 1" :use ((:instance bt-hack (e (expo x))))))))

(local
(defthm bt-hack-2
    (implies (and (integerp n) (integerp k))
	     (not (and (<= (EXPT 2 N) X) (< X (EXPT 2 (+ 1 -1 N))))))
  :rule-classes ()))

(local
(defthm bt-hack-3
    (implies (and (integerp n) (integerp x)
		  (EQUAL e (+ -1 N))
		  (EQUAL (REM X (EXPT 2 N)) X))
	     (= (REM X (EXPT 2 (+ 1 e)))
		x))
  :rule-classes ()))

(local
(defthm bits-trunc-2
    (implies (and (integerp x) (> x 0)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (= (expo x) (1- n)))
	     (= (trunc x k)
		(* (bits x (1- n) (- n k))
		   (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc-1)
			(:instance rem< (m x) (n (expt 2 n)))
			(:instance expo-upper-bound)))
	  ("Subgoal 2'''" :use ((:instance bt-hack-2)))
	  ("Subgoal 1'6'" :use ((:instance bt-hack-3 (e (expo x))))))))

(local
(defthm crap444
    (implies (integerp n)
             (equal (* 2 (expt 2 (+ -1 n)))
                    (expt 2 n)))))

(local (in-theory (disable crap444)))

(local
(defthm bits-trunc-3
    (implies (and (integerp x) (> x 0)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (= (expo x) (1- n)))
	     (= (trunc x k)
		(logand x (- (expt 2 n) (expt 2 (- n k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc-2)
			(:instance and-bits-c (k (- n k)))))
         ("Subgoal 1'5'" :use (:instance crap444)))))

(local
(defthm hack-78
    (implies (and (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k))
	     (integerp (+ (EXPT 2 N)
			  (* -1 (EXPT 2 (+ N (* -1 K)))))))
  :hints (("Goal" :in-theory (disable expt integerp-expt integerp-expt-type)
		  :use ((:instance integerp-expt (n (- n k)))
			(:instance integerp-expt))))))

(local
(defthm hack-79
    (implies (and (integerp n)
		  (integerp m)
		  (>= m n))
	     (integerp (+ -1 (EXPT 2 (+ M (* -1 N))))))
  :hints (("Goal" :in-theory (disable expt integerp-expt integerp-expt-type)
		  :use ((:instance integerp-expt (n (- m n))))))))

(local
(defthm hack-80
    (implies (and (integerp n)
		  (integerp m)
		  (>= m n))
	     (not (< (+ -1 (EXPT 2 (+ M (* -1 N)))) 0)))
  :hints (("Goal" :in-theory (disable expt-pos hack-79)
		  :use ((:instance expt-pos (x (- m n)))
			(:instance hack-79))))))

(local
(defthm rem-2m-2n-k-1
    (implies (and (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0))
	     (= (rem (- (expt 2 m) (expt 2 (- n k)))
		     (expt 2 n))
		(rem (- (expt 2 n) (expt 2 (- n k)))
		     (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem+
				   (m (- (expt 2 n) (expt 2 (- n k))))
				   (n (expt 2 n))
				   (a (1- (expt 2 (- m n)))))
			(:instance expt-monotone (n (- n k)) (m n)))))))

(local
(defthm rem-2m-2n-k-2
    (implies (and (integerp n) (> n k)
		  (integerp k) (> k 0))
	     (= (rem (- (expt 2 n) (expt 2 (- n k)))
		     (expt 2 n))
		(- (expt 2 n) (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem< (m (- (expt 2 n) (expt 2 (- n k)))) (n (expt 2 n)))
			(:instance expt-monotone (n (- n k)) (m n))))
	  ("Goal'''" :in-theory (disable expt-pos)  ;; RBK:
		       :use ((:instance expt-pos (x (- n k))))))))

(local
(defthm rem-2m-2n-k
    (implies (and (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0))
	     (= (rem (- (expt 2 m) (expt 2 (- n k)))
		     (expt 2 n))
		(- (expt 2 n) (expt 2 (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-2m-2n-k-1)
			(:instance rem-2m-2n-k-2))))))

(local
(defthm bits-trunc-4
    (implies (and (integerp x) (> x 0)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (>= x (expt 2 (1- n)))
		  (< x (expt 2 n)))
	     (= (trunc x k)
		(logand x (- (expt 2 n) (expt 2 (- n k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc-3)
			(:instance expo-unique (n (1- n))))))))

(local
(defthm bits-trunc-5
    (implies (and (integerp x) (> x 0)
		  (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (>= x (expt 2 (1- n)))
		  (< x (expt 2 n)))
	     (= (trunc x k)
		(logand x (rem (- (expt 2 m) (expt 2 (- n k))) (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc-4)
			(:instance rem-2m-2n-k))))))

(local
(defthm hack-81
    (implies (and (integerp n)
		  (integerp m)
		  (>= m 0)
		  (integerp k)
		  (> k 0)
		  (>= n k))
	     (integerp (+ (EXPT 2 m)
			  (* -1 (EXPT 2 (+ N (* -1 K)))))))
  :hints (("Goal" :in-theory (disable expt integerp-expt integerp-expt-type)
		  :use ((:instance integerp-expt (n (- n k)))
			(:instance integerp-expt (n m))
			(:instance integerp-expt))))))

(local
(defthm hack-82
    (implies (and (integerp x)
		  (integerp n)
		  (< x (expt 2 n)))
	     (not (<= (* 2 (EXPT 2 (+ -1 N))) X)))
  :rule-classes ()))

(defthm BITS-TRUNC
    (implies (and (integerp x) (> x 0)
		  (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  (>= x (expt 2 (1- n)))
		  (< x (expt 2 n)))
	     (= (trunc x k)
		(logand x (- (expt 2 m) (expt 2 (- n k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc-5)
			(:instance expt-monotone (n (- n k)))
			(:instance and-dist-d (y (- (expt 2 m) (expt 2 (- n k)))))))
	  ("Goal'''" :in-theory (enable crap444))  ;; RBK:
          ))
;;          ("Subgoal 1" :use ((:instance hack-82)))))  ;; RBK:

(local
(defthm near-est-1
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (< (trunc x n)
		(- x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near2 (y (trunc x n)))
			(:instance trunc-exactp-b)
			(:instance trunc-pos)
			(:instance trunc-upper-pos))))))

(local
(defthm near-est-2
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near2 (y (away x n)))
			(:instance away-exactp-b)
			(:instance away-pos)
			(:instance away-lower-pos))))))

(local
(defthm near-est-3
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a15)
		  :use ((:instance near-est-1)
			(:instance expo+ (m (- (expo x) n)) (n 1))
			(:instance near-est-2))))))

(local
(defthm near-est-4
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near x n)))
		     (expt 2 (- (expo x) n))))
	     (> x
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-est-3)
			(:instance fp+2 (x (trunc x n)))
			(:instance trunc-exactp-b)
			(:instance trunc-pos)
			(:instance expo-trunc)
			(:instance away-exactp-c (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(in-theory (disable abs-trunc))

(defthm NEAR-EST
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-est-4)
			(:instance trunc-lower-1)
			(:instance trunc-pos)))))

(local
(defthm trunc-away-1
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (not (exactp x n)))
	     (> x (expt 2 (expo x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-lower-bound)
			(:instance exactp-2**n (n (expo x)) (m n)))))))

(local
(defthm trunc-away-2
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (- x (expt 2 (- (expo x) n)))
		 (expt 2 (expo x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-1)
			(:instance exactp-2**n (n (expo x)) (m (1+ n)))
			(:instance fp+1 (x (expt 2 (expo x))) (n (1+ n)) (y x)))))))

(local
(defthm trunc-away-3
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (expo (- x (expt 2 (- (expo x) n))))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-away-2)
			(:instance expo-unique (x (- x (expt 2 (- (expo x) n)))) (n (expo x)))
			(:instance exactp-2**n (n (- (expo x) n)) (m n))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance expo-lower-bound)
			(:instance expt-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expo-upper-bound))))))

(local
(defthm hack-83
    (IMPLIES (AND (INTEGERP N)
		  (< 0 N))
	     (= (* 1/2 (EXPT 2 (+ N (* -1 (EXPO X)))))
		(EXPT 2 (+ -1 N (* -1 (EXPO X))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- n (expo x))) (n -1)))))))

(local
(defthm hack-84
    (implies (and (rationalp x)
		  (rationalp a)
		  (rationalp b)
		  (= a b))
	     (= (* x a) (* x b)))
  :rule-classes ()))

(local
(defthm hack-85
    (IMPLIES (AND (INTEGERP N)
		  (< 0 N)
		  (rationalp x))
	     (equal (* 1/2 x (EXPT 2 (+ N (* -1 (EXPO X)))))
		(* X (EXPT 2 (+ -1 N (* -1 (EXPO X)))))))
  :hints (("Goal" :use ((:instance hack-83)
			(:instance hack-84
				   (a (* 1/2 (EXPT 2 (+ N (* -1 (EXPO X))))))
				   (b (EXPT 2 (+ -1 N (* -1 (EXPO X)))))))))))

(local
(defthm trunc-away-4
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (* x (expt 2 (- n (expo x))))
		(1+ (* 2 (fl-half (* x (expt 2 (- n (expo x)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2-lemma)
		  :use ((:instance fl-half-lemma (x (* x (expt 2 (- n (expo x)))))))))))

(local
(defthm hack-86
    (implies (integerp k)
	     (= (- (/ (1+ (* 2 k)) 2) 1/2) k))
  :rule-classes ()))

(local
(defthm trunc-away-5
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (* (- x (expt 2 (- (expo x) n)))
		   (expt 2 (- (1- n) (expo x))))
		(fl-half (* x (expt 2 (- n (expo x)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-4)
			(:instance hack-86 (k (fl-half (* x (expt 2 (- n (expo x)))))))
			(:instance expo+ (m (- (expo x) n)) (n (- (1- n) (expo x))))
			(:instance expo+ (m 1) (n (- (1- n) (expo x)))))))))

(local
(defthm trunc-away-6
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (integerp (* (- x (expt 2 (- (expo x) n)))
			  (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-5))))))

(local
(defthm trunc-away-7
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (integerp (* (- x (expt 2 (- (expo x) n)))
			  (expt 2 (- (1- n) (expo (- x (expt 2 (- (expo x) n)))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-6)
			(:instance trunc-away-3))))))

(local
(defthm trunc-away-8
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (>= (- x (expt 2 (- (expo x) n))) 0)
		  (not (exactp x n)))
	     (exactp (- x (expt 2 (- (expo x) n)))
		     n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2-lemma)
		  :use ((:instance trunc-away-7))))))

(local
(defthm trunc-away-9
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (- x (expt 2 (- (expo x) n)))
		     n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-8)
			(:instance expo-lower-bound)
			(:instance expt-monotone (n (- (expo x) n)) (m (expo x))))))))

(local
(defthm trunc-away-10
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (<= (- x (expt 2 (- (expo x) n)))
		 (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-away-9)
			(:instance expo-lower-bound)
			(:instance expt-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c (a (- x (expt 2 (- (expo x) n))))))))))

(local
(defthm trunc-away-11
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (- x (expt 2 (- (expo x) n)))
		     (trunc x n)))
	     (<= x (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-away-8)
			(:instance trunc-away-3)
			(:instance expo+ (m 1) (n (- n (expo x))))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance fp+1 (x (- x (expt 2 (- (expo x) n)))) (y (trunc x n)))
			(:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(defthm TRUNC-AWAY-A
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-b)
		  :use ((:instance trunc-away-10)
			(:instance trunc-away-11)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-b)))))

(local
(defthm hack-87
    (implies (and (rationalp x)
		  (integerp n)
		  (= (expo (- x (expt 2 (- (expo x) n))))
		     (expo x)))
	     (equal (+ x (* -1 (EXPT 2 (+ (EXPO X) (* -1 N))))
		       (EXPT 2
			 (+ 1 (* -1 N)
			    (EXPO (+ X
				     (* -1 (EXPT 2 (+ (EXPO X) (* -1 N)))))))))
		    (+ x (EXPT 2 (+ (EXPO X) (* -1 N))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- (expo x) n)) (n 1)))))))

(local
(defthm hack-88
    (implies (equal x y) (equal (exactp x n) (exactp y n)))
  :rule-classes ()))

(local
(defthm hack-89
    (implies (and (rationalp x)
		  (integerp n)
		  (= (expo (- x (expt 2 (- (expo x) n))))
		     (expo x)))
	     (equal (exactp (+ x (* -1 (EXPT 2 (+ (EXPO X) (* -1 N))))
			       (EXPT 2
				     (+ 1 (* -1 N)
					(EXPO (+ X
						 (* -1 (EXPT 2 (+ (EXPO X) (* -1 N)))))))))
			    n)
		    (exactp (+ x (EXPT 2 (+ (EXPO X) (* -1 N)))) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-87)
			(:instance hack-88
				   (x (+ x (* -1 (EXPT 2 (+ (EXPO X) (* -1 N))))
					 (EXPT 2
					       (+ 1 (* -1 N)
						  (EXPO (+ X
							   (* -1 (EXPT 2 (+ (EXPO X) (* -1 N))))))))))
				   (y (+ x (EXPT 2 (+ (EXPO X) (* -1 N)))))))))))

(local
(defthm trunc-away-12
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (+ x (expt 2 (- (expo x) n)))
		     n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-9)
			(:instance fp+2 (x (- x (expt 2 (- (expo x) n)))))
			(:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expo+ (m (- (expo x) n)) (n 1))
			(:instance trunc-away-3)))
	  ("Subgoal 1" :use ((:instance hack-89))))))

(local
(defthm trunc-away-13
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (+ x (expt 2 (- (expo x) n)))
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-away-12)
			(:instance expo-lower-bound)
			(:instance expt-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance away-exactp-c (a (+ x (expt 2 (- (expo x) n))))))))))

(local
(defthm trunc-away-14
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (> (away x n)
		(- x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance away-lower-pos)
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm trunc-away-15
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (away x n)
		 (+ (- x (expt 2 (- (expo x) n)))
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-b)
		  :use ((:instance trunc-away-8)
			(:instance trunc-away-3)
			(:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance trunc-away-14)
			(:instance away-exactp-b)
			(:instance fp+1 (x (- x (expt 2 (- (expo x) n)))) (y (away x n))))))))

(local
(defthm trunc-away-16
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (away x n)
		 (+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-15)
			(:instance expo+ (m 1) (n (- (expo x) n))))))))

(defthm TRUNC-AWAY-B
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-away-16)
			(:instance trunc-away-13)))))

(local
(defthm near-a-a-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> (near x n) a))
	     (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp+1 (x a) (y (near x n)))
			(:instance exactp-near))))))

(local
(defthm near-a-a-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (rationalp d) (> d 0)
		  (integerp n) (> n 0)
		  (<= (near x n) a)
		  (> x (+ a d)))
	     (> (abs (- (near x n) x))
		(abs (- (+ a d d)
			x))))
  :rule-classes ()))

(local
(defthm near-a-a-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (<= (near x n) a)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near x n) x))
		(abs (- (+ a
			   (expt 2 (- (expo a) n))
			   (expt 2 (- (expo a) n)))
			x))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-a-a-2 (d (expt 2 (- (expo a) n))))
			(:instance expt-pos (x (- (expo a) n))))))))

(local
(defthm near-a-a-4
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (<= (near x n) a)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near x n) x))
		(abs (- (+ a (expt 2 (- (1+ (expo a)) n)))
			x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-a-a-3)
			(:instance expo+ (m (- (expo a) n)) (n 1)))))))

(defthm NEAR-A-A
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near2 (y (+ a (expt 2 (- (1+ (expo a)) n)))))
			(:instance near-a-a-4)
			(:instance near-a-a-1)
			(:instance fp+2 (x a))
			(:instance expt-pos (x (- (1+ (expo a)) n)))))))

(local
(defthm near-a-b-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (rationalp d) (> d 0)
		  (integerp n) (> n 0)
		  (>= (near x n) (+ a d d))
		  (< x (+ a d)))
	     (> (abs (- (near x n) x))
		(abs (- a x))))
  :rule-classes ()))

(local
(defthm near-a-b-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (>= (near x n)
		      (+ a
			 (expt 2 (- (expo a) n))
			 (expt 2 (- (expo a) n))))
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near x n) x))
		(abs (- a x))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-a-b-1 (d (expt 2 (- (expo a) n))))
			(:instance expt-pos (x (- (expo a) n))))))))

(local
(defthm near-a-b-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (>= (near x n)
		      (+ a (expt 2 (- (1+ (expo a)) n))))
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near x n) x))
		(abs (- a x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-a-b-2)
			(:instance expo+ (m (- (expo a) n)) (n 1)))))))

(defthm NEAR-A-B
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near x n) a))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near2 (y a))
			(:instance near-a-b-3)
			(:instance near-a-a-1)))))

(local
(defthm near-a-c-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (>= x a))
	     (>= (near x n) a))
  :rule-classes ()
  :hints (("Goal" :use ((:instance monotone-near (x a) (y x))
			(:instance near-choice (x a))
			(:instance trunc-exactp-a (x a))
			(:instance away-exactp-a (x a)))))))

(local
(defthm near-a-c-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a))
	     (>= a
		 (+ (expt 2 (expo x))
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-lower-bound)
			(:instance fp+1 (x (expt 2 (expo x))) (y a))
			(:instance exactp-2**n (n (expo x)) (m n)))))))

(local
(defthm near-a-c-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> x (- a (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(local
(defthm near-a-c-4
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (= (expo (- a (expt 2 (- (1+ (expo x)) n))))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-a-c-2)
			(:instance near-a-c-3)
			(:instance expt-pos (x (expo x)))
			(:instance expo-upper-bound)
			(:instance expo-unique
				   (x (- a (expt 2 (- (1+ (expo x)) n))))
				   (n (expo x))))))))

(local
(defthm near-a-c-5
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (integerp (* (- a (expt 2 (- (1+ (expo x)) n)))
			  (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- (1+ (expo x)) n)) (n (- (1- n) (expo x))))
			(:instance exactp-<=-expo (x a) (e (expo x)))
			(:instance near-a-c-3)
			(:instance expo-monotone (x (- a (expt 2 (- (1+ (expo x)) n)))) (y a))
			(:instance expo-monotone (y a)))))))

(local
(defthm near-a-c-6
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (exactp (- a (expt 2 (- (1+ (expo x)) n)))
		     n))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance exactp2-lemma (x (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near-a-c-5)
			(:instance near-a-c-2)
			(:instance expt-pos (x (expo x)))
			(:instance near-a-c-4))))))

(local
(defthm near-a-c-7
    (implies (and (rationalp x)
		  (rationalp a)
		  (rationalp e)
		  (> x (- a e)))
	     (> x (+ (- a (* 2 e))
		     e)))
  :rule-classes ()))

(local
(defthm near-a-c-8
    (implies (and (rationalp x)
		  (rationalp a)
		  (integerp n)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> x (+ (- a (expt 2 (- (1+ (expo x)) n)))
		     (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m 1) (n (- (expo x) n)))
			(:instance near-a-c-7 (e (expt 2 (- (expo x) n)))))))))

(local
(defthm near-a-c-9
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> (- a (expt 2 (- (1+ (expo x)) n)))
		0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-a-c-2)
			(:instance expt-pos (x (expo x))))))))

(defthm NEAR-A-C
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near x n) a))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-a-a (a (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near-a-c-8)
			(:instance near-a-c-6)
			(:instance near-a-c-4)
			(:instance near-a-c-9)))))

(local
(defthm near-exact-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (and (< f 1) (< 0 f))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (* (expt 2 (1- n)) (sig x))))
			(:instance exactp))))))

(local
(defthm near-exact-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x (1+ n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (integerp (* 2 f))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp (n (1+ n))))))))

(local
(defthm near-exact-3
    (implies (and (integerp |2F|)
		  (< 0 |2F|)
		  (< |2F| 2))
	     (= |2F| 1))
  :rule-classes ()))

(local
(defthm near-exact-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (re (* (expt 2 (1- n)) (sig x)))
		1/2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-1)
			(:instance near-exact-2)
			(:instance near-exact-3 (|2F| (* 2 (re (* (expt 2 (1- n)) (sig x)))))))))))

(local
(defthm near-exact-5
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (near x n)
		(* (fl (* (expt 2 (1- n)) (sig x)))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near)
			(:instance near-exact-4)
			(:instance trunc))))))

(local
(defthm near-exact-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (near x n))
		(/ (fl (* (expt 2 (1- n)) (sig x)))
		   2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-5)
			(:instance expo+ (m (- (- n 2) (expo x))) (n (expt 2 (- (1+ (expo x)) n)))))))))

(local
(defthm near-exact-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (integerp (* (expt 2 (- (- n 2) (expo x)))
			  (near x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-6)
			(:instance evenp (x (fl (* (expt 2 (1- n)) (sig x))))))))))

(local
(defthm near-exact-8
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-4)
			(:instance near)
			(:instance expo-trunc))))))

(local
(defthm near-exact-9
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (evenp (fl (* (expt 2 (1- n)) (sig x)))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-7)
			(:instance near-exact-8)
			(:instance near-pos)
			(:instance exactp2-lemma (x (near x n)) (n (1- n))))))))

(local
(defthm near-exact-10
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (near x n)
		(* (cg (* (expt 2 (1- n)) (sig x)))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near)
			(:instance near-exact-4)
			(:instance away))))))

(local
(defthm near-exact-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (near x n)
		(* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-10)
			(:instance near-exact-1)
			(:instance fl-cg (x (* (expt 2 (1- n)) (sig x)))))))))

(local
(defthm near-exact-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		      (expt 2 (- (1+ (expo x)) n))))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- (- n 2) (expo x))) (n (expt 2 (- (1+ (expo x)) n)))))))))

(local
(defthm near-exact-13
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (near x n))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-11)
			(:instance near-exact-12))))))

(local
(defthm near-exact-14
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (integerp (* (expt 2 (- (- n 2) (expo x)))
			  (near x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a9 rearrange-fractional-coefs-equal distributivity)
		  :use ((:instance near-exact-13)
			(:instance evenp (x (fl (* (expt 2 (1- n)) (sig x)))))
			(:instance x-or-x/2 (x (fl (* (expt 2 (1- n)) (sig x))))))))))

(local
(defthm near-exact-15
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (= (near x n) (expt 2 (1+ (expo x)))))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-4)
			(:instance near)
			(:instance away)
			(:instance away-pos)
			(:instance expo-away))))))

(local
(defthm near-exact-16
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (= (near x n) (expt 2 (1+ (expo x)))))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-14)
			(:instance near-exact-15)
			(:instance near-pos)
			(:instance exactp2-lemma (x (near x n)) (n (1- n))))))))

(local
(defthm near-exact-17
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x n))
		  (exactp x (1+ n))
		  (not (evenp (fl (* (expt 2 (1- n)) (sig x))))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-16)
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n))))))))

(defthm NEAR-EXACT
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-exact-17)
			(:instance near-exact-9)))))

(local
(defthm near-power-a-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (= (expo (near x n)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near)
			(:instance away)
			(:instance away-pos)
			(:instance expo-trunc)
			(:instance expo-away))))))

(local
(defthm near-power-a-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (< (near x n) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-1)
			(:instance expo-upper-bound (x (near x n)))
			(:instance near-pos))))))

(local
(defthm near-power-a-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (<= (+ (near x n) (expt 2 (- (1+ (expo x)) n)))
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-2)
			(:instance near-power-a-1)
			(:instance exactp-near)
			(:instance fp+1 (x (near x n)) (y (expt 2 (1+ (expo x)))))
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance near-pos))))))

(local
(defthm near-power-a-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (<= (+ (- x (expt 2 (- (expo x) n)))
		    (expt 2 (- (1+ (expo x)) n)))
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-3)
			(:instance near-est))))))

(local
(defthm near-power-a-5
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x))))))
	     (<= (+ x (expt 2 (- (expo x) n)))
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-4)
			(:instance expo+ (m (- (expo x) n)) (n 1)))))))

(local
(defthm near-power-a-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (+ x (expt 2 (- (expo x) n)))
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-5))))))

(local
(defthm near-power-a-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= x
		(- (expt 2 (1+ (expo x)))
		   (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-6))))))

(local
(defthm near-power-a-8
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (integerp (* (- (expt 2 (1+ (expo x)))
			     (expt 2 (- (expo x) n)))
			  (expt 2 (- n (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-7)
			(:instance expo+ (m (- n (expo x))) (n (1+ (expo x))))
			(:instance expo+ (m (- n (expo x))) (n (- (expo x) n))))))))

(local
(defthm hack-90
    (implies (and (= x y)
		  (integerp (* y e)))
	     (integerp (* x e)))
  :rule-classes ()))

(local
(defthm near-power-a-9
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (integerp (* x (expt 2 (- n (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-7)
			(:instance hack-90
				   (y (- (expt 2 (1+ (expo x))) (expt 2 (- (expo x) n))))
				   (e (expt 2 (- n (expo x)))))
			(:instance near-power-a-8))))))

(local
(defthm near-power-a-10
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (exactp x (1+ n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2-lemma)
		  :use ((:instance near-power-a-9))))))

(local
(defthm near-power-a-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (not (exactp x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-6)
			(:instance expo-upper-bound)
			(:instance fp+1 (y (expt 2 (1+ (expo x)))))
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(local
(defthm near-power-a-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (exactp (near x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-10)
			(:instance near-power-a-11)
			(:instance near-exact))))))

(local
(defthm near-power-a-13
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (<= (+ (near x n) (expt 2 (- (+ (expo x) 2) n)))
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-12)
			(:instance near-power-a-2)
			(:instance near-pos)
			(:instance fp+1 (x (near x n)) (n (1- n)) (y (expt 2 (1+ (expo x)))))
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
			(:instance near-power-a-1))))))

(local
(defthm near-power-a-14
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (= (near x n)
			  (expt 2 (1+ (expo x)))))
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (>= (+ (near x n) (expt 2 (- (+ (expo x) 1) n)))
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-est)
			(:instance expo+ (m (- (expo x) n)) (n 1)))))))

(defthm NEAR-POWER-A
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-13)
			(:instance near-power-a-14)
			(:instance expt-strong-monotone
				   (n (- (+ (expo x) 1) n))
				   (m (- (+ (expo x) 2) n)))))))

(local
(defthm near-power-b-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (a (expt 2 (1+ (expo x))))))))))

(local
(defthm near-power-b-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-b-1))))))

(local
(defthm near-power-b-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (+ (expt 2 (1+ (expo x)))
		    (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-power-b-2)
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n)))))
			(:instance expt-pos (x (1+ (expo x))))
			(:instance expo-2**n (n (1+ (expo x))))
			(:instance fp+1
				   (x (expt 2 (1+ (expo x))))
				   (y (trunc (+ x (expt 2 (- (expo x) n))) n))))))))

(local
(defthm near-power-b-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-b-3)
			(:instance expo-upper-bound)
			(:instance expt-monotone (n (- (expo x) n)) (m (- (+ 2 (expo x)) n))))))))

(defthm NEAR-POWER-B
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-power-b-4)
			(:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
			(:instance expt-pos (x (- (expo x) n)))))))

(local
 (defthm near-trunc-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-power-a)
			(:instance near-power-b)
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
			(:instance trunc-trunc (x (+ x (expt 2 (- (expo x) n)))) (m (1- n)))
			(:instance trunc-exactp-a
				   (x (trunc (+ x (expt 2 (- (expo x) n))) n))
				   (n (1- n)))
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x)))))
	     (= (expo (near x n))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-power-a-1)
			(:instance near-est))))))

(local
(defthm near-trunc-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x)))))
	     (= (expo (+ x (expt 2 (- (expo x) n))))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expo-unique (x (+ x (expt 2 (- (expo x) n)))) (n (expo x)))
			(:instance expo-lower-bound)
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (a x))
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-5
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (<(trunc (+ x (expt 2 (- (expo x) n))) n)
	       (fp+ x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n)))
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-6
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 x))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-trunc-5)
			(:instance fp+1 (y (trunc (+ x (expt 2 (- (expo x) n))) n)))
			(:instance trunc-exactp-a (x (+ x (expt 2 (- (expo x) n)))))
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-7
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		x))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-4)
			(:instance near-trunc-6))))))

(defthm NEAR-EXACTP
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x n))
	     (equal (near x n) x))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-choice)
			(:instance trunc-exactp-a)
			(:instance away-exactp-a)))))

(local
(defthm near-trunc-case-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x n))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(near x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-7)
			(:instance near-exactp)
			(:instance trunc-exactp-a (x (+ x (expt 2 (- (expo x) n))))))))))

(local
(defthm near-trunc-8
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (= (near x n)
		     (- x (expt 2 (- (expo x) n)))))
	     (exactp x (1+ n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable exactp-near)
		  :use ((:instance near-trunc-2)
			(:instance near-pos)
			(:instance exactp-near)
			(:instance fp+2 (x (near x n)) (n (1+ n)))
			(:instance exactp-<= (x (near x n)) (m n) (n (1+ n))))))))

(local
(defthm near-trunc-9
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (not (exactp x (1+ n))))
	     (> (near x n)
		(- x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-8)
			(:instance near-est))))))

(local
(defthm near-trunc-10
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (<= (near x n)
		 (trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable exactp-near)
		  :use ((:instance exactp-near)
			(:instance trunc-exactp-c (x (+ x (expt 2 (- (expo x) n)))) (a (near x n)))
			(:instance near-est))))))

(local
(defthm near-trunc-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (not (exactp x (1+ n))))
	     (< (trunc (+ x (expt 2 (- (expo x) n))) n)
		(+ (near x n)
		   (expt 2 (- (expo x) n))
		   (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-trunc-9)
			(:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
			(:instance expt-pos (x (- (expo x) n))))))))

(local
(defthm near-trunc-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (not (exactp x (1+ n))))
	     (< (trunc (+ x (expt 2 (- (expo x) n))) n)
		(+ (near x n)
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-11)
			(:instance expo+ (m (- (expo x) n)) (n 1)))))))

(local
(defthm near-trunc-13
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (not (exactp x (1+ n))))
	     (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (near x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable exactp-near trunc-exactp-b expt-pos)
		  :use ((:instance near-trunc-12)
			(:instance fp+1
				   (x (near x n))
				   (y (trunc (+ x (expt 2 (- (expo x) n))) n)))
			(:instance near-trunc-2)
			(:instance expt-pos (x (- (expo x) n)))
			(:instance exactp-near)
			(:instance near-pos)
			(:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n))))))))))

(local
(defthm near-trunc-case-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (not (exactp x (1+ n))))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-10)
			(:instance near-trunc-13))))))

(local
(defthm near-trunc-14
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (> (near x n) x))
	     (= (near x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-est)
			(:instance exactp-near)
			(:instance exactp-<= (x (near x n)) (m n) (n (1+ n)))
			(:instance fp+1 (n (1+ n)) (y (near x n))))))))

(local
(defthm near-trunc-15
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (> (near x n) x))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-14)
			(:instance near-exact)
			(:instance trunc-exactp-a (x (near x n)) (n (1- n))))))))

(local
(defthm near-trunc-16
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (<= (near x n)
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-exact)
			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (n (1- n))
				   (a (near x n))))))))

(local
(defthm near-trunc-17
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (>= (+ (near x n)
		    (expt 2 (- (1+ (expo x)) n)))
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))) (n (1- n)))
			(:instance expt-pos (x (- (expo x) n)))
			(:instance expo+ (m (- (expo x) n)) (n 1))
			(:instance near-est))))))

(local
(defthm near-trunc-18
    (implies (and (rationalp x)
		  (integerp n))
	     (> (+ (near x n)
		   (expt 2 (- (+ 2 (expo x)) n)))
		(+ (near x n)
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-strong-monotone
				   (n (- (1+ (expo x)) n))
				   (m (- (+ 2 (expo x)) n))))))))

(local
(defthm near-trunc-19
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (> (+ (near x n)
		   (expt 2 (- (+ 2 (expo x)) n)))
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-17)
			(:instance near-trunc-18))))))

(local
(defthm near-trunc-20
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (>= (near x n)
		 (trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance near-exact)
			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n)))) (n (1- n)))
			(:instance fp+1
				   (x (near x n))
				   (y (trunc (+ x (expt 2 (- (expo x) n))) (1- n)))
				   (n (1- n)))
			(:instance near-pos)
			(:instance near-trunc-19)
			(:instance near-trunc-2))))))

(local
(defthm near-trunc-21
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (near x n) x))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-16)
			(:instance near-trunc-20))))))

(local
(defthm near-trunc-case-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (< (+ x (expt 2 (- (expo x) n)))
		     (expt 2 (1+ (expo x))))
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (near x n)
		(trunc (+ x (expt 2 (- (expo x) n))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable exactp-near)
		  :use ((:instance near-trunc-21)
			(:instance exactp-near)
			(:instance near-trunc-15))))))

(defthm NEAR-TRUNC
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-trunc-1)
			(:instance near-trunc-case-1)
			(:instance near-trunc-case-2)
			(:instance near-trunc-case-3)))))

(local (defthm away-imp-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (< (trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)
		(+ x (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-upper-pos
				   (x (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m))))))
			(:instance expt-pos (x (- (1+ (expo x)) m)))
			(:instance expt-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n))))))))

(local (in-theory (disable abs-pos abs-away)))

(local (defthm away-imp-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (+ x (expt 2 (- (1+ (expo x)) n)))
		 (+ (away x n)
		    (expt 2 (- (1+ (expo (away x n))) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-lower-pos)
			(:instance expo-monotone (y (away x n)))
			(:instance expt-monotone
				   (n (- (1+ (expo x)) n)) (m (- (1+ (expo (away x n))) n))))))))

(local (defthm away-imp-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (< (trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)
		(+ (away x n)
		   (expt 2 (- (1+ (expo (away x n))) n)))))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-1 away-imp-2)))))

(local (defthm away-imp-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (<= (trunc (+ x
			   (expt 2 (- (1+ (expo x)) n))
			   (- (expt 2 (- (1+ (expo x)) m))))
			n)
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-3
			(:instance fp+1
				   (x (away x n))
				   (y (trunc (+ x
						(expt 2 (- (1+ (expo x)) n))
						(- (expt 2 (- (1+ (expo x)) m))))
					     n)))
			(:instance away-pos)
			(:instance away-exactp-b)
			(:instance trunc-exactp-b
				   (x (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m)))))))))))

(local (defthm away-imp-5
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (exactp x n))
	     (>= (trunc (+ x
			   (expt 2 (- (1+ (expo x)) n))
			   (- (expt 2 (- (1+ (expo x)) m))))
			n)
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-monotone
				   (y (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m))))))
			(:instance expt-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n)))
			(:instance trunc-exactp-a)
			(:instance away-exactp-a))))))

(local (defthm away-imp-6
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= x
		 (+ (trunc x n)
		    (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-exactp-a
			trunc-pos
			trunc-upper-pos
			trunc-exactp-b
			(:instance exactp-<= (x (trunc x n)) (n m) (m n))
			(:instance fp+1 (x (trunc x n)) (y x) (n m)))))))

(local (defthm away-imp-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (+ x
		    (expt 2 (- (1+ (expo x)) n))
		    (- (expt 2 (- (1+ (expo x)) m))))
		 (+ (trunc x n)
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-6)))))

(local (in-theory (disable expt-pos)))

(local (defthm away-imp-8
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (not (exactp x n)))
	     (> (+ (trunc x n)
		   (expt 2 (- (1+ (expo x)) n)))
		x))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp+2 (x (trunc x n)))
			(:instance trunc-exactp-b)
			(:instance trunc-pos)
			(:instance expt-pos (x (- (1+ (expo x)) n)))
			(:instance trunc-exactp-c
				   (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local (defthm away-imp-9
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (not (exactp x n)))
	     (>= (+ (trunc x n)
		   (expt 2 (- (1+ (expo x)) n)))
		(away x n)))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-8
			(:instance fp+2 (x (trunc x n)))
			(:instance trunc-exactp-b)
			(:instance trunc-pos)
			(:instance away-exactp-c
				   (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local (defthm away-imp-10
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (+ x
		    (expt 2 (- (1+ (expo x)) n))
		    (- (expt 2 (- (1+ (expo x)) m))))
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-7 away-imp-9)))))

(local (defthm away-imp-11
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (trunc (+ x
			   (expt 2 (- (1+ (expo x)) n))
			   (- (expt 2 (- (1+ (expo x)) m))))
			n)
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :use (away-imp-10
			away-exactp-b
			(:instance expt-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n)))
			(:instance trunc-exactp-c
				   (a (away x n))
				   (x (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m)))))))))))

(defthm AWAY-IMP
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
  :rule-classes ()
  :hints (("Goal" :use (away-imp-11 away-imp-5 away-imp-4))))

(local
(defthm hack-m7
    (implies (and (rationalp x)
		  (integerp k)
		  (integerp n))
	     (equal (EXPT 2 (+ 1 K (EXPO X) (* -1 N)))
		    (* (expt 2 k)
		       (EXPT 2 (+ 1 (EXPO X) (* -1 N))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- (1+ (expo x)) n)) (n k)))))))

(local
(defthm hack-m8
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (integerp n))
	     (EQUAL (* y
		       (EXPT 2 K)
		       (EXPT 2 (+ 1 (EXPO X) (* -1 N))))
		    (* (EXPT 2 K)
		       y
		       (EXPT 2 (+ 1 (EXPO X) (* -1 N))))))
  :rule-classes ()))


(defthm TRUNC-SHIFT
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (trunc (* x (expt 2 k)) n)
		(* (trunc x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc)
		  :use ((:instance sig-expo-shift (n k))
			(:instance expt-pos (x k))))
	  ("Goal'4'" :in-theory (disable a15)
		     :use (hack-m7))
	  ("Goal'8'" :use (:instance hack-m8 (y (FL (* (SIG X) (EXPT 2 (+ -1 N)))))))))

(defthm AWAY-SHIFT
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (away (* x (expt 2 k)) n)
		(* (away x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable away)
		  :use ((:instance sig-expo-shift (n k))
			(:instance expt-pos (x k))))
	  ("Goal'4'" :in-theory (disable a15)
		     :use (hack-m7))
	  ("Goal'8'" :use (:instance hack-m8 (y (cg (* (SIG X) (EXPT 2 (+ -1 N)))))))))

(defthm NEAR-SHIFT
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp k))
	     (= (near (* x (expt 2 k)) n)
		(* (near x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near)
		  :use (trunc-shift
			away-shift
			(:instance sig-expo-shift (n k))))))

(local
(defthm sgn-near-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (trunc x n)
		(* (sgn x) (trunc (abs x) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc)
		  :use (sig-minus expo-minus)))))

(local
(defthm sgn-near-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (away x n)
		(* (sgn x) (away (abs x) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable away)
		  :use (sig-minus expo-minus)))))

(defthm SGN-NEAR
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (near x n)
		(* (sgn x) (near (abs x) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near)
		  :use (sgn-near-2 sgn-near-1 sig-minus))))

(local (in-theory (disable integerp-expt)))

(defthm int-trunc
    (implies (and (rationalp x)
		  (integerp n)
		  (>= (expo x) n)
		  (> n 0))
	     (integerp (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc)
		  :use ((:instance integerp-expt (n (- (1+ (expo x)) n)))))))
