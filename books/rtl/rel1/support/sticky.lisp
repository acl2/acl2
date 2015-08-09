;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "divsqrt")

(defun STICKY (x n)
  (cond ((= n 1)
	 (* (sgn x) (expt 2 (expo x))))
	((exactp x (1- n))
	 x)
	(t
	 (+ (trunc x (1- n))
	    (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(local (defthm sgn-pos
    (implies (and (rationalp x)
		  (> x 0))
	     (equal (sgn x) 1))
  :hints (("Goal" :in-theory (enable sgn)))))

(defthm STICKY-POS
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (> (sticky x n) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance trunc-pos (n  (1- n)))
			(:instance expt-pos (x (expo x)))
			(:instance expt-pos (x (+ 1 (- N) (EXPO X))))))))

(defthm STICKY-SHIFT
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (sticky (* (expt 2 k) x) n)
		(* (expt 2 k) (sticky x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable exactp-shift expt-pos)
		  :use ((:instance expt-pos (x k))
			(:instance sig-expo-shift (n k))
			(:instance expo+ (m k) (n (expo x)))
			(:instance trunc-shift (n  (1- n)))
			(:instance exactp-shift (m (1- n)) (n k))
			(:instance exactp-shift (m (1- n)) (n (- k)) (x (* x (expt 2 k))))))))

(defthm STICKY-EXACTP
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-b)
		  :use ((:instance trunc-exactp-b (n  (1- n)))
			(:instance expo-trunc (n (1- n)))
			(:instance exactp-<= (m (1- n)))
			(:instance exactp-<= (x (trunc x (1- n))) (m (1- n)))
			(:instance trunc-pos (n (1- n)))
			(:instance exactp-2**n (n (expo x)) (m n))
			(:instance fp+2 (x (trunc x (1- n))))))))

(defthm STICKY-EXACTP-N-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (iff (exactp (sticky x n) (1- n))
		  (exactp x (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-b)
		  :use ((:instance trunc-exactp-b (n  (1- n)))
			(:instance expo-trunc (n (1- n)))
			(:instance expt-strong-monotone
				   (n (1+ (- (expo x) n)))
				   (m (+ 2 (- (expo x) n))))
			(:instance trunc-pos (n (1- n)))
			(:instance expt-pos (x (1+ (- (expo x) n))))
			(:instance fp+1
				   (y (sticky x n))
				   (n (1- n))
				   (x (trunc x (1- n))))))))

(local (in-theory (disable expt-pos)))

(local (defthm expo-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (<= (expt 2 (expo x))
		 (sticky x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-trunc (n (1- n)))
			(:instance expo-lower-bound (x (trunc x (1- n))))
			(:instance trunc-pos (n (1- n)))
			(:instance trunc-upper-pos (n (1- n)))
			(:instance expt-pos (x (1+ (- (expo x) n)))))))))

(local (defthm expo-sticky-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (<= (+ (trunc x (1- n))
		    (expt 2 (+ 2 (- (expo x) n))))
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-b)
		  :use ((:instance trunc-exactp-b (n  (1- n)))
			(:instance expo-trunc (n (1- n)))
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
			(:instance expo-upper-bound (x (trunc x (1- n))))
			(:instance expo-upper-bound)
			(:instance trunc-pos (n (1- n)))
			(:instance expt-pos (x (1+ (- (expo x) n))))
			(:instance fp+1
				   (y (expt 2 (1+ (expo x))))
				   (n (1- n))
				   (x (trunc x (1- n)))))))))

(local (defthm expo-sticky-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (< (sticky x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-b)
		  :use ((:instance expo-sticky-2)
			(:instance expo-upper-bound)
			(:instance expt-strong-monotone
				   (n (1+ (- (expo x) n)))
				   (m (+ 2 (- (expo x) n)))))))))

(local (defthm expo-sticky-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :use (expo-sticky-1
			expo-sticky-3
			sticky-pos
			(:instance expo-squeeze (x (sticky x n)) (n (expo x))))))))

(defthm EXPO-STICKY
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :use (expo-sticky-4
			expo-upper-bound
			expo-lower-bound
			(:instance expo-squeeze (x (expt 2 (expo x))) (n (expo x)))))))


(local (defthm trunc-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (trunc (sticky x n) (1- n))
		(trunc x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-exactp
			expo-sticky
			sticky-exactp-n-1
			sticky-pos
			(:instance trunc-trunc (n (1- n)) (m (1- n)))
			(:instance trunc-away-a (x (sticky x n)) (n (1- n))))))))

(defthm TRUNC-STICKY
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (trunc (sticky x n) m)
		(trunc x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use (trunc-sticky-1
			sticky-pos
			(:instance trunc-trunc (n (1- n)))
			(:instance trunc-trunc (n (1- n)) (x (sticky x n)))))))

(local (defthm away-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (= (away (sticky x n) (1- n))
		(+ (trunc x (1- n))
		   (expt 2 (+ (expo x) 2 (- n))))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-exactp
			expo-sticky
			sticky-exactp-n-1
			sticky-pos
			(:instance expo+ (m (1+ (- (expo x) n))) (n 1))
			(:instance trunc-away-b (x (sticky x n)) (n (1- n))))))))

(local (defthm away-sticky-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (<= (+ (trunc x (1- n))
		    (expt 2 (+ (expo x) 2 (- n))))
		 (away x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp+1 (x (trunc x (1- n))) (n (1- n)) (y (away x (1- n))))
			(:instance away-exactp-b (n (1- n)))
			(:instance trunc-exactp-b (n (1- n)))
			(:instance trunc-exactp-a (n (1- n)))
			(:instance trunc-pos (n (1- n)))
			(:instance trunc-upper-pos (n (1- n)))
			(:instance away-lower-pos (n (1- n))))))))

(local (defthm away-sticky-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (>= (+ (trunc x (1- n))
		    (expt 2 (+ (expo x) 2 (- n))))
		 (away x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp+2 (x (trunc x (1- n))) (n (1- n)))
			(:instance trunc-exactp-b (n (1- n)))
			(:instance trunc-pos (n (1- n)))
			(:instance trunc-diff-pos (n (1- n)))
			(:instance away-exactp-c
				   (n (1- n))
				   (a (+ (trunc x (1- n))
					 (expt 2 (+ (expo x) 2 (- n)))))))))))

(local (defthm away-sticky-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (away (sticky x n) (1- n))
		(away x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (away-sticky-1
			away-sticky-2
			away-sticky-3)))))

(defthm AWAY-STICKY
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use (away-sticky-4
			sticky-pos
			(:instance away-away (n (1- n)))
			(:instance away-away (n (1- n)) (x (sticky x n)))))))

(local (defthm near-sticky-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (not (= (near x m) (near y m))))
	     (= x (near-witness x y m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-near-lemma (n m))
			(:instance trunc-upper-pos (n (1+ m)))
			(:instance trunc-exactp-c (x y) (n (1+ m)) (a (near-witness x y m))))))))

(local (defthm near-sticky-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (away x (1+ m)) (away y (1+ m)))
		  (not (= (near x m) (near y m))))
	     (= y (near-witness x y m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-c)
		  :use ((:instance near-near-lemma (n m))
			(:instance away-lower-pos (x y) (n (1+ m)))
			(:instance away-exactp-c (n (1+ m)) (a (near-witness x y m))))))))

(local (defthm near-sticky-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< 0 y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (= (away x (1+ m)) (away y (1+ m))))
	     (= (near x m) (near y m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near-sticky-1 (x y) (y x))
			(:instance near-sticky-2 (x y) (y x))
			(:instance near-sticky-1)
			(:instance near-sticky-2))))))

(defthm NEAR-STICKY
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance near-sticky-3 (y (sticky x n)))
			(:instance trunc-sticky (m (1+ m)))
			(:instance away-sticky (m (1+ m)))
			sticky-pos))))

(in-theory (enable TRUNC-REWRITE))

(local (defthm minus-trunc-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (- (* x (expt 2 (- (1- k) (expo y))))
			  (fl (* y (expt 2 (- (1- k) (expo y))))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo+ (m (- (1- k) (expo y))) (n (- (1+ (expo y)) k))))))))

(local (defthm minus-trunc-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (- (fl (* (- y x) (expt 2 (- (1- k) (expo y))))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl+int expo trunc-rewrite)
		  :use ((:instance minus-trunc-1)
			exactp2
			(:instance fl+int
				   (x (* y (expt 2 (- (1- k) (expo y)))))
				   (n (- (* x (expt 2 (- (1- k) (expo y))))))))))))

(local (defthm minus-trunc-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (cg (* (- x y) (expt 2 (- (1- k) (expo y)))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cg)
		  :use ((:instance minus-trunc-2))))))

(in-theory (enable AWAY-REWRITE))

(defthm MINUS-TRUNC-4
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
  :rule-classes ()
  :hints (("Goal" :use ((:instance minus-trunc-3)))))

(defthm MINUS-TRUNC-5
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
  :rule-classes ()
  :hints (("Goal" :use ((:instance minus-trunc-2)
			(:instance expo-minus (x (- x y)))))))

(local (defthm sticky-plus-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (iff (exactp y (1- k))
		  (exactp (+ x y) (1- k2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp2 (n (1- k1)))
			(:instance exactp2 (x y) (n (1- k)))
			(:instance exactp2 (x (+ x y)) (n (1- k2))))))))

(local (defthm sticky-plus-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (exactp y (1- k))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-plus-1))))))

(local (defthm sticky-plus-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-plus-1
			(:instance plus-trunc (k (1- k)) (n (1- k1))))))))

(defthm STICKY-PLUS
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
  :rule-classes ()
  :hints (("Goal" :use (sticky-plus-2 sticky-plus-3))))

(local (defthm hack1
    (implies (and (integerp x)
		  (integerp y))
	     (integerp (- x y)))
  :rule-classes ()))

(local (defthm shack2
    (implies (and (rationalp x) (rationalp y))
	     (equal (+ X (* -1 (+ X (* -1 Y))))
		    y))
  :rule-classes ()))

(local (defthm shack3
    (implies (and (integerp x)
		  (rationalp y)
		  (integerp (- x y)))
	     (integerp y))
  :rule-classes ()
  :hints (("Goal" :use (shack2 (:instance hack1 (y (- x y))))))))

(local (defthm sticky-minus-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (iff (exactp y (1- k))
		  (exactp (- x y) (1- k2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance expo-minus (x y))
			(:instance shack3
				   (x (* X (EXPT 2 (+ -2 K (* -1 (EXPO (* -1 Y)))))))
				   (y (* Y (EXPT 2 (+ -2 K (* -1 (EXPO (* -1 Y)))))))))))))

(local (defthm sticky-minus-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (exactp y (1- k))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-minus-1))))))

(local (defthm sticky-minus-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(- (sticky (- y x) k2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance sticky-minus-1)
			(:instance expo-minus (x (- x y)))
			(:instance minus-trunc-5 (n (+ k (- (expo x) (expo y)))) (k (1- k))))))))

(local (defthm sticky-minus-4
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(- (away (- x y) (1- k2))
		   (expt 2 (1+ (- (expo (- x y)) k2))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-minus-1)
			(:instance minus-trunc-4 (n (+ -1 k (- (expo x) (expo y)))) (k (1- k))))))))

(defthm TRUNC-AWAY
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-sticky-2 (n (1+ n)))
			(:instance away-sticky-3 (n (1+ n)))))))

(in-theory (disable trunc-rewrite away-rewrite))

(local (defthm sticky-minus-5
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-minus-4)
			(:instance sticky-minus-1)
			(:instance trunc-away (x (- x y)) (n (1- k2)))
			(:instance expo+ (m (1+ (- (expo (- x y)) k2))) (n 1)))))))

(defthm trunc-minus
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (trunc (- x) n) (- (trunc x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn trunc-rewrite)
		  :use (expo-minus))))

(local (defthm shack4
    (implies (and (rationalp x)
		  (rationalp y))
	     (= (- (* x y))
		(* -1 x y)))
  :rule-classes ()))

(local (defthm shack5
    (implies (integerp x)
	     (integerp (- x)))
  :rule-classes ()))

(local (defthm shack6
    (implies (rationalp x)
	     (= (- (- x)) x))
  :rule-classes ()))

(local (defthm shack7
    (implies (and (rationalp x)
		  (integerp (- x)))
	     (integerp x))
  :rule-classes ()
  :hints (("Goal" :use (shack6
			(:instance shack5 (x (- x))))))))

(local (defthm shack8
    (implies (rationalp x)
	     (iff (integerp x)
		  (integerp (- x))))
  :rule-classes ()
  :hints (("Goal" :use (shack5
			shack7)))))

(defthm EXACTP-MINUS
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
		  (exactp (- x) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn exactp2)
		  :use (expo-minus
			(:instance shack8 (x (* X (EXPT 2 (+ -1 N (* -1 (EXPO X)))))))))))

(defthm STICKY-NEG
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (sticky (- x) n) (- (sticky x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn)
		  :use (expo-minus
			(:instance exactp-minus (n (1- n)))
			(:instance trunc-minus (n (1- n)))))))

(local (defthm sticky-minus-6
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (not (= y x))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance sticky-minus-2)
			(:instance sticky-minus-3)
			(:instance sticky-neg (x (- x y)) (n k2))
			(:instance sticky-minus-5))))))

(local (defthm sticky-0
    (implies (and (integerp n)
		  (> n 1))
	     (= (sticky 0 n) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc)))))

(local (defthm sticky-minus-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k2 1)
		  (exactp x (1- k)))
	     (= (- x (sticky x k))
		(sticky 0 k2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-0 (n k2)))))))

(defthm STICKY-MINUS
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
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance sticky-minus-7)
			(:instance sticky-minus-6)))))

(local (defthm sticky-lemma-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (< y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance sticky-minus (y (- y)))
			(:instance expo-minus (x y))
			(:instance sticky-neg (x y) (n k)))))))

(local (defthm sticky-lemma-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (= y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-0 (n k)))))))

(defthm STICKY-LEMMA
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
  :rule-classes ()
  :hints (("Goal" :use (sticky-plus sticky-lemma-1 sticky-lemma-2))))