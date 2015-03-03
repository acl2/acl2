(in-package "ACL2")

(include-book "../../rel9/lib/util")

(local (encapsulate ()

(local (include-book "../../rel9/lib/top"))

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

;;---------------------------------------------------------------------------------

(local-defthmd trunc-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n)))
           (equal (trunc x n) a))
  :hints (("Goal" :use (trunc-exactp-c
                        trunc-upper-pos
                        (:instance fp+2 (x a) (y (trunc x n)))))))

(local-defthmd away-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (<= x (fp+ a n)))
           (equal (away x n) (fp+ a n)))
  :hints (("Goal" :use (away-lower-pos
                        (:instance fp+1 (x a))
                        (:instance away-exactp-c (a (fp+ a n)))
                        (:instance fp+2 (x a) (y (away x n)))))))

(local-defthmd near-down-1
  (implies (and (integerp n) (integerp m))
           (= (expt 2 (+ 1 m n)) (* 2 (expt 2 (+ m n))))))

(local-defthm near-down-2
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (< (abs (- x a)) (abs (- x (+ a (expt 2 (- (1+ (expo a)) n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (near-down-1) (acl2::normalize-factors-gather-exponents)))))

(local-defthmd near-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (near x n) a))
  :hints (("Goal" :in-theory (disable acl2::EXPT-IS-INCREASING-FOR-BASE->-1)
                  :use (near-down-2
                        trunc-squeeze
                        away-squeeze
                        near-choice
                        near1-a))))

(local-defthm near-up-2
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (> x (+ a (expt 2 (- (expo a) n)))))
           (> (abs (- x a)) (abs (- x (+ a (expt 2 (- (1+ (expo a)) n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (near-down-1) (acl2::normalize-factors-gather-exponents)))))

(local-defthmd near-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (near x n) (fp+ a n)))
  :hints (("Goal" :in-theory (disable acl2::EXPT-IS-INCREASING-FOR-BASE->-1)
                  :use (near-up-2
                        trunc-squeeze
                        away-squeeze
                        near-choice
                        near1-b))))


;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From bits.lisp:

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;; From float.lisp:

(defund sgn (x) 
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (:? x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

;; From reps.lisp:

(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defund spn (q)
  (expt 2 (- 1 (bias q))))

(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))

(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       ;number of bits available in the sig field = p - 1 - ( - bias - expo(x))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))


;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm rtz-trunc
  (equal (rtz x n) (trunc x n))
  :hints (("Goal" :in-theory (enable rtz trunc))))

(defthmd rtz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (rtz x n)
		    (* (sgn x) 
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x))) 
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (trunc-rewrite))))

(defthmd rtz-minus
  (equal (rtz (* -1 x) n) (* -1 (rtz x n)))
  :hints (("Goal" :use trunc-minus)))

(defthmd abs-rtz
  (equal (abs (rtz x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("Goal" :use (abs-trunc))))

(defthm rtz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (rtz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (sgn (rtz x n))
		    (sgn x)))
  :hints (("Goal" :use (sgn-trunc))))

(defthm rtz-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n)))
            (< 0 (rtz x n)))
   :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-positive))))

(defthm rtz-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (rtz x n) 0))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-negative))))

(defthm rtz-neg-bits
    (implies (and (integerp n)
		  (<= n 0))
	     (equal (rtz x n) 0))
  :hints (("Goal" :use (trunc-to-0))))

(defthm rtz-0
  (equal (rtz 0 n) 0)
  :hints (("Goal" :use (trunc-0))))

(defthmd rtz-shift
  (implies (integerp n)
           (equal (rtz (* x (expt 2 k)) n)
                  (* (rtz x n) (expt 2 k))))
  :hints (("Goal" :use (trunc-shift))))

(defthm expo-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (rtz x n))
                    (expo x)))
  :hints (("Goal" :use (expo-trunc))))

(defthmd rtz-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (rtz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-bound))))

(defthmd rtz-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (rtz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-pos))))

(defthmd rtz-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (rtz x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-lower-bound))))

(defthm rtz-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (abs (- x (rtz x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-diff))))

(defthmd rtz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n)))
           (equal (rtz x n) a))
  :hints (("Goal" :use (trunc-squeeze))))

(defthm rtz-exactp-a
  (exactp (rtz x n) n)
  :hints (("Goal" :use (trunc-exactp-a))))

(defthmd rtz-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rtz x n))))
  :hints (("Goal" :use (trunc-exactp-b))))

(defthm rtz-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use (trunc-exactp-c))))

(defthmd rtz-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (rtz x n) (rtz y n)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-monotone))))

(defthmd rtz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rtz x n)
                    (- x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use (trunc-midpoint))))

(defthm rtz-rtz
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (rtz (rtz x n) m)
		    (rtz x m)))
  :hints (("Goal" :use (trunc-trunc))))

(defthm plus-rtz
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (rtz y k))
		(rtz (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use (plus-trunc))))

(defthm minus-rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (- x (rtz y k))
                (- (rtz (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ()
  :hints (("Goal" :use (minus-trunc-1))))

(defthmd bits-rtz
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (equal (rtz x k)
                  (* (expt 2 (- n k))
                     (bits x (1- n) (- n k)))))
  :hints (("Goal" :use (bits-trunc))))

(defthmd bits-rtz-bits
  (implies (and (rationalp x)
                (>= x 0)
                (integerp k)
                (integerp i)
                (integerp j)
                (> k 0)
                (>= (expo x) i)
                (>= j (- (1+ (expo x)) k)))
           (equal (bits (rtz x k) i j)
                  (bits x i j)))
  :hints (("Goal" :use (bits-trunc-bits))))

(defthmd rtz-split
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp m)
                (> m k)
                (integerp k)
                (> k 0))
           (equal (rtz x m)
                  (+ (rtz x k)
                     (* (expt 2 (- n m))
                        (bits x (1- (- n k)) (- n m))))))
  :hints (("Goal" :use (trunc-split))))

(defthmd rtz-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (equal (rtz x k)
                  (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :hints (("Goal" :use (trunc-logand))))


;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm raz-away
  (equal (raz x n) (away x n))
  :hints (("Goal" :in-theory (enable raz away))))

(defthmd raz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (raz x n)
		    (* (sgn x) 
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x))) 
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (away-rewrite))))

(defthmd raz-minus
  (equal (raz (* -1 x) n) (* -1 (raz x n)))
  :hints (("Goal" :use away-minus)))

(defthmd abs-raz
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (raz x n)) 
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use abs-away)))


(defthm raz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (raz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-raz
  (equal (sgn (raz x n))
         (sgn x))
  :hints (("Goal" :use sgn-away)))

(defthm raz-positive
  (implies (and (< 0 x)
                (case-split (rationalp x)))
           (< 0 (raz x n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-positive)))

(defthm raz-negative
    (implies (and (< x 0)
                  (case-split (rationalp x)))
	     (< (raz x n) 0))
    :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-negative)))

(defthm raz-neg-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n))
           (equal (raz x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
  :hints (("Goal" :use away-to-0)))

(defthm raz-0
  (equal (raz 0 n) 0)
  :hints (("Goal" :use away-0)))

(defthm raz-shift
    (implies (integerp n)
	     (= (raz (* x (expt 2 k)) n)
		(* (raz x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use away-shift)))

(defthmd raz-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (raz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-bound)))

(defthmd raz-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (raz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-pos)))

(defthmd raz-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (raz x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use away-upper-bound)))

(defthmd raz-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (raz x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use away-diff)))

(defthm raz-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (raz x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use away-expo-upper)))

(defthmd expo-raz-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (raz x n)) (expo x)))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-lower-bound)))

(defthmd expo-raz
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (raz x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (raz x n))
                    (expo x)))
  :hints (("Goal" :use expo-away)))

(defthmd expo-raz-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (raz x n)) (1+ (expo x))))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-upper-bound)))

(defthmd raz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (<= x (fp+ a n)))
           (equal (raz x n) (fp+ a n)))
  :hints (("Goal" :use (away-squeeze))))

(defthm raz-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (raz x n) n))
  :hints (("Goal" :use away-exactp-a)))

(defthmd raz-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (raz x n))))
  :hints (("Goal" :use away-exactp-b)))

(defthm raz-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use away-exactp-c)))

(defthmd raz-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (raz x n) (raz y n)))
  :rule-classes :linear
  :hints (("Goal" :use away-monotone)))

(defthmd rtz-raz
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (equal (raz x n)
	            (+ (rtz x n)
		       (expt 2 (+ (expo x) 1 (- n))))))
  :hints (("Goal" :use trunc-away)))

(defthmd raz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (raz x n)
		    (+ x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use away-midpoint)))

(defthmd raz-raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (raz (raz x n) m)
		    (raz x m)))
  :hints (("Goal" :use away-away)))

(defthm plus-raz
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (raz y k))
              (raz (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use plus-away)))

(defthm minus-rtz-raz
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                (exactp x (+ k (- (expo x) (expo y)))))
           (= (- x (rtz y k))
              (raz (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use minus-trunc-2)))

(defthm rtz-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                  (exactp x k1)
                  (> k2 0))
             (= (+ x (rtz y k))
                (if (= (sgn (+ x y)) (sgn y))
                    (rtz (+ x y) k2)
                  (raz (+ x y) k2))))
  :rule-classes ()
  :hints (("Goal" :use trunc-plus-minus)))

(defthmd raz-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (equal (raz x n)
		    (rtz (+ x
		    	    (expt 2 (- (1+ (expo x)) n))
			    (- (expt 2 (- (1+ (expo x)) m))))
		         n)))
  :hints (("Goal" :use away-imp)))

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(local-defthm rne-near
  (equal (rne x n) (near x n))
  :hints (("Goal" :in-theory (enable near rne))))

(defthm rne-choice
    (or (= (rne x n) (rtz x n))
	(= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near-choice)))

(defthmd rne-minus
  (equal (rne (* -1 x) n) (* -1 (rne x n)))
  :hints (("Goal" :use near-minus)))

(defthmd sgn-rne
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rne x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near)))

(defthm rne-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (rne x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-positive)))

(defthmd rne-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n))
           (< (rne x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-negative)))

(defthm rne-0
  (equal (rne 0 n) 0)
  :hints (("Goal" :use near-0)))

(defthm expo-rne
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (rne x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rne x n))
                    (expo x)))
  :hints (("Goal" :use expo-near)))

(defthm rne<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near<=away)))

(defthm rne>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rne x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use near>=trunc)))

(defthm rne-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (rne (* x (expt 2 k)) n)
		(* (rne x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near-shift)))

(defthm rne-exactp-a
    (implies (< 0 n)
	     (exactp (rne x n) n))
  :hints (("Goal" :use near-exactp-a)))

(defthmd rne-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rne x n))))
  :hints (("Goal" :use near-exactp-b)))

(defthm rne-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-c)))

(defthm rne-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-d)))

(defthmd rne-rtz
    (implies (and (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (rne x n)
                    (rtz x n)))
  :hints (("Goal" :use near1-a)))

(defthmd rne-raz
  (implies (and (> (abs (- x (rtz x n)))
                   (abs (- (raz x n) x)))
                (rationalp x)
                (integerp n))
           (equal (rne x n)
                  (raz x n)))
  :hints (("Goal" :use near1-b)))

(defthmd rne-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) a))
  :hints (("Goal" :use (near-down))))

(defthmd rne-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) (fp+ a n)))
  :hints (("Goal" :use (near-up))))

(defthm rne-nearest
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rne x n)))))
  :rule-classes ()
  :hints (("Goal" :use near2)))

(defthm rne-diff
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use near-est)))

(local-defthm ne-9
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= z 0)
                (<= y x))
           (<= (* y z) (* x z)))
  :rule-classes ())

(local-defthm ne-10
  (implies (and (rationalp x)
                (integerp n)
                (rationalp (abs x))
                (not (= x 0))
                (rationalp (expt 2 (expo x)))
                (rationalp (expt 2 (- n)))
                (>= (expt 2 (- n)) 0)
                (> n 0))
           (<= (* (expt 2 (expo x)) (expt 2 (- n)))
               (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (expo-lower-bound
                        (:instance ne-9 (y (expt 2 (expo x))) (x (abs x)) (z (expt 2 (- n)))))
                  :in-theory (theory 'minimal-theory))))

(local-defthm ne-11
  (implies (and (rationalp x)
                (not (= x 0))
                (integerp n)
                (> n 0))
           (<= (expt 2 (- (expo x) n))
               (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (ne-10))))

(local-defthm ne-12
    (implies (and (integerp n) 
		  (> n 0)
                  (not (= x 0))
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (rne-diff ne-11)
                  :in-theory (theory 'minimal-theory))))

(defthm rne-diff-cor
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (ne-12))))

(defthm rne-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (rne y n)))
  :rule-classes ()
  :hints (("Goal" :use near-monotone)))

(defund rne-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rne x n) (rne y n)) 2)
    (expt 2 (expo y))))

(defthm rne-rne-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (rne x n) (rne y n))))
	     (and (<= x (rne-witness x y n))
		  (<= (rne-witness x y n) y)
		  (exactp (rne-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rne-witness near-witness)
                  :use near-near-lemma)))

(defthm rne-rne
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
	     (<= (rne y k) (rne x k)))
  :rule-classes ()
  :hints (("Goal" :use near-near)))

(defthm rne-boundary
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (< 0 x)
		  (< x a)
		  (< a y)
		  (integerp n)
		  (> n 0)
		  (exactp a (1+ n))
		  (not (exactp a n)))
	     (< (rne x n) (rne y n)))
  :rule-classes ()
  :hints (("Goal" :use near-boundary)))

(defthm rne-exact
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (rne x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use near-exact)))

(defthm plus-rne
  (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rne y k))
              (rne (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near-plus)))

(defthmd rne-imp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (equal (rne x n)
   		    (if (and (exactp x (1+ n)) (not (exactp x n)))
		        (rtz (+ x (expt 2 (- (expo x) n))) (1- n))
		      (rtz (+ x (expt 2 (- (expo x) n))) n))))
  :hints (("Goal" :use near-trunc)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(local-defthm rna-near+
  (equal (rna x n) (near+ x n))
  :hints (("Goal" :in-theory (enable near+ rna))))

(defthm rna-choice
    (or (= (rna x n) (rtz x n))
	(= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-choice)))

(defthmd rna-minus
  (equal (rna (* -1 x) n) (* -1 (rna x n)))
  :hints (("Goal" :use near+-minus)))

(defthm rna<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+<=away)))

(defthm rna>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rna x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+>=trunc)))

(defthm rna-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (rna (* x (expt 2 k)) n)
		(* (rna x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near+-shift)))

(defthm rna-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-positive)))

(defthm rna-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-negative)))

(defthm rna-0
  (equal (rna 0 n) 0)
  :hints (("Goal" :use near+-0)))

(defthm sgn-rna
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rna x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near+)))

(defthm rna-exactp-a
    (implies (> n 0)
	     (exactp (rna x n) n))
  :hints (("Goal" :use (rna-choice rtz-exactp-a raz-exactp-a))))

(defthmd rna-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rna x n))))
  :hints (("Goal" :use near+-exactp-b)))

(defthm rna-exactp-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-c)))

(defthm rna-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-d)))

(defthmd expo-rna
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (rna x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rna x n))
                    (expo x)))
  :hints (("Goal" :use expo-near+)))

(defthmd rna-rtz
    (implies (and (rationalp x)
		  (integerp n)
		  (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (rtz x n)))
  :hints (("Goal" :use near+1-a)))

(defthmd rna-raz
    (implies (and (rationalp x)
		  (integerp n)
		  (> (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (raz x n)))
  :hints (("Goal" :use near+1-b)))

(defthm rna-nearest
    (implies (and (exactp y n)
                  (rationalp x)
                  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rna x n)))))
  :rule-classes ()
  :hints (("Goal" :use near+2)))

(defthm rna-diff
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rna x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use near+-est)))

(defthm rna-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rna x n) (rna y n)))
  :rule-classes ()
  :hints (("Goal" :use near+-monotone)))

(defthmd rna-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rna x n) (raz x n)))
  :hints (("Goal" :use near+-midpoint)))

(defthm rne-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rne x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near-power-a)))

(defthm rtz-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rtz (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near-power-b)))

(defthm rna-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rna x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near+-power)))

(defthm plus-rna
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rna y k))
              (rna (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near+-plus)))

(defthmd rna-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (equal (rna x n)
		    (rtz (+ x (expt 2 (- (expo x) n))) n)))
  :hints (("Goal" :use near+trunc)))

(defthmd rna-imp-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (equal (rna (rtz x n) m)
                    (rna x m)))
  :hints (("Goal" :use near+-trunc-cor)))

;;;**********************************************************************
;;;                          Odd Rounding
;;;**********************************************************************

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(local-defthm rto-sticky
  (equal (rto x n) (sticky x n))
  :hints (("Goal" :in-theory (enable rto sticky))))

(defthm sgn-rto
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rto x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-sticky)))

(defthmd rto-minus
  (equal (rto (* -1 x) n) (* -1 (rto x n)))
  :hints (("Goal" :use sticky-minus)))

(defthmd rto-positive
    (implies (and (< 0 x)
                  (rationalp x) 
		  (integerp n)
                  (> n 0))
	     (> (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-positive)))

(defthmd rto-negative
    (implies (and (< x 0)
                  (rationalp x) 
		  (integerp n)
                  (> n 0))
	     (< (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-negative)))

(defthm rto-0
  (equal (rto 0 n) 0)
  :hints (("Goal" :use sticky-0)))

(defthmd rto-minus
  (equal (rto (* -1 x) n) (* -1 (rto x n)))
  :hints (("Goal" :use sticky-minus)))

(defthm rto-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (rto (* (expt 2 k) x) n)
		(* (expt 2 k) (rto x n))))		
  :rule-classes ()
  :hints (("Goal" :use sticky-shift)))

(defthm expo-rto
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (equal (expo (rto x n))
		    (expo x)))
  :hints (("Goal" :use expo-sticky )))

(defthm rto-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (rto x n) n))
  :hints (("Goal" :use sticky-exactp-a)))

(defthmd rto-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rto x n))))
  :hints (("Goal" :use sticky-exactp-b)))

(defthm rto-exactp-c
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n) 
		  (> n m)
		  (> m 0))
	     (iff (exactp (rto x n) m)
		  (exactp x m)))
  :hints (("Goal" :use sticky-exactp-m)))

(defthmd rto-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rto x n) (rto y n)))
  :rule-classes :linear
  :hints (("Goal" :use sticky-monotone)))

(defthmd rtz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (rtz (rto x n) m)
		    (rtz x m)))
  :hints (("Goal" :use trunc-sticky)))

(defthmd raz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (raz (rto x n) m)
		    (raz x m)))
  :hints (("Goal" :use away-sticky)))

(defthmd rne-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rne (rto x n) m)
		    (rne x m)))
  :hints (("Goal" :use near-sticky)))

(defthmd rna-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rna (rto x n) m)
		    (rna x m)))
  :hints (("Goal" :use near+-sticky)))

(defthm rto-rto
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (equal (rto (rto x n) m)
		    (rto x m)))
  :hints (("Goal" :use sticky-sticky)))

(defthm rto-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (not (= y 0))
		  (not (= (+ x y) 0))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (rto y k))
		(rto (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use sticky-plus)))


;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

(defun rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(local-defthm rup-inf
  (equal (rup x n) (inf x n))
  :hints (("Goal" :in-theory (enable rup inf))))

(defthmd rup-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (rup x n) x))
  :rule-classes :linear
  :hints (("Goal" :use inf-lower-bound)))

(defun rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(local-defthm rdn-minf
  (equal (rdn x n) (minf x n))
  :hints (("Goal" :in-theory (enable rdn minf))))

(defthmd rdn-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (rdn x n) x))
  :rule-classes :linear
  :hints (("Goal" :use minf-lower-bound)))

(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(local-defund old-mode (mode)
  (case mode
    (raz 'away)
    (rna 'near+)
    (rtz 'trunc)
    (rup 'inf)
    (rdn 'minf)
    (rne 'near)
    (otherwise ())))

(local-defthm common-mode-rewrite
  (implies (common-mode-p mode)
           (common-rounding-mode-p (old-mode mode)))
  :hints (("Goal" :in-theory (enable IEEE-mode-p IEEE-rounding-mode-p common-mode-p common-rounding-mode-p old-mode))))

(defthm ieee-mode-is-common-mode
  (implies (IEEE-rounding-mode-p mode)
           (common-mode-p mode))
  :hints (("Goal" :in-theory (enable common-mode-p))))

(defund fp-rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(local-defthm fp-rnd-rnd
  (equal (fp-rnd x mode n) (rnd x (old-mode mode) n))
  :hints (("Goal" :in-theory (enable IEEE-rounding-mode-p common-mode-p fp-rnd old-mode rnd))))

(defthm rationalp-fp-rnd
  (rationalp (fp-rnd x mode n))
  :rule-classes (:type-prescription))

(defthm fp-rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode))
           (or (= (fp-rnd x mode n) (rtz x n))
	       (= (fp-rnd x mode n) (raz x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-choice (mode (old-mode mode)))))))

(defthmd sgn-fp-rnd
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (fp-rnd x mode n))
		    (sgn x)))
  :hints (("Goal" :use ((:instance sgn-rnd (mode (old-mode mode)))))))

(defthm fp-rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (> (fp-rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance rnd-positive (mode (old-mode mode)))))))

(defthm fp-rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (< (fp-rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance rnd-negative (mode (old-mode mode)))))))

(defthm fp-rnd-0
  (equal (fp-rnd 0 mode n)
         0)
  :hints (("Goal" :use ((:instance rnd-0 (mode (old-mode mode)))))))

(defthm fp-rnd-non-pos
    (implies (<= x 0)
	     (<= (fp-rnd x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use ((:instance rnd-non-pos (mode (old-mode mode)))))))

(defthm fp-rnd-non-neg
    (implies (<= 0 x)
	     (<= 0 (fp-rnd x mode n)))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use ((:instance rnd-non-neg (mode (old-mode mode)))))))

(defund flip-mode (m)
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(local-defthm old-mode-flip-mode
  (equal (old-mode (flip-mode mode))
         (flip (old-mode mode)))
  :hints (("Goal" :in-theory (enable old-mode flip flip-mode))))

(defthm ieee-rounding-mode-p-flip-mode
    (implies (ieee-rounding-mode-p m)
	     (ieee-rounding-mode-p (flip-mode m)))
  :hints (("Goal" :in-theory (enable ieee-rounding-mode-p flip-mode))))

(defthm common-mode-p-flip-mode
    (implies (common-mode-p m)
	     (common-mode-p (flip-mode m)))
  :hints (("Goal" :in-theory (enable common-mode-p ieee-rounding-mode-p flip-mode))))

(defthmd fp-rnd-minus
  (equal (fp-rnd (* -1 x) mode n)
         (* -1 (fp-rnd x (flip-mode mode) n)))
  :hints (("Goal" :use ((:instance rnd-minus (mode (old-mode mode)))))))

(defthm fp-rnd-exactp-a
    (implies (< 0 n)
	     (exactp (fp-rnd x mode n) n))
  :hints (("Goal" :use ((:instance rnd-exactp-a (mode (old-mode mode)))))))

(defthmd fp-rnd-exactp-b
  (implies (and (rationalp x)
                (common-mode-p mode)
                (integerp n) 
                (> n 0))
           (equal (exactp x n)
                  (equal x (fp-rnd x mode n))))
  :hints (("Goal" :use ((:instance rnd-exactp-b (mode (old-mode mode)))))))

(defthm fp-rnd-exactp-c
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (fp-rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-exactp-c (mode (old-mode mode)))))))

(defthm fp-rnd-exactp-d
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (fp-rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-exactp-d (mode (old-mode mode)))))))

(defthm fp-rnd<=raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (common-mode-p mode)
		  (natp n))
	     (<= (fp-rnd x mode n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd<=away (mode (old-mode mode)))))))

(defthm fp-rnd>=rtz
    (implies (and (rationalp x)
		  (> x 0) ;; 
		  (common-mode-p mode)
                  (integerp n)
                  (> N 0))
	     (>= (fp-rnd x mode n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd>=trunc (mode (old-mode mode)))))))

(local (include-book "rnd-near-equal"))

(defthm fp-rnd<equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n)))
                (< (rtz x (1+ n)) y)
                (< y x)
                ;; (:instance near+-near+ (y x) (x y) (k n) (a (rtz x (1+ n))))
                (implies (and (rationalp (rtz x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz x (1+ n)))
		              (< (rtz x (1+ n)) y)
		              (< x (fp+ (rtz x (1+ n)) (1+ n)))
		              (exactp (rtz x (1+ n)) (1+ n)))
	                 (<= (rna x n) (rna y n))))
           (= (fp-rnd y mode n) (fp-rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd<equal (mode (old-mode mode)))))))

(defthm fp-rnd>equal
  (implies (and (rationalp x)
                (rationalp y)
                (common-mode-p mode)
                (natp n)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n)))
                (< y (raz x (1+ n)))
                (< x y)
                ;; (:instance near+-near+ (k n) (a (rtz x (1+ n))))
                (implies (and (rationalp (rtz x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz x (1+ n)))
		              (< (rtz x (1+ n)) x)
		              (< y (fp+ (rtz x (1+ n)) (1+ n)))
		              (exactp (rtz x (1+ n)) (1+ n)))
	                 (<= (rna y n) (rna x n))))
           (= (fp-rnd y mode n) (fp-rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd>equal (mode (old-mode mode)))))))

(defthm fp-rnd-near-equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n)))
                ;; (:instance near+-near+ (y x) (x y) (k n) (a (rtz x (1+ n))))
                (implies (and (rationalp (rtz x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz x (1+ n)))
		              (< (rtz x (1+ n)) y)
		              (< x (fp+ (rtz x (1+ n)) (1+ n)))
		              (exactp (rtz x (1+ n)) (1+ n)))
	                 (<= (rna x n) (rna y n)))
                ;; (:instance near+-near+ (k n) (a (rtz x (1+ n))))
                (implies (and (rationalp (rtz x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz x (1+ n)))
		              (< (rtz x (1+ n)) x)
		              (< y (fp+ (rtz x (1+ n)) (1+ n)))
		              (exactp (rtz x (1+ n)) (1+ n)))
	                 (<= (rna y n) (rna x n))))
           (let ((d (min (- x (rtz x (1+ n))) (- (raz x (1+ n)) x))))
             (and (> d 0)
                  (implies (< (abs (- x y)) d)
                           (= (fp-rnd y mode n) (fp-rnd x mode n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-near-equal (mode (old-mode mode)))))))

(defthm fp-rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (< (abs (- x (fp-rnd x mode n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-diff (mode (old-mode mode)))))))

(defthmd expo-fp-rnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode)
		  (not (= (abs (fp-rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (equal (expo (fp-rnd x mode n))
                    (expo x)))
  :hints (("Goal" :use ((:instance expo-rnd (mode (old-mode mode)))))))

(defthm fp-rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-mode-p mode)
                  (integerp N)
                  (> N 0))
	     (<= (fp-rnd x mode n) (fp-rnd y mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-monotone (mode (old-mode mode)))))))

(defthm fp-rnd-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (common-mode-p mode)
		  (integerp k))
	     (= (fp-rnd (* x (expt 2 k)) mode n)
		(* (fp-rnd x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-shift (mode (old-mode mode)))))))

(defthm plus-fp-rnd
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y))))
                (common-mode-p mode))
           (= (+ x (fp-rnd y mode k))
              (fp-rnd (+ x y)
                   mode
                   (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance plus-rnd (mode (old-mode mode)))))))

(defthmd fp-rnd-rto
  (implies (and (common-mode-p mode)
                (rationalp x)
                (integerp m) 
		(> m 0)
                (integerp n) 
		(>= n (+ m 2)))
           (equal (fp-rnd (rto x n) mode m)
                  (fp-rnd x mode m)))
  :hints (("Goal" :use ((:instance rnd-sticky (mode (old-mode mode)))))))

(defun fp-rnd-const (e mode n)
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defthmd fp-rnd-const-thm
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (equal (fp-rnd x mode n)
                    (if (and (eql mode 'rne)
                             (exactp x (1+ n))
		             (not (exactp x n)))
		        (rtz (+ x (fp-rnd-const (expo x) mode n)) (1- n))
                      (rtz (+ x (fp-rnd-const (expo x) mode n)) n))))
  :hints (("Goal" :in-theory (enable ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p rnd-const fp-rnd-const)
                  :use ((:instance rnd-const-thm (mode (old-mode mode)))))))

(defund round-up-p (x sticky mode n)
  (case mode
    (rna (= (bitn x (- (expo x) n)) 1))
    (rne (and (= (bitn x (- (expo x) n)) 1)
               (or (not (= (bits x (- (expo x) (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((rup raz) (or (not (= (bits x (- (expo x) n) 0) 0))
                    (= sticky 1)))
    (otherwise ())))

(defthmd round-up-p-thm$
  (implies (and (common-mode-p mode)
                (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (rtz r k))
                  (sticky (if (< x r) 1 0)))
	     (equal (fp-rnd r mode n)
                    (if (round-up-p x sticky mode n)
                        (fp+ (rtz r n) n)
                      (rtz r n)))))
  :hints (("Goal" :in-theory (enable round-up-p ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p rnd-const fp-rnd-const)
                  :use ((:instance round-up-thm (mode (old-mode mode)))))))
  

;;;**********************************************************************
;;;                         Denormal Rounding 
;;;**********************************************************************

(defund denorm-rnd (x mode p q)
  (fp-rnd x mode (+ p (expo x) (- (expo (spn q))))))

(local-defthm denorm-rnd-drnd
  (equal (denorm-rnd x mode p q)
         (drnd x (old-mode mode) p q))
  :hints (("Goal" :in-theory (enable denorm-rnd drnd))))

(defthmd denorm-rnd-minus
  (equal (denorm-rnd (* -1 x) mode p q)
         (* -1 (denorm-rnd x (flip-mode mode) p q)))
  :hints (("Goal" :use ((:instance drnd-minus (mode (old-mode mode)))))))

(defthm denorm-rnd-exactp-a
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (or (drepp (denorm-rnd x mode p q) p q)
               (= (denorm-rnd x mode p q) 0)
               (= (denorm-rnd x mode p q) (* (sgn x) (spn q)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-a (mode (old-mode mode)))))))

(defthmd denorm-rnd-exactp-b
  (implies (and (rationalp x)
	        (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (equal (denorm-rnd x mode p q)
                  x))
  :hints (("Goal" :use ((:instance drnd-exactp-b (mode (old-mode mode)))))))

(defthm denorm-rnd-exactp-c
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(>= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (>= a (denorm-rnd x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-c (mode (old-mode mode)))))))

(defthm denorm-rnd-exactp-d
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(<= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (<= a (denorm-rnd x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-d (mode (old-mode mode)))))))

(defthm denorm-rnd-rtz
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (abs (denorm-rnd x 'rtz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use drnd-trunc)))

(defthm denorm-rnd-raz
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (abs (denorm-rnd x 'raz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use drnd-away)))

(defthm denorm-rnd-rdn
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (denorm-rnd x 'rdn p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use drnd-minf)))

(defthm denorm-rnd-rup
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (denorm-rnd x 'rup p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use drnd-inf)))

(defthm denorm-rnd-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (< (abs (- x (denorm-rnd x mode p q))) (spd p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-diff (mode (old-mode mode)))))))

(defthm denorm-rnd-rne-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (denorm-rnd x 'rne p q)))))
  :rule-classes ()
  :hints (("Goal" :use drnd-near-est)))

(defthm denorm-rnd-rna-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (denorm-rnd x 'rna p q)))))
  :rule-classes ()
  :hints (("Goal" :use drnd-near+-est)))

(defthmd denorm-rnd-rto
    (implies (and (common-mode-p mode)
		  (natp p)
		  (> p 1)
		  (natp q)
		  (> q 0)
		  (rationalp x)
                  (<= (abs x) (spn q))
		  (natp n)
		  (>= n (+ p (expo x) (- (expo (spn q))) 2)))
	     (equal (denorm-rnd (rto x n) mode p q)
		    (denorm-rnd x mode p q)))
  :hints (("Goal" :use ((:instance drnd-sticky (mode (old-mode mode)))))))

(defthmd denorm-rnd-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (common-mode-p mode)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (denorm-rnd x mode p q)
                  (- (fp-rnd (+ x (* (sgn x) (spn q))) mode p)
		     (* (sgn x) (spn q)))))
  :hints (("Goal" :use ((:instance drnd-rewrite (mode (old-mode mode)))))))

(defthmd denorm-rnd-tiny
  (implies (and (common-mode-p mode)
                (natp p)
                (> p 1)
                (natp q)
                (> q 0)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd p q) 2)))
           (equal (denorm-rnd x mode p q)
                  (if (member mode '(raz rup))
                      (spd p q)
                     0)))
  :hints (("Goal" :in-theory (enable ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p)
                  :use ((:instance drnd-tiny (mode (old-mode mode)))))))

(defthm denorm-rnd-tiny-equal
    (implies (and (common-mode-p mode)
                  (natp p)
                  (> p 1)
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd p q) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd p q) 2)))
             (equal (denorm-rnd x mode p q)
                    (denorm-rnd y mode p q)))
    :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-tiny-equal (mode (old-mode mode)))))))
))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From bits.lisp:

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;; From float.lisp:

(defund sgn (x) 
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (:? x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

;; From reps.lisp:

(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defund spn (q)
  (expt 2 (- 1 (bias q))))

(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))

(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       ;number of bits available in the sig field = p - 1 - ( - bias - expo(x))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))


;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defthmd rtz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (rtz x n)
		    (* (sgn x) 
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x))) 
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (trunc-rewrite))))

(defthmd rtz-minus
  (equal (rtz (* -1 x) n) (* -1 (rtz x n)))
  :hints (("Goal" :use trunc-minus)))

(defthmd abs-rtz
  (equal (abs (rtz x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("Goal" :use (abs-trunc))))

(defthm rtz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (rtz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (sgn (rtz x n))
		    (sgn x)))
  :hints (("Goal" :use (sgn-trunc))))

(defthm rtz-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n)))
            (< 0 (rtz x n)))
   :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-positive))))

(defthm rtz-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (rtz x n) 0))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-negative))))

(defthm rtz-neg-bits
    (implies (and (integerp n)
		  (<= n 0))
	     (equal (rtz x n) 0))
  :hints (("Goal" :use (trunc-to-0))))

(defthm rtz-0
  (equal (rtz 0 n) 0)
  :hints (("Goal" :use (trunc-0))))

(defthmd rtz-shift
  (implies (integerp n)
           (equal (rtz (* x (expt 2 k)) n)
                  (* (rtz x n) (expt 2 k))))
  :hints (("Goal" :use (trunc-shift))))

(defthm expo-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (rtz x n))
                    (expo x)))
  :hints (("Goal" :use (expo-trunc))))

(defthmd rtz-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (rtz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-bound))))

(defthmd rtz-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (rtz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-pos))))

(defthmd rtz-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (rtz x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-lower-bound))))

(defthm rtz-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (abs (- x (rtz x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-diff))))

(defthmd rtz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n)))
           (equal (rtz x n) a))
  :hints (("Goal" :use (trunc-squeeze))))

(defthm rtz-exactp-a
  (exactp (rtz x n) n)
  :hints (("Goal" :use (trunc-exactp-a))))

(defthmd rtz-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rtz x n))))
  :hints (("Goal" :use (trunc-exactp-b))))

(defthm rtz-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use (trunc-exactp-c))))

(defthmd rtz-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (rtz x n) (rtz y n)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-monotone))))

(defthmd rtz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rtz x n)
                    (- x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use (trunc-midpoint))))

(defthm rtz-rtz
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (rtz (rtz x n) m)
		    (rtz x m)))
  :hints (("Goal" :use (trunc-trunc))))

(defthm plus-rtz
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (rtz y k))
		(rtz (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use (plus-trunc))))

(defthm minus-rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (- x (rtz y k))
                (- (rtz (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ()
  :hints (("Goal" :use (minus-trunc-1))))

(defthmd bits-rtz
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (equal (rtz x k)
                  (* (expt 2 (- n k))
                     (bits x (1- n) (- n k)))))
  :hints (("Goal" :use (bits-trunc))))

(defthmd bits-rtz-bits
  (implies (and (rationalp x)
                (>= x 0)
                (integerp k)
                (integerp i)
                (integerp j)
                (> k 0)
                (>= (expo x) i)
                (>= j (- (1+ (expo x)) k)))
           (equal (bits (rtz x k) i j)
                  (bits x i j)))
  :hints (("Goal" :use (bits-trunc-bits))))

(defthmd rtz-split
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp m)
                (> m k)
                (integerp k)
                (> k 0))
           (equal (rtz x m)
                  (+ (rtz x k)
                     (* (expt 2 (- n m))
                        (bits x (1- (- n k)) (- n m))))))
  :hints (("Goal" :use (trunc-split))))

(defthmd rtz-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) ;(> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (equal (rtz x k)
                  (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :hints (("Goal" :use (trunc-logand))))


;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defthmd raz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (raz x n)
		    (* (sgn x) 
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x))) 
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (away-rewrite))))

(defthmd raz-minus
  (equal (raz (* -1 x) n) (* -1 (raz x n)))
  :hints (("Goal" :use away-minus)))

(defthmd abs-raz
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (raz x n)) 
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use abs-away)))


(defthm raz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (raz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-raz
  (equal (sgn (raz x n))
         (sgn x))
  :hints (("Goal" :use sgn-away)))

(defthm raz-positive
  (implies (and (< 0 x)
                (case-split (rationalp x)))
           (< 0 (raz x n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-positive)))

(defthm raz-negative
    (implies (and (< x 0)
                  (case-split (rationalp x)))
	     (< (raz x n) 0))
    :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-negative)))

(defthm raz-neg-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n))
           (equal (raz x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
  :hints (("Goal" :use away-to-0)))

(defthm raz-0
  (equal (raz 0 n) 0)
  :hints (("Goal" :use away-0)))

(defthm raz-shift
    (implies (integerp n)
	     (= (raz (* x (expt 2 k)) n)
		(* (raz x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use away-shift)))

(defthmd raz-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (raz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-bound)))

(defthmd raz-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (raz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-pos)))

(defthmd raz-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (raz x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use away-upper-bound)))

(defthmd raz-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (raz x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use away-diff)))

(defthm raz-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (raz x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use away-expo-upper)))

(defthmd expo-raz-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (raz x n)) (expo x)))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-lower-bound)))

(defthmd expo-raz
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (raz x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (raz x n))
                    (expo x)))
  :hints (("Goal" :use expo-away)))

(defthmd expo-raz-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (raz x n)) (1+ (expo x))))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-upper-bound)))

(defthmd raz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (<= x (fp+ a n)))
           (equal (raz x n) (fp+ a n)))
  :hints (("Goal" :use (away-squeeze))))

(defthm raz-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (raz x n) n))
  :hints (("Goal" :use away-exactp-a)))

(defthmd raz-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (raz x n))))
  :hints (("Goal" :use away-exactp-b)))

(defthm raz-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use away-exactp-c)))

(defthmd raz-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (raz x n) (raz y n)))
  :rule-classes :linear
  :hints (("Goal" :use away-monotone)))

(defthmd rtz-raz
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (equal (raz x n)
	            (+ (rtz x n)
		       (expt 2 (+ (expo x) 1 (- n))))))
  :hints (("Goal" :use trunc-away)))

(defthmd raz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (raz x n)
		    (+ x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use away-midpoint)))

(defthmd raz-raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (raz (raz x n) m)
		    (raz x m)))
  :hints (("Goal" :use away-away)))

(defthm plus-raz
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (raz y k))
              (raz (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use plus-away)))

(defthm minus-rtz-raz
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                (exactp x (+ k (- (expo x) (expo y)))))
           (= (- x (rtz y k))
              (raz (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use minus-trunc-2)))

(defthm rtz-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                  (exactp x k1)
                  (> k2 0))
             (= (+ x (rtz y k))
                (if (= (sgn (+ x y)) (sgn y))
                    (rtz (+ x y) k2)
                  (raz (+ x y) k2))))
  :rule-classes ()
  :hints (("Goal" :use trunc-plus-minus)))

(defthmd raz-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (equal (raz x n)
		    (rtz (+ x
		    	    (expt 2 (- (1+ (expo x)) n))
			    (- (expt 2 (- (1+ (expo x)) m))))
		         n)))
  :hints (("Goal" :use away-imp)))

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defthm rne-choice
    (or (= (rne x n) (rtz x n))
	(= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near-choice)))

(defthmd rne-minus
  (equal (rne (* -1 x) n) (* -1 (rne x n)))
  :hints (("Goal" :use near-minus)))

(defthmd sgn-rne
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rne x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near)))

(defthm rne-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (rne x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-positive)))

(defthmd rne-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n))
           (< (rne x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-negative)))

(defthm rne-0
  (equal (rne 0 n) 0)
  :hints (("Goal" :use near-0)))

(defthm expo-rne
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (rne x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rne x n))
                    (expo x)))
  :hints (("Goal" :use expo-near)))

(defthm rne<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near<=away)))

(defthm rne>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rne x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use near>=trunc)))

(defthm rne-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (rne (* x (expt 2 k)) n)
		(* (rne x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near-shift)))

(defthm rne-exactp-a
    (implies (< 0 n)
	     (exactp (rne x n) n))
  :hints (("Goal" :use near-exactp-a)))

(defthmd rne-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rne x n))))
  :hints (("Goal" :use near-exactp-b)))

(defthm rne-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-c)))

(defthm rne-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-d)))

(defthmd rne-rtz
    (implies (and (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (rne x n)
                    (rtz x n)))
  :hints (("Goal" :use near1-a)))

(defthmd rne-raz
  (implies (and (> (abs (- x (rtz x n)))
                   (abs (- (raz x n) x)))
                (rationalp x)
                (integerp n))
           (equal (rne x n)
                  (raz x n)))
  :hints (("Goal" :use near1-b)))

(defthmd rne-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) a))
  :hints (("Goal" :use (near-down))))

(defthmd rne-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) (fp+ a n)))
  :hints (("Goal" :use (near-up))))

(defthm rne-nearest
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rne x n)))))
  :rule-classes ()
  :hints (("Goal" :use near2)))

(defthm rne-diff
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use near-est)))

(defthm rne-diff-cor
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (ne-12))))

(defthm rne-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  ;(<= 0 x) ;; not necessary
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (rne y n)))
  :rule-classes ()
  :hints (("Goal" :use near-monotone)))

(defund rne-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rne x n) (rne y n)) 2)
    (expt 2 (expo y))))

(defthm rne-rne-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (rne x n) (rne y n))))
	     (and (<= x (rne-witness x y n))
		  (<= (rne-witness x y n) y)
		  (exactp (rne-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rne-witness near-witness)
                  :use near-near-lemma)))

(defthm rne-rne
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
	     (<= (rne y k) (rne x k)))
  :rule-classes ()
  :hints (("Goal" :use near-near)))

(defthm rne-boundary
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (< 0 x)
		  (< x a)
		  (< a y)
		  (integerp n)
		  (> n 0)
		  (exactp a (1+ n))
		  (not (exactp a n)))
	     (< (rne x n) (rne y n)))
  :rule-classes ()
  :hints (("Goal" :use near-boundary)))

(defthm rne-exact
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (rne x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use near-exact)))

(defthm plus-rne
  (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rne y k))
              (rne (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near-plus)))

(defthmd rne-imp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (equal (rne x n)
   		    (if (and (exactp x (1+ n)) (not (exactp x n)))
		        (rtz (+ x (expt 2 (- (expo x) n))) (1- n))
		      (rtz (+ x (expt 2 (- (expo x) n))) n))))
  :hints (("Goal" :use near-trunc)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defthm rna-choice
    (or (= (rna x n) (rtz x n))
	(= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-choice)))

(defthmd rna-minus
  (equal (rna (* -1 x) n) (* -1 (rna x n)))
  :hints (("Goal" :use near+-minus)))

(defthm rna<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+<=away)))

(defthm rna>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rna x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use near+>=trunc)))

(defthm rna-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (rna (* x (expt 2 k)) n)
		(* (rna x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near+-shift)))

(defthm rna-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-positive)))

(defthm rna-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-negative)))

(defthm rna-0
  (equal (rna 0 n) 0)
  :hints (("Goal" :use near+-0)))

(defthm sgn-rna
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rna x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near+)))

(defthm rna-exactp-a
    (implies (> n 0)
	     (exactp (rna x n) n))
  :hints (("Goal" :use (rna-choice rtz-exactp-a raz-exactp-a))))

(defthmd rna-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rna x n))))
  :hints (("Goal" :use near+-exactp-b)))

(defthm rna-exactp-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-c)))

(defthm rna-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-d)))

(defthmd expo-rna
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (rna x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rna x n))
                    (expo x)))
  :hints (("Goal" :use expo-near+)))

(defthmd rna-rtz
    (implies (and (rationalp x)
		  (integerp n)
		  (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (rtz x n)))
  :hints (("Goal" :use near+1-a)))

(defthmd rna-raz
    (implies (and (rationalp x)
		  (integerp n)
		  (> (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (raz x n)))
  :hints (("Goal" :use near+1-b)))

(defthm rna-nearest
    (implies (and (exactp y n)
                  (rationalp x)
                  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rna x n)))))
  :rule-classes ()
  :hints (("Goal" :use near+2)))

(defthm rna-diff
    (implies (and (integerp n) 
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rna x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use near+-est)))

(defthm rna-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rna x n) (rna y n)))
  :rule-classes ()
  :hints (("Goal" :use near+-monotone)))

(encapsulate ()

(local (include-book "../../rel9/lib/top"))

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(defun rna-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rna x n) (rna y n)) 2)
    (expt 2 (expo y))))

(local-defthm expt-monotone
  (implies (and (integerp n) (integerp m) (<= n m))
           (<= (expt 2 n) (expt 2 m)))
  :rule-classes ())

(local-defthm rna-rna-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (expo x) (expo y))))
	     (and (<= x (rna-witness x y n))
		  (<= (rna-witness x y n) y)
		  (exactp (rna-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS acl2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-< 
                                      acl2::|(< (expt x n) (expt x m))| rna)
		  :use ((:instance exactp-2**n (n (expo y)) (m (1+ n)))
			(:instance expo-upper-bound)
			(:instance expo-monotone)
			(:instance expt-monotone (n (1+ (expo x))) (m (expo y)))
			(:instance expo-lower-bound (x y))))))

(local-defthm rna-rna-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (rna x n) (rna y n))
		  (= (expo x) (expo y)))
	     (and (<= x (rna-witness x y n))
		  (<= (rna-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rna)
		  :use ((:instance rna-nearest (y (rna y n)))
			(:instance rna-nearest (x y) (y (rna x n)))
			(:instance rna-positive)
			(:instance rna-positive (x y))))))

(local-defthm rna-rna-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (rna x n) (rna y n)))
		  (= (expo x) (expo y)))
	     (and (<= x (rna-witness x y n))
		  (<= (rna-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rna rna-witness)
		  :use ((:instance rna-rna-2)
			(:instance rna-monotone)))))

(local-defthm rna-rna-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (rna x n) (rna y n))
		  (= (expo x) (expo y)))
	     (<= (expo (rna-witness x y n)) (expo y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rna abs-raz)
		  :use ((:instance rna<=raz (x y))
			(:instance raz-expo-upper (x y))
			(:instance rna-positive)
			(:instance raz-positive (x y))
			(:instance expo<= (x (rna-witness x y n)) (n (expo y)))))))

(local-defthm rna-neg
    (implies (and (rationalp x)
		  (< x 0)
		  (integerp n)
		  (> n 0))
	     (< (rna x n) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rna)
		  :use ((:instance rna-choice)
			(:instance rtz-negative)
			(:instance raz-negative)))))

(local-defthm rna-0-0
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= (rna x n) 0)
		  (= x 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (sgn) (rna))
		  :use (sgn-rtz sgn-raz (:instance rna-choice)))))

(local-defthm exactp-<=-expo
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp e)
		  (<= e (expo x))
		  (exactp x n))
	     (integerp (* x (expt 2 (- (1- n) e)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use ((:instance exactp-<= (m n) (n (+ n (- (expo x) e))))))))

(local-defthm rna-rna-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (rna x n) (rna y n))
		  (= (expo x) (expo y)))
	     (integerp (* (rna x n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (sgn) (rna expo-rtz abs-rtz abs-raz))
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (rna x n)))
			(:instance expo-monotone (x (rtz x n)) (y (rna x n)))
			(:instance rna-0-0)
			(:instance rtz-positive)
			(:instance rna-positive)
			(:instance expo-rtz)
			(:instance sgn-rtz)
			(:instance rna>=rtz)))))

(local-defthm rna-rna-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (rna x n) (rna y n))
		  (= (expo x) (expo y)))
	     (integerp (* (rna y n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (sgn) (rna expo-rtz abs-rtz abs-raz))
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (rna y n)))
			(:instance expo-monotone (x (rtz x n)) (y (rna y n)))
			(:instance rna-0-0)
			(:instance rna-monotone)
			(:instance rtz-positive)
			(:instance rna-positive)
			(:instance expo-rtz)
			(:instance sgn-rtz)
			(:instance rna>=rtz)))))

(local-in-theory (disable rna))

(local-defthm rna-rna-7
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k))
	     (= (+ (* x (expt 2 (1- k)))
		   (* y (expt 2 (1- k))))
		(* (/ (+ x y) 2) (expt 2 k))))
  :rule-classes ())

(local-defthm rna-rna-8
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
	          (integerp (* x (expt 2 (1- k))))
	          (integerp (* y (expt 2 (1- k)))))
	     (integerp (* (/ (+ x y) 2) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rna-rna-7)))))

(local-defthm exactp->=-expo
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp e)
		  (>= e (expo x))
		  (integerp (* x (expt 2 (- (1- n) e)))))
	     (exactp x n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use ((:instance exactp-<= (m (+ n (- (expo x) e))))))))

(local-defthm rna-rna-9
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (rna x n) (rna y n))
		  (= (expo x) (expo y)))
	     (exactp (rna-witness x y n) (1+ n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rna-rna-5)
			(:instance rna-rna-6)
			(:instance rna-rna-4)
			(:instance rna-rna-8 (x (rna x n)) (y (rna y n)) (k (- n (expo y))))
			(:instance exactp->=-expo (n (1+ n)) (e (expo y)) (x (rna-witness x y n)))))))

(defthm rna-rna-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (rna x n) (rna y n))))
	     (and (<= x (rna-witness x y n))
		  (<= (rna-witness x y n) y)
		  (exactp (rna-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rna)
		  :use ((:instance rna-rna-2)
			(:instance rna-rna-1)
			(:instance rna-rna-9)
			(:instance rna-monotone)))))

(local-in-theory (disable rna-witness rna))

(local-defthm rna-rna-10
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
		  (< x y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (= (rna y k) (rna x k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rna-rna-lemma (n k))
			(:instance exactp-<= (x (rna-witness x y k)) (m (1+ k)) (n (1+ n)))
			(:instance fp+2 (x a) (y (rna-witness x y k)) (n (1+ n)))))))

(defthm rna-rna
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
	     (<= (rna y k) (rna x k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rna-rna-10)
			(:instance rna-monotone (n k) (x y) (y x))))))
)

(defthmd rna-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rna x n) (raz x n)))
  :hints (("Goal" :use near+-midpoint)))

(defthm rne-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rne x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm rtz-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rtz (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm rna-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rna x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm plus-rna
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rna y k))
              (rna (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near+-plus)))

(defthmd rna-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (equal (rna x n)
		    (rtz (+ x (expt 2 (- (expo x) n))) n)))
  :hints (("Goal" :use near+trunc)))

(defthmd rna-imp-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (equal (rna (rtz x n) m)
                    (rna x m)))
  :hints (("Goal" :use near+-trunc-cor)))

;;;**********************************************************************
;;;                          Odd Rounding
;;;**********************************************************************

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defthm sgn-rto
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rto x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-sticky)))

(defthmd rto-minus
  (equal (rto (* -1 x) n) (* -1 (rto x n)))
  :hints (("Goal" :use sticky-minus)))

(defthmd rto-positive
    (implies (and (< 0 x)
                  (rationalp x) 
		  (integerp n)
                  (> n 0))
	     (> (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-positive)))

(defthmd rto-negative
    (implies (and (< x 0)
                  (rationalp x) 
		  (integerp n)
                  (> n 0))
	     (< (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-negative)))

(defthm rto-0
  (equal (rto 0 n) 0)
  :hints (("Goal" :use sticky-0)))

(defthmd rto-minus
  (equal (rto (* -1 x) n) (* -1 (rto x n)))
  :hints (("Goal" :use sticky-minus)))

(defthm rto-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (rto (* (expt 2 k) x) n)
		(* (expt 2 k) (rto x n))))		
  :rule-classes ()
  :hints (("Goal" :use sticky-shift)))

(defthm expo-rto
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (equal (expo (rto x n))
		    (expo x)))
  :hints (("Goal" :use expo-sticky )))

(defthm rto-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (rto x n) n))
  :hints (("Goal" :use sticky-exactp-a)))

(defthmd rto-exactp-b
    (implies (and (rationalp x)
		  (integerp n) 
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rto x n))))
  :hints (("Goal" :use sticky-exactp-b)))

(defthm rto-exactp-c
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n) 
		  (> n m)
		  (> m 0))
	     (iff (exactp (rto x n) m)
		  (exactp x m)))
  :hints (("Goal" :use sticky-exactp-m)))

(defthmd rto-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rto x n) (rto y n)))
  :rule-classes :linear
  :hints (("Goal" :use sticky-monotone)))

(defthmd rtz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (rtz (rto x n) m)
		    (rtz x m)))
  :hints (("Goal" :use trunc-sticky)))

(defthmd raz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (raz (rto x n) m)
		    (raz x m)))
  :hints (("Goal" :use away-sticky)))

(defthmd rne-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rne (rto x n) m)
		    (rne x m)))
  :hints (("Goal" :use near-sticky)))

(defthmd rna-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rna (rto x n) m)
		    (rna x m)))
  :hints (("Goal" :use near+-sticky)))

(defthm rto-rto
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (equal (rto (rto x n) m)
		    (rto x m)))
  :hints (("Goal" :use sticky-sticky)))

(defthm rto-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (not (= y 0))
		  (not (= (+ x y) 0))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (rto y k))
		(rto (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use sticky-plus)))


;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

(defun rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defthmd rup-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (rup x n) x))
  :rule-classes :linear
  :hints (("Goal" :use inf-lower-bound)))

(defun rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defthmd rdn-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (rdn x n) x))
  :rule-classes :linear
  :hints (("Goal" :use minf-lower-bound)))

(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defthm ieee-mode-is-common-mode
  (implies (IEEE-rounding-mode-p mode)
           (common-mode-p mode))
  :hints (("Goal" :in-theory (enable common-mode-p))))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(local-defthm rnd-rnd
  (equal (fp-rnd x mode n) (rnd x mode n))
  :hints (("Goal" :in-theory (enable fp-rnd rnd))))

(defthm rationalp-rnd
  (rationalp (rnd x mode n))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use rationalp-fp-rnd)))

(defthm rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode))
           (or (= (rnd x mode n) (rtz x n))
	       (= (rnd x mode n) (raz x n))))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-choice)))

(defthmd sgn-rnd
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd x mode n))
		    (sgn x)))
  :hints (("Goal" :use sgn-fp-rnd)))

(defthm rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (> (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use fp-rnd-positive)))

(defthm rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (< (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use fp-rnd-negative)))

(defthm rnd-0
  (equal (rnd 0 mode n)
         0)
  :hints (("Goal" :use fp-rnd-0)))

(defthm rnd-non-pos
    (implies (<= x 0)
	     (<= (rnd x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use fp-rnd-non-pos)))

(defthm rnd-non-neg
    (implies (<= 0 x)
	     (<= 0 (rnd x mode n)))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use fp-rnd-non-neg)))

(defund flip-mode (m)
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(defthm ieee-rounding-mode-p-flip-mode
    (implies (ieee-rounding-mode-p m)
	     (ieee-rounding-mode-p (flip-mode m))))

(defthm common-mode-p-flip-mode
    (implies (common-mode-p m)
	     (common-mode-p (flip-mode m))))

(defthmd rnd-minus
  (equal (rnd (* -1 x) mode n)
         (* -1 (rnd x (flip-mode mode) n)))
  :hints (("Goal" :use fp-rnd-minus)))

(defthm rnd-exactp-a
    (implies (< 0 n)
	     (exactp (rnd x mode n) n))
  :hints (("Goal" :use fp-rnd-exactp-a)))

(defthmd rnd-exactp-b
  (implies (and (rationalp x)
                (common-mode-p mode)
                (integerp n) 
                (> n 0))
           (equal (exactp x n)
                  (equal x (rnd x mode n))))
  :hints (("Goal" :use fp-rnd-exactp-b)))

(defthm rnd-exactp-c
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-exactp-c)))

(defthm rnd-exactp-d
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-exactp-d )))

(defthm rnd<=raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (Common-mode-p mode)
		  (natp n))
	     (<= (rnd x mode n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd<=raz)))

(defthm rnd>=rtz
    (implies (and (rationalp x)
		  (> x 0) ;; 
		  (common-mode-p mode)
                  (integerp n)
                  (> N 0))
	     (>= (rnd x mode n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd>=rtz)))

(defthm rnd<equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n)))
                (< (rtz x (1+ n)) y)
                (< y x))
           (= (rnd y mode n) (rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use (fp-rnd<equal
                        (:instance rna-rna (y x) (x y) (k n) (a (rtz x (1+ n))))))))

(defthm rnd>equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n)))
                (> (raz x (1+ n)) y)
                (> y x))
           (= (rnd y mode n) (rnd x mode n)))
  :rule-classes ()
  :hints (("Goal" :use (fp-rnd>equal
                        (:instance rna-rna (k n) (a (rtz x (1+ n))))))))

(defthm rnd-near-equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp x (1+ n))))
           (let ((d (min (- x (rtz x (1+ n))) (- (raz x (1+ n)) x))))
             (and (> d 0)
                  (implies (< (abs (- x y)) d)
                           (= (rnd y mode n) (rnd x mode n))))))
  :rule-classes ()
  :hints (("Goal" :use (fp-rnd-near-equal
                        (:instance rna-rna (y x) (x y) (k n) (a (rtz x (1+ n))))
                        (:instance rna-rna (k n) (a (rtz x (1+ n))))))))

(defthm rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-diff)))

(defthmd expo-rnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (equal (expo (rnd x mode n))
                    (expo x)))
  :hints (("Goal" :use expo-fp-rnd)))

(defthm rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-mode-p mode)
                  (integerp N)
                  (> N 0))
	     (<= (rnd x mode n) (rnd y mode n)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-monotone)))

(defthm rnd-shift
    (implies (and (rationalp x)
 (integerp n)
		  (common-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-shift)))

(defthm plus-rnd
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y))))
                (common-mode-p mode))
           (= (+ x (rnd y mode k))
              (rnd (+ x y)
                   mode
                   (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use plus-fp-rnd)))

(defthmd rnd-rto
  (implies (and (common-mode-p mode)
                (rationalp x)
                (integerp m) 
		(> m 0)
                (integerp n) 
		(>= n (+ m 2)))
           (equal (rnd (rto x n) mode m)
                  (rnd x mode m)))
  :hints (("Goal" :use fp-rnd-rto)))

(defun rnd-const (e mode n)
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(local-defthm fp-rnd-rnd-const
  (equal (fp-rnd-const e mode n) (rnd-const e mode n)))

(defthmd rnd-const-thm
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (equal (rnd x mode n)
                    (if (and (eql mode 'rne)
                             (exactp x (1+ n))
		             (not (exactp x n)))
		        (rtz (+ x (rnd-const (expo x) mode n)) (1- n))
                      (rtz (+ x (rnd-const (expo x) mode n)) n))))
  :hints (("Goal" :use fp-rnd-const-thm)))

(defund round-up-p (x sticky mode n)
  (case mode
    (rna (= (bitn x (- (expo x) n)) 1))
    (rne (and (= (bitn x (- (expo x) n)) 1)
               (or (not (= (bits x (- (expo x) (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((rup raz) (or (not (= (bits x (- (expo x) n) 0) 0))
                    (= sticky 1)))
    (otherwise ())))

(defthmd round-up-p-thm
  (implies (and (common-mode-p mode)
                (rationalp z)
                (> z 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo z))))
           (let* ((x (rtz z k))
                  (sticky (if (< x z) 1 0)))
	     (equal (rnd z mode n)
                    (if (round-up-p x sticky mode n)
                        (fp+ (rtz z n) n)
                      (rtz z n)))))
  :hints (("Goal" :use ((:instance round-up-p-thm$ (r z))))))
  

;;;**********************************************************************
;;;                         Denormal Rounding 
;;;**********************************************************************

(defund drnd (x mode p q)
  (rnd x mode (+ p (expo x) (- (expo (spn q))))))

(local-defthm denorm-rnd-drnd
  (equal (denorm-rnd x mode p q) (drnd x mode p q))
  :hints (("Goal" :in-theory (enable denorm-rnd drnd))))

(defthmd drnd-minus
  (equal (drnd (* -1 x) mode p q)
         (* -1 (drnd x (flip-mode mode) p q)))
  :hints (("Goal" :use denorm-rnd-minus)))

(defthm drnd-exactp-a
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (or (drepp (drnd x mode p q) p q)
               (= (drnd x mode p q) 0)
               (= (drnd x mode p q) (* (sgn x) (spn q)))))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-exactp-a)))

(defthmd drnd-exactp-b
  (implies (and (rationalp x)
	        (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (equal (drnd x mode p q)
                  x))
  :hints (("Goal" :use denorm-rnd-exactp-b)))

(defthm drnd-exactp-c
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(>= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (>= a (drnd x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-exactp-c)))

(defthm drnd-exactp-d
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(<= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (<= a (drnd x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-exactp-d)))

(defthm drnd-rtz
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (abs (drnd x 'rtz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-rtz)))

(defthm drnd-raz
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (abs (drnd x 'raz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-raz)))

(Defthm drnd-rdn
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (drnd x 'rdn p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-rdn)))

(defthm drnd-rup
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (drnd x 'rup p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-rup)))

(defthm drnd-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (< (abs (- x (drnd x mode p q))) (spd p q)))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-diff)))

(defthm drnd-rne-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (drnd x 'rne p q)))))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-rne-diff)))

(defthm drnd-rna-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (drnd x 'rna p q)))))
  :rule-classes ()
  :hints (("Goal" :use denorm-rnd-rna-diff)))

(defthmd drnd-rto
    (implies (and (common-mode-p mode)
		  (natp p)
		  (> p 1)
		  (natp q)
		  (> q 0)
		  (rationalp x)
                  (<= (abs x) (spn q))
		  (natp n)
		  (>= n (+ p (expo x) (- (expo (spn q))) 2)))
	     (equal (drnd (rto x n) mode p q)
		    (drnd x mode p q)))
  :hints (("Goal" :use denorm-rnd-rto)))

(defthmd drnd-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (common-mode-p mode)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (drnd x mode p q)
                  (- (rnd (+ x (* (sgn x) (spn q))) mode p)
		     (* (sgn x) (spn q)))))
  :hints (("Goal" :use denorm-rnd-rewrite)))

(defthmd drnd-tiny
  (implies (and (common-mode-p mode)
                (natp p)
                (> p 1)
                (natp q)
                (> q 0)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd p q) 2)))
           (equal (drnd x mode p q)
                  (if (member mode '(raz rup))
                      (spd p q)
                     0)))
  :hints (("Goal" :use denorm-rnd-tiny)))

(defthm drnd-tiny-equal
    (implies (and (common-mode-p mode)
                  (natp p)
                  (> p 1)
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd p q) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd p q) 2)))
             (equal (drnd x mode p q)
                    (drnd y mode p q)))
    :rule-classes ()
  :hints (("Goal" :use denorm-rnd-tiny-equal )))
