(in-package "RTL")

(include-book "util")

(local (encapsulate ()

(local (include-book "../rel9-rtl-pkg/lib/top"))

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


(local-defthmd near+-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (near+ x n) a))
  :hints (("Goal" :in-theory (disable acl2::EXPT-IS-INCREASING-FOR-BASE->-1)
                  :use (near-down-2
                        trunc-squeeze
                        away-squeeze
                        near+-choice
                        near+1-a))))

(local-defthmd near+-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (near+ x n) (fp+ a n)))
  :hints (("Goal" :in-theory (disable acl2::EXPT-IS-INCREASING-FOR-BASE->-1)
                  :use (near-up-2
                        trunc-squeeze
                        away-squeeze
                        near+-choice
                        near+1-b))))


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

(defnd expo (x)
  (declare (xargs :measure (:? x)
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))

(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp$ (x n)
  (declare (xargs :guard (and (real/rationalp x) (integerp n))
                  :verify-guards nil))
  (integerp (* (sig x) (expt 2 (1- n)))))

(local-defthm exactp$-rewrite
  (equal (exactp$ x n) (exactp x n))
  :hints (("Goal" :in-theory (enable exactp exactp$))))

(defun fp+$ (x n)
  (declare (xargs :guard (and (real/rationalp x) (integerp n))
                  :verify-guards nil))
  (+ x (expt 2 (- (1+ (expo x)) n))))

(local-defthm fp+$-rewrite
  (equal (fp+$ x n) (fp+ x n)))


;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

(defund rtz$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm rtz$-trunc
  (equal (rtz$ x n) (trunc x n))
  :hints (("Goal" :in-theory (enable rtz$ trunc))))

(defthmd rtz$-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (rtz$ x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (trunc-rewrite))))

(defthmd rtz$-minus
  (equal (rtz$ (- x) n) (- (rtz$ x n)))
  :hints (("Goal" :use trunc-minus)))

(defthmd abs-rtz$
  (equal (abs (rtz$ x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("Goal" :use (abs-trunc))))

(defthm rtz$-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (rtz$ x n)))
  :rule-classes :type-prescription)

(defthmd sgn-rtz$
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (sgn (rtz$ x n))
		    (sgn x)))
  :hints (("Goal" :use (sgn-trunc))))

(defthm rtz$-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n)))
            (< 0 (rtz$ x n)))
   :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-positive))))

(defthm rtz$-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (rtz$ x n) 0))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (trunc-negative))))

(defthm rtz$-neg-bits
    (implies (and (integerp n)
		  (<= n 0))
	     (equal (rtz$ x n) 0))
  :hints (("Goal" :use (trunc-to-0))))

(defthm rtz$-0
  (equal (rtz$ 0 n) 0)
  :hints (("Goal" :use (trunc-0))))

(defthmd rtz$-shift
  (implies (integerp n)
           (equal (rtz$ (* x (expt 2 k)) n)
                  (* (rtz$ x n) (expt 2 k))))
  :hints (("Goal" :use (trunc-shift))))

(defthm expo-rtz$
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (rtz$ x n))
                    (expo x)))
  :hints (("Goal" :use (expo-trunc))))

(defthmd rtz$-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (rtz$ x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-bound))))

(defthmd rtz$-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (rtz$ x n) x))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-upper-pos))))

(defthmd rtz$-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (rtz$ x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-lower-bound))))

(defthm rtz$-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (abs (- x (rtz$ x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-diff))))

(defthmd rtz$-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (< x (fp+$ a n)))
           (equal (rtz$ x n) a))
  :hints (("Goal" :use (trunc-squeeze))))

(defthm rtz$-exactp$-a
  (exactp$ (rtz$ x n) n)
  :hints (("Goal" :use (trunc-exactp-a))))

(defthmd rtz$-exactp$-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp$ x n)
                  (= x (rtz$ x n))))
  :hints (("Goal" :use (trunc-exactp-b))))

(defthm rtz$-exactp$-c
    (implies (and (exactp$ a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (rtz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use (trunc-exactp-c))))

(defthmd rtz$-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (rtz$ x n) (rtz$ y n)))
  :rule-classes :linear
  :hints (("Goal" :use (trunc-monotone))))

(defthmd rtz$-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp$ x (1+ n))
		  (not (exactp$ x n)))
	     (equal (rtz$ x n)
                    (- x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use (trunc-midpoint))))

(defthm rtz$-rtz$
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (rtz$ (rtz$ x n) m)
		    (rtz$ x m)))
  :hints (("Goal" :use (trunc-trunc))))

(defthm plus-rtz$
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp$ x (+ k (- (expo x) (expo y)))))
	     (= (+ x (rtz$ y k))
		(rtz$ (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use (plus-trunc))))

(defthm minus-rtz$
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (exactp$ x (+ k (- (expo x) (expo y)))))
	     (= (- x (rtz$ y k))
                (- (rtz$ (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance minus-trunc-1 (n (+ k (- (expo x) (expo y)))))))))

(defthmd bits-rtz$
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (equal (rtz$ x k)
                  (* (expt 2 (- n k))
                     (bits x (1- n) (- n k)))))
  :hints (("Goal" :use (bits-trunc))))

(defthmd bits-rtz$-bits
  (implies (and (rationalp x)
                (>= x 0)
                (integerp k)
                (integerp i)
                (integerp j)
                (> k 0)
                (>= (expo x) i)
                (>= j (- (1+ (expo x)) k)))
           (equal (bits (rtz$ x k) i j)
                  (bits x i j)))
  :hints (("Goal" :use (bits-trunc-bits))))

(defthmd rtz$-split
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp m)
                (> m k)
                (integerp k)
                (> k 0))
           (equal (rtz$ x m)
                  (+ (rtz$ x k)
                     (* (expt 2 (- n m))
                        (bits x (1- (- n k)) (- n m))))))
  :hints (("Goal" :use (trunc-split))))

(defthmd rtz$-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (equal (rtz$ x k)
                  (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :hints (("Goal" :use (trunc-logand))))


;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************

(defund raz$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm raz$-away
  (equal (raz$ x n) (away x n))
  :hints (("Goal" :in-theory (enable raz$ away))))

(defthmd raz$-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (raz$ x n)
		    (* (sgn x)
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (away-rewrite))))

(defthmd raz$-minus
  (equal (raz$ (- x) n) (- (raz$ x n)))
  :hints (("Goal" :use away-minus)))

(defthmd abs-raz$
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (raz$ x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use abs-away)))


(defthm raz$-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (raz$ x n)))
  :rule-classes :type-prescription)

(defthmd sgn-raz$
  (equal (sgn (raz$ x n))
         (sgn x))
  :hints (("Goal" :use sgn-away)))

(defthm raz$-positive
  (implies (and (< 0 x)
                (case-split (rationalp x)))
           (< 0 (raz$ x n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-positive)))

(defthm raz$-negative
    (implies (and (< x 0)
                  (case-split (rationalp x)))
	     (< (raz$ x n) 0))
    :rule-classes (:rewrite :linear)
  :hints (("Goal" :use away-negative)))

(defthm raz$-neg-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n))
           (equal (raz$ x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
  :hints (("Goal" :use away-to-0)))

(defthm raz$-0
  (equal (raz$ 0 n) 0)
  :hints (("Goal" :use away-0)))

(defthm raz$-shift
    (implies (integerp n)
	     (= (raz$ (* x (expt 2 k)) n)
		(* (raz$ x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use away-shift)))

(defthmd raz$-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (raz$ x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-bound)))

(defthmd raz$-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (raz$ x n) x))
  :rule-classes :linear
  :hints (("Goal" :use away-lower-pos)))

(defthmd raz$-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (raz$ x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use away-upper-bound)))

(defthmd raz$-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (raz$ x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use away-diff)))

(defthm raz$-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (raz$ x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use away-expo-upper)))

(defthmd expo-raz$-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (raz$ x n)) (expo x)))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-lower-bound)))

(defthmd expo-raz$
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (raz$ x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (raz$ x n))
                    (expo x)))
  :hints (("Goal" :use expo-away)))

(defthmd expo-raz$-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (raz$ x n)) (1+ (expo x))))
  :rule-classes :linear
  :hints (("Goal" :use expo-away-upper-bound)))

(defthmd raz$-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (<= x (fp+$ a n)))
           (equal (raz$ x n) (fp+$ a n)))
  :hints (("Goal" :use (away-squeeze))))

(defthm raz$-exactp$-a
    (implies (case-split (< 0 n))
	     (exactp$ (raz$ x n) n))
  :hints (("Goal" :use away-exactp-a)))

(defthmd raz$-exactp$-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp$ x n)
                  (= x (raz$ x n))))
  :hints (("Goal" :use away-exactp-b)))

(defthm raz$-exactp$-c
    (implies (and (exactp$ a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use away-exactp-c)))

(defthmd raz$-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (raz$ x n) (raz$ y n)))
  :rule-classes :linear
  :hints (("Goal" :use away-monotone)))

(defthmd rtz$-raz$
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp$ x n)))
	     (equal (raz$ x n)
	            (+ (rtz$ x n)
		       (expt 2 (+ (expo x) 1 (- n))))))
  :hints (("Goal" :use trunc-away)))

(defthmd raz$-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp$ x (1+ n))
		  (not (exactp$ x n)))
	     (equal (raz$ x n)
		    (+ x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use away-midpoint)))

(defthmd raz$-raz$
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (raz$ (raz$ x n) m)
		    (raz$ x m)))
  :hints (("Goal" :use away-away)))

(defthm plus-raz$
  (implies (and (exactp$ x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (raz$ y k))
              (raz$ (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use plus-away)))

(defthm minus-rtz$-raz$
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (exactp$ x (+ k (- (expo x) (expo y)))))
           (= (- x (rtz$ y k))
              (raz$ (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use (:instance minus-trunc-2 (n (+ k (- (expo x) (expo y))))))))

(defthm rtz$-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (- (expo y))))
                  (exactp$ x k1)
                  (> k2 0))
             (= (+ x (rtz$ y k))
                (if (= (sgn (+ x y)) (sgn y))
                    (rtz$ (+ x y) k2)
                  (raz$ (+ x y) k2))))
  :rule-classes ()
  :hints (("Goal" :use trunc-plus-minus)))

(defthmd raz$-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp$ x m))
	     (equal (raz$ x n)
		    (rtz$ (+ x
		    	    (expt 2 (- (1+ (expo x)) n))
			    (- (expt 2 (- (1+ (expo x)) m))))
		         n)))
  :hints (("Goal" :use away-imp)))

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defun re$ (x)
  (declare (xargs :guard (real/rationalp x)))
  (- x (fl x)))

(local-defthm re$-rewrite
  (equal (re$ x) (re x)))

(defund rne$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re$ (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz$ x n)
      (if (> f 1/2)
	  (raz$ x n)
	(if (evenp z)
	    (rtz$ x n)
	  (raz$ x n))))))

(local-defthm rne$-near
  (equal (rne$ x n) (near x n))
  :hints (("Goal" :in-theory (enable near rne$))))

(defthm rne$-choice
    (or (= (rne$ x n) (rtz$ x n))
	(= (rne$ x n) (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near-choice)))

(defthmd rne$-minus
  (equal (rne$ (- x) n) (- (rne$ x n)))
  :hints (("Goal" :use near-minus)))

(defthmd sgn-rne$
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rne$ x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near)))

(defthm rne$-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (rne$ x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-positive)))

(defthmd rne$-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n))
           (< (rne$ x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use near-negative)))

(defthm rne$-0
  (equal (rne$ 0 n) 0)
  :hints (("Goal" :use near-0)))

(defthm expo-rne$
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (rne$ x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rne$ x n))
                    (expo x)))
  :hints (("Goal" :use expo-near)))

(defthm rne$<=raz$
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rne$ x n) (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near<=away)))

(defthm rne$>=rtz$
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rne$ x n) (rtz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near>=trunc)))

(defthm rne$-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (rne$ (* x (expt 2 k)) n)
		(* (rne$ x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near-shift)))

(defthm rne$-exactp$-a
    (implies (< 0 n)
	     (exactp$ (rne$ x n) n))
  :hints (("Goal" :use near-exactp-a)))

(defthmd rne$-exactp$-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp$ x n)
                  (= x (rne$ x n))))
  :hints (("Goal" :use near-exactp-b)))

(defthm rne$-exactp$-c
    (implies (and (exactp$ a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (rne$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-c)))

(defthm rne$-exactp$-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp$ a n)
		  (<= a x))
	     (<= a (rne$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near-exactp-d)))

(defthmd rne$-rtz$
    (implies (and (< (abs (- x (rtz$ x n)))
                     (abs (- (raz$ x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (rne$ x n)
                    (rtz$ x n)))
  :hints (("Goal" :use near1-a)))

(defthmd rne$-raz$
  (implies (and (> (abs (- x (rtz$ x n)))
                   (abs (- (raz$ x n) x)))
                (rationalp x)
                (integerp n))
           (equal (rne$ x n)
                  (raz$ x n)))
  :hints (("Goal" :use near1-b)))

(defthmd rne$-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne$ x n) a))
  :hints (("Goal" :use (near-down))))

(defthmd rne$-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (< x (fp+$ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne$ x n) (fp+$ a n)))
  :hints (("Goal" :use (near-up))))

(local-defthm rne$-up-2-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (<= m n)
                (< x (expt 2 k))
                (= (rne$ x n) (expt 2 k)))
           (> x (fp- (expt 2 k) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-fp- (x (expt 2 k)))
                        (:instance rne$-exactp$-c (a (fp- (expt 2 k) n)))))))

(local-defthm rne$-up-2-2
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (<= 1 (expt 2 (1- (- n m)))))
  :rule-classes ())

(local-defthm rne$-up-2-3
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (<= (1+ (expt 2 (1- (- n m))))
               (+ (expt 2 (1- (- n m))) (expt 2 (1- (- n m))))))
  :rule-classes ()
  :hints (("Goal" :use (rne$-up-2-2))))

(local-defthm rne$-up-2-4
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (<= (1+ (expt 2 (1- (- n m))))
               (expt 2 (- n m))))
  :rule-classes ()
  :hints (("Goal" :use (rne$-up-2-3))))

(defthm rne$-up-2-5-a
  (implies (and (integerp a) (integerp b) (<= a b))
           (<= (+ (expt 2 a) (expt 2 b)) (expt 2 (1+ b))))
  :rule-classes())

(local-defthm rne$-up-2-5-b
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (<= (+ (EXPT 2 (- N)) (EXPT 2 (+ -1 (- M))))
               (EXPT 2 (- M))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rne$-up-2-5-a (a (- n)) (b (- -1 m)))))))

(local-defthm rne$-up-2-5
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (>= (fp- (expt 2 k) n) (+ (fp- (expt 2 k) m) (expt 2 (- (1- k) m)))))
  :rule-classes ()
  :hints (("Goal" :use (rne$-up-2-4))
          ("Goal'''" :use (rne$-up-2-5-b)
                     :in-theory (disable ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(local-defthm rne$-up-2-6
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (rne$ x n) (expt 2 k)))
           (> x (+ (fp- (expt 2 k) m) (expt 2 (- (1- k) m)))))
  :rule-classes ()
  :hints (("Goal" :use (rne$-up-2-1 rne$-up-2-5)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rne$-up-2-7
  (implies (and (integerp k)
                (not (zp m)))
           (<= (expo (fp- (expt 2 k) m)) (1- k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo<= (x (fp- (expt 2 k) m)) (n (1- k)))))))

(local-defthm rne$-up-2-8
  (implies (and (integerp k)
                (not (zp m)))
           (>= (expo (fp- (expt 2 k) m)) (1- k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo>= (x (fp- (expt 2 k) m)) (n (1- k)))))))

(local-defthmd rne$-up-2-9
  (implies (and (integerp k)
                (not (zp m)))
           (equal (expo (fp- (expt 2 k) m)) (1- k)))
  :hints (("Goal" :use (rne$-up-2-8 rne$-up-2-7))))

(local-defthm rne$-up-2-10
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (rne$ x n) (expt 2 k)))
           (equal (rne$ x m) (expt 2 k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (rne$-up-2-9 exactp-2**n) (fp-))
                  :use (rne$-up-2-6 rne$-up-2-8
                        (:instance rne$-up (a (fp- (expt 2 k) m)) (n m))))))

(defthmd rne$-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rne$ x n)) (expt 2 k)))
           (equal (abs (rne$ x m)) (expt 2 k)))
  :hints (("Goal" :in-theory (enable sgn rne$-minus)
                  :use (sgn-rne$ rne$-up-2-10 (:instance rne$-up-2-10 (x (- x)))))))

(local-defthm raz$-up-2-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (raz$ x n) (expt 2 k)))
           (> x (fp- (expt 2 k) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-fp- (x (expt 2 k)))
                        (:instance raz$-exactp$-c (a (fp- (expt 2 k) n)))))))

(local-defthm raz$-up-2-2
  (implies (and (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n))
           (>= (fp- (expt 2 k) n) (fp- (expt 2 k) m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rne$-up-2-6 (x 0)))
                  :in-theory (disable ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(local-defthm raz$-up-2-3
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (raz$ x n) (expt 2 k)))
           (> x (fp- (expt 2 k) m)))
  :rule-classes ()
  :hints (("Goal" :use (raz$-up-2-1 raz$-up-2-2)
                  :in-theory (disable fp-))))

(local-defthm raz$-up-2-4
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (raz$ x n) (expt 2 k)))
           (= (raz$ x m) (expt 2 k)))
  :rule-classes ()
  :hints (("Goal" :use (raz$-up-2-3
                        (:instance raz$-squeeze (a (fp- (expt 2 k) m)) (n m)))
                  :in-theory (e/d (exactp-2**n) (fp-)))))

(defthmd raz$-up
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (raz$ x n)) (expt 2 k)))
           (equal (abs (raz$ x m)) (expt 2 k)))
  :hints (("Goal" :in-theory (enable sgn raz$-minus)
                  :use (sgn-rne$ raz$-up-2-4 (:instance raz$-up-2-4 (x (- x)))))))

(defthm rne$-nearest
    (implies (and (exactp$ y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rne$ x n)))))
  :rule-classes ()
  :hints (("Goal" :use near2)))

(defthm rne$-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne$ x n)))
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
	     (<= (abs (- x (rne$ x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (rne$-diff ne-11)
                  :in-theory (theory 'minimal-theory))))

(defthm rne$-diff-cor
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne$ x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use (ne-12))))

(defthm rne$-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (<= (rne$ x n) (rne$ y n)))
  :rule-classes ()
  :hints (("Goal" :use near-monotone)))

(defund rne$-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rne$ x n) (rne$ y n)) 2)
    (expt 2 (expo y))))

(defthm rne$-rne$-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (rne$ x n) (rne$ y n))))
	     (and (<= x (rne$-witness x y n))
		  (<= (rne$-witness x y n) y)
		  (exactp$ (rne$-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rne$-witness near-witness)
                  :use near-near-lemma)))

(defthm rne$-rne$
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
		  (< y (fp+$ a (1+ n)))
		  (exactp$ a (1+ n)))
	     (<= (rne$ y k) (rne$ x k)))
  :rule-classes ()
  :hints (("Goal" :use near-near)))

(defthm rne$-boundary
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (< 0 x)
		  (< x a)
		  (< a y)
		  (integerp n)
		  (> n 0)
		  (exactp$ a (1+ n))
		  (not (exactp$ a n)))
	     (< (rne$ x n) (rne$ y n)))
  :rule-classes ()
  :hints (("Goal" :use near-boundary)))

(defthm rne$-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 1)
		  (exactp$ x (1+ n))
		  (not (exactp$ x n)))
	     (exactp$ (rne$ x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use near-exact)))

(defthm plus-rne$
  (implies (and (exactp$ x (1- (+ k (- (expo x) (expo y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rne$ y k))
              (rne$ (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near-plus)))

(defthmd rne$-imp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (equal (rne$ x n)
   		    (if (and (exactp$ x (1+ n)) (not (exactp$ x n)))
		        (rtz$ (+ x (expt 2 (- (expo x) n))) (1- n))
		      (rtz$ (+ x (expt 2 (- (expo x) n))) n))))
  :hints (("Goal" :use near-trunc)))

(defund rna$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (< (re$ (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz$ x n)
    (raz$ x n)))

(local-defthm rna$-near+
  (equal (rna$ x n) (near+ x n))
  :hints (("Goal" :in-theory (enable near+ rna$))))

(defthm rna$-choice
    (or (= (rna$ x n) (rtz$ x n))
	(= (rna$ x n) (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-choice)))

(defthmd rna$-minus
  (equal (rna$ (- x) n) (- (rna$ x n)))
  :hints (("Goal" :use near+-minus)))

(defthm rna$<=raz$
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rna$ x n) (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near+<=away)))

(defthm rna$>=rtz$
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rna$ x n) (rtz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near+>=trunc)))

(defthm rna$-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (rna$ (* x (expt 2 k)) n)
		(* (rna$ x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use near+-shift)))

(defthm rna$-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (rna$ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-positive)))

(defthm rna$-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (rna$ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use near+-negative)))

(defthm rna$-0
  (equal (rna$ 0 n) 0)
  :hints (("Goal" :use near+-0)))

(defthm sgn-rna$
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rna$ x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-near+)))

(defthm rna$-exactp$-a
    (implies (> n 0)
	     (exactp$ (rna$ x n) n))
  :hints (("Goal" :use (rna$-choice rtz$-exactp$-a raz$-exactp$-a))))

(defthmd rna$-exactp$-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp$ x n)
                  (= x (rna$ x n))))
  :hints (("Goal" :use near+-exactp-b)))

(defthm rna$-exactp$-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp$ a n)
		  (>= a x))
	     (>= a (rna$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-c)))

(defthm rna$-exactp$-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp$ a n)
		  (<= a x))
	     (<= a (rna$ x n)))
  :rule-classes ()
  :hints (("Goal" :use near+-exactp-d)))

(defthmd expo-rna$
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (rna$ x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rna$ x n))
                    (expo x)))
  :hints (("Goal" :use expo-near+)))

(defthmd rna$-rtz$
    (implies (and (rationalp x)
		  (integerp n)
		  (< (abs (- x (rtz$ x n)))
                     (abs (- (raz$ x n) x))))
	     (equal (rna$ x n) (rtz$ x n)))
  :hints (("Goal" :use near+1-a)))

(defthmd rna$-raz$
    (implies (and (rationalp x)
		  (integerp n)
		  (> (abs (- x (rtz$ x n)))
                     (abs (- (raz$ x n) x))))
	     (equal (rna$ x n) (raz$ x n)))
  :hints (("Goal" :use near+1-b)))

(defthmd rna$-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna$ x n) a))
  :hints (("Goal" :use (near+-down))))

(defthmd rna$-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp$ a n)
                (< x (fp+$ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna$ x n) (fp+$ a n)))
  :hints (("Goal" :use (near+-up))))

(local-defthm rna$-up-2-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (<= m n)
                (< x (expt 2 k))
                (= (rna$ x n) (expt 2 k)))
           (> x (fp- (expt 2 k) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-fp- (x (expt 2 k)))
                        (:instance rna$-exactp$-c (a (fp- (expt 2 k) n)))))))

(local-defthm rna$-up-2-6
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (rna$ x n) (expt 2 k)))
           (> x (+ (fp- (expt 2 k) m) (expt 2 (- (1- k) m)))))
  :rule-classes ()
  :hints (("Goal" :use (rna$-up-2-1 rne$-up-2-5)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rna$-up-2-10
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< x (expt 2 k))
                (= (rna$ x n) (expt 2 k)))
           (equal (rna$ x m) (expt 2 k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (rne$-up-2-9 exactp-2**n) (fp-))
                  :use (rna$-up-2-6 rne$-up-2-8
                        (:instance rna$-up (a (fp- (expt 2 k) m)) (n m))))))

(defthmd rna$-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rna$ x n)) (expt 2 k)))
           (equal (abs (rna$ x m)) (expt 2 k)))
  :hints (("Goal" :in-theory (enable sgn rna$-minus)
                  :use (sgn-rne$ rna$-up-2-10 (:instance rna$-up-2-10 (x (- x)))))))

(defthm rna$-nearest
    (implies (and (exactp$ y n)
                  (rationalp x)
                  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rna$ x n)))))
  :rule-classes ()
  :hints (("Goal" :use near+2)))

(defthm rna$-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rna$ x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use near+-est)))

(defthm rna$-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rna$ x n) (rna$ y n)))
  :rule-classes ()
  :hints (("Goal" :use near+-monotone)))

(defthmd rna$-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp$ x (1+ n))
		  (not (exactp$ x n)))
	     (equal (rna$ x n) (raz$ x n)))
  :hints (("Goal" :use near+-midpoint)))

(defthm rne$-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rne$ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near-power-a)))

(defthm rtz$-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rtz$ (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near-power-b)))

(defthm rna$-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rna$ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use near+-power)))

(defthm plus-rna$
  (implies (and (exactp$ x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (rna$ y k))
              (rna$ (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use near+-plus)))

(defthmd rna$-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (equal (rna$ x n)
		    (rtz$ (+ x (expt 2 (- (expo x) n))) n)))
  :hints (("Goal" :use near+trunc)))

(defthmd rna$-imp-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (equal (rna$ (rtz$ x n) m)
                    (rna$ x m)))
  :hints (("Goal" :use near+-trunc-cor)))

;;;**********************************************************************
;;;                          Odd Rounding
;;;**********************************************************************

(defund rto$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (exactp$ x (1- n))
      x
    (+ (rtz$ x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(local-defthm rto$-sticky
  (equal (rto$ x n) (sticky x n))
  :hints (("Goal" :in-theory (enable rto$ sticky))))

(defthm sgn-rto$
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rto$ x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-sticky)))

(defthmd rto$-minus
  (equal (rto$ (- x) n) (- (rto$ x n)))
  :hints (("Goal" :use sticky-minus)))

(defthmd rto$-positive
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (rto$ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-positive)))

(defthmd rto$-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (rto$ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use sticky-negative)))

(defthm rto$-0
  (equal (rto$ 0 n) 0)
  :hints (("Goal" :use sticky-0)))

(defthmd rto$-minus
  (equal (rto$ (- x) n) (- (rto$ x n)))
  :hints (("Goal" :use sticky-minus)))

(defthm rto$-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (rto$ (* (expt 2 k) x) n)
		(* (expt 2 k) (rto$ x n))))
  :rule-classes ()
  :hints (("Goal" :use sticky-shift)))

(defthm expo-rto$
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (equal (expo (rto$ x n))
		    (expo x)))
  :hints (("Goal" :use expo-sticky )))

(defthm rto$-exactp$-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp$ (rto$ x n) n))
  :hints (("Goal" :use sticky-exactp-a)))

(defthmd rto$-exactp$-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp$ x n)
                  (= x (rto$ x n))))
  :hints (("Goal" :use sticky-exactp-b)))

(defthm rto$-exactp$-c
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp$ (rto$ x n) m)
		  (exactp$ x m)))
  :hints (("Goal" :use sticky-exactp-m)))

(defthmd rto$-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rto$ x n) (rto$ y n)))
  :rule-classes :linear
  :hints (("Goal" :use sticky-monotone)))

(defthmd rtz$-rto$
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (rtz$ (rto$ x n) m)
		    (rtz$ x m)))
  :hints (("Goal" :use trunc-sticky)))

(defthmd raz$-rto$
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (raz$ (rto$ x n) m)
		    (raz$ x m)))
  :hints (("Goal" :use away-sticky)))

(defthmd rne$-rto$
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rne$ (rto$ x n) m)
		    (rne$ x m)))
  :hints (("Goal" :use near-sticky)))

(defthmd rna$-rto$
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rna$ (rto$ x n) m)
		    (rna$ x m)))
  :hints (("Goal" :use near+-sticky)))

(defthm rto$-rto$
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (equal (rto$ (rto$ x n) m)
		    (rto$ x m)))
  :hints (("Goal" :use sticky-sticky)))

(defthm rto$-plus
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
		  (exactp$ x (1- k1)))
	     (= (+ x (rto$ y k))
		(rto$ (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use sticky-plus)))


;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

(defun rup$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (raz$ x n)
    (rtz$ x n)))

(local-defthm rup$-inf
  (equal (rup$ x n) (inf x n))
  :hints (("Goal" :in-theory (enable rup$ inf))))

(defthmd rup$-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (rup$ x n) x))
  :rule-classes :linear
  :hints (("Goal" :use inf-lower-bound)))

(defun rdn$ (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (rtz$ x n)
    (raz$ x n)))

(local-defthm rdn$-minf
  (equal (rdn$ x n) (minf x n))
  :hints (("Goal" :in-theory (enable rdn$ minf))))

(defthmd rdn$-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (rdn$ x n) x))
  :rule-classes :linear
  :hints (("Goal" :use minf-lower-bound)))

(defnd IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defnd common-mode-p (mode)
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

(defund rnd$ (x mode n)
  (case mode
    (raz (raz$ x n))
    (rna (rna$ x n))
    (rtz (rtz$ x n))
    (rup (rup$ x n))
    (rdn (rdn$ x n))
    (rne (rne$ x n))
    (otherwise 0)))

(local-defthm rnd$-rnd
  (equal (rnd$ x mode n) (rnd x (old-mode mode) n))
  :hints (("Goal" :in-theory (enable IEEE-rounding-mode-p common-mode-p rnd$ old-mode rnd))))

(defthm rationalp-rnd$
  (rationalp (rnd$ x mode n))
  :rule-classes (:type-prescription))

(defthm rnd$-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode))
           (or (= (rnd$ x mode n) (rtz$ x n))
	       (= (rnd$ x mode n) (raz$ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-choice (mode (old-mode mode)))))))

(defthmd sgn-rnd$
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd$ x mode n))
		    (sgn x)))
  :hints (("Goal" :use ((:instance sgn-rnd (mode (old-mode mode)))))))

(defthm rnd$-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (> (rnd$ x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance rnd-positive (mode (old-mode mode)))))))

(defthm rnd$-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (< (rnd$ x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance rnd-negative (mode (old-mode mode)))))))

(defthm rnd$-0
  (equal (rnd$ 0 mode n)
         0)
  :hints (("Goal" :use ((:instance rnd-0 (mode (old-mode mode)))))))

(defthm rnd$-non-pos
    (implies (<= x 0)
	     (<= (rnd$ x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use ((:instance rnd-non-pos (mode (old-mode mode)))))))

(defthm rnd$-non-neg
    (implies (<= 0 x)
	     (<= 0 (rnd$ x mode n)))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use ((:instance rnd-non-neg (mode (old-mode mode)))))))

(defund flip-mode (m)
  (declare (xargs :guard (common-mode-p m)))
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

(defthmd rnd$-minus
  (equal (rnd$ (- x) mode n)
         (- (rnd$ x (flip-mode mode) n)))
  :hints (("Goal" :use ((:instance rnd-minus (mode (old-mode mode)))))))

(defthm rnd$-exactp$-a
    (implies (< 0 n)
	     (exactp$ (rnd$ x mode n) n))
  :hints (("Goal" :use ((:instance rnd-exactp-a (mode (old-mode mode)))))))

(defthmd rnd$-exactp$-b
  (implies (and (rationalp x)
                (common-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (exactp$ x n)
                  (equal x (rnd$ x mode n))))
  :hints (("Goal" :use ((:instance rnd-exactp-b (mode (old-mode mode)))))))

(defthm rnd$-exactp$-c
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp$ a n)
		  (>= a x))
	     (>= a (rnd$ x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-exactp-c (mode (old-mode mode)))))))

(defthm rnd$-exactp$-d
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp$ a n)
		  (<= a x))
	     (<= a (rnd$ x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-exactp-d (mode (old-mode mode)))))))

(defthm rnd$<=raz$
    (implies (and (rationalp x)
		  (>= x 0)
		  (common-mode-p mode)
		  (natp n))
	     (<= (rnd$ x mode n) (raz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd<=away (mode (old-mode mode)))))))

(defthm rnd$>=rtz$
    (implies (and (rationalp x)
		  (> x 0) ;;
		  (common-mode-p mode)
                  (integerp n)
                  (> N 0))
	     (>= (rnd$ x mode n) (rtz$ x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd>=trunc (mode (old-mode mode)))))))

(local (include-book "rnd-near-equal"))

(defthm rnd$<equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp$ x (1+ n)))
                (< (rtz$ x (1+ n)) y)
                (< y x)
                ;; (:instance near+-near+ (y x) (x y) (k n) (a (rtz$ x (1+ n))))
                (implies (and (rationalp (rtz$ x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz$ x (1+ n)))
		              (< (rtz$ x (1+ n)) y)
		              (< x (fp+$ (rtz$ x (1+ n)) (1+ n)))
		              (exactp$ (rtz$ x (1+ n)) (1+ n)))
	                 (<= (rna$ x n) (rna$ y n))))
           (= (rnd$ y mode n) (rnd$ x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd<equal (mode (old-mode mode)))))))

(defthm rnd$>equal
  (implies (and (rationalp x)
                (rationalp y)
                (common-mode-p mode)
                (natp n)
                (> n 0)
                (> x 0)
                (not (exactp$ x (1+ n)))
                (< y (raz$ x (1+ n)))
                (< x y)
                ;; (:instance near+-near+ (k n) (a (rtz$ x (1+ n))))
                (implies (and (rationalp (rtz$ x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz$ x (1+ n)))
		              (< (rtz$ x (1+ n)) x)
		              (< y (fp+$ (rtz$ x (1+ n)) (1+ n)))
		              (exactp$ (rtz$ x (1+ n)) (1+ n)))
	                 (<= (rna$ y n) (rna$ x n))))
           (= (rnd$ y mode n) (rnd$ x mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd>equal (mode (old-mode mode)))))))

(defthm rnd$-near-equal
  (implies (and (rationalp x)
                (rationalp y)
                (natp n)
                (common-mode-p mode)
                (> n 0)
                (> x 0)
                (not (exactp$ x (1+ n)))
                ;; (:instance near+-near+ (y x) (x y) (k n) (a (rtz$ x (1+ n))))
                (implies (and (rationalp (rtz$ x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz$ x (1+ n)))
		              (< (rtz$ x (1+ n)) y)
		              (< x (fp+$ (rtz$ x (1+ n)) (1+ n)))
		              (exactp$ (rtz$ x (1+ n)) (1+ n)))
	                 (<= (rna$ x n) (rna$ y n)))
                ;; (:instance near+-near+ (k n) (a (rtz$ x (1+ n))))
                (implies (and (rationalp (rtz$ x (1+ n)))
                              (< 0 y)
		              (< 0 (rtz$ x (1+ n)))
		              (< (rtz$ x (1+ n)) x)
		              (< y (fp+$ (rtz$ x (1+ n)) (1+ n)))
		              (exactp$ (rtz$ x (1+ n)) (1+ n)))
	                 (<= (rna$ y n) (rna$ x n))))
           (let ((d (min (- x (rtz$ x (1+ n))) (- (raz$ x (1+ n)) x))))
             (and (> d 0)
                  (implies (< (abs (- x y)) d)
                           (= (rnd$ y mode n) (rnd$ x mode n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-near-equal (mode (old-mode mode)))))))

(defthm rnd$-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (< (abs (- x (rnd$ x mode n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-diff (mode (old-mode mode)))))))

(defthmd expo-rnd$
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode)
		  (not (= (abs (rnd$ x mode n))
			  (expt 2 (1+ (expo x))))))
	     (equal (expo (rnd$ x mode n))
                    (expo x)))
  :hints (("Goal" :use ((:instance expo-rnd (mode (old-mode mode)))))))

(defthm rnd$-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-mode-p mode)
                  (integerp N)
                  (> N 0))
	     (<= (rnd$ x mode n) (rnd$ y mode n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-monotone (mode (old-mode mode)))))))

(defthm rnd$-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (common-mode-p mode)
		  (integerp k))
	     (= (rnd$ (* x (expt 2 k)) mode n)
		(* (rnd$ x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-shift (mode (old-mode mode)))))))

(defthm plus-rnd$
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp$ x (+ -1 k (- (expo x) (expo y))))
                (common-mode-p mode))
           (= (+ x (rnd$ y mode k))
              (rnd$ (+ x y)
                   mode
                   (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance plus-rnd (mode (old-mode mode)))))))

(defthmd rnd$-rto$
  (implies (and (common-mode-p mode)
                (rationalp x)
                (integerp m)
		(> m 0)
                (integerp n)
		(>= n (+ m 2)))
           (equal (rnd$ (rto$ x n) mode m)
                  (rnd$ x mode m)))
  :hints (("Goal" :use ((:instance rnd-sticky (mode (old-mode mode)))))))

(defun rnd$-const (e mode n)
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defthmd rnd$-const-thm
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (equal (rnd$ x mode n)
                    (if (and (eql mode 'rne)
                             (exactp$ x (1+ n))
		             (not (exactp$ x n)))
		        (rtz$ (+ x (rnd$-const (expo x) mode n)) (1- n))
                      (rtz$ (+ x (rnd$-const (expo x) mode n)) n))))
  :hints (("Goal" :in-theory (enable ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p rnd-const rnd$-const)
                  :use ((:instance rnd-const-thm (mode (old-mode mode)))))))


;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************

(defund bias$ (q) (- (expt 2 (- q 1)) 1) )

(defund spn$ (q)
  (expt 2 (- 1 (bias$ q))))

(defund spd$ (p q)
     (expt 2 (+ 2 (- (bias$ q)) (- p))))

(defund drepp$ (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias$ q)))
       (<= (+ (expo x) (bias$ q)) 0)
       (exactp$ x (+ -2 p (expt 2 (- q 1)) (expo x)))))

(local-defthm bias$-rewrite
  (equal (bias$ q) (bias q))
  :hints (("Goal" :in-theory (enable bias bias$))))

(local-defthm spn$-rewrite
  (equal (spn$ q) (spn q))
  :hints (("Goal" :in-theory (enable spn spn$))))

(local-defthm spd$-rewrite
  (equal (spd$ p q) (spd p q))
  :hints (("Goal" :in-theory (enable spd spd$))))

(local-defthm drepp$-rewrite
  (equal (drepp$ x p q) (drepp x p q))
  :hints (("Goal" :in-theory (enable drepp drepp$))))

(defund drnd$ (x mode p q)
  (rnd$ x mode (+ p (expo x) (- (expo (spn$ q))))))

(local-defthm drnd$-drnd
  (equal (drnd$ x mode p q)
         (drnd x (old-mode mode) p q))
  :hints (("Goal" :in-theory (enable drnd$ drnd))))

(defthmd drnd$-minus
  (equal (drnd$ (- x) mode p q)
         (- (drnd$ x (flip-mode mode) p q)))
  :hints (("Goal" :use ((:instance drnd-minus (mode (old-mode mode)))))))

(defthm drnd$-exactp-a
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (or (drepp$ (drnd$ x mode p q) p q)
               (= (drnd$ x mode p q) 0)
               (= (drnd$ x mode p q) (* (sgn x) (spn$ q)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-a (mode (old-mode mode)))))))

(defthmd drnd$-exactp-b
  (implies (and (rationalp x)
	        (drepp$ x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (equal (drnd$ x mode p q)
                  x))
  :hints (("Goal" :use ((:instance drnd-exactp-b (mode (old-mode mode)))))))

(defthm drnd$-exactp-c
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
		(rationalp a)
                (drepp$ a p q)
		(>= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (>= a (drnd$ x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-c (mode (old-mode mode)))))))

(defthm drnd$-exactp-d
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
		(rationalp a)
                (drepp$ a p q)
		(<= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (<= a (drnd$ x mode p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-exactp-d (mode (old-mode mode)))))))

(defthm drnd$-rtz$
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn$ q)))
           (<= (abs (drnd$ x 'rtz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use drnd-trunc)))

(defthm drnd$-raz$
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn$ q)))
           (>= (abs (drnd$ x 'raz p q))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use drnd-away)))

(defthm drnd$-rdn$
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn$ q)))
           (<= (drnd$ x 'rdn p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use drnd-minf)))

(defthm drnd$-rup$
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn$ q)))
           (>= (drnd$ x 'rup p q)
               x))
  :rule-classes ()
  :hints (("Goal" :use drnd-inf)))

(defthm drnd$-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-mode-p mode))
           (< (abs (- x (drnd$ x mode p q))) (spd$ p q)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-diff (mode (old-mode mode)))))))

(defthm drnd$-rne$-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp$ a p q))
           (>= (abs (- x a)) (abs (- x (drnd$ x 'rne p q)))))
  :rule-classes ()
  :hints (("Goal" :use drnd-near-est)))

(defthm drnd$-rna$-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp$ a p q))
           (>= (abs (- x a)) (abs (- x (drnd$ x 'rna p q)))))
  :rule-classes ()
  :hints (("Goal" :use drnd-near+-est)))

(defthmd drnd$-rto$
    (implies (and (common-mode-p mode)
		  (natp p)
		  (> p 1)
		  (natp q)
		  (> q 0)
		  (rationalp x)
                  (<= (abs x) (spn$ q))
		  (natp n)
		  (>= n (+ p (expo x) (- (expo (spn$ q))) 2)))
	     (equal (drnd$ (rto$ x n) mode p q)
		    (drnd$ x mode p q)))
  :hints (("Goal" :use ((:instance drnd-sticky (mode (old-mode mode)))))))

(defthmd drnd$-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn$ q))
                (common-mode-p mode)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (drnd$ x mode p q)
                  (- (rnd$ (+ x (* (sgn x) (spn$ q))) mode p)
		     (* (sgn x) (spn$ q)))))
  :hints (("Goal" :use ((:instance drnd-rewrite (mode (old-mode mode)))))))

(defthmd drnd$-tiny
  (implies (and (common-mode-p mode)
                (natp p)
                (> p 1)
                (natp q)
                (> q 0)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd$ p q) 2)))
           (equal (drnd$ x mode p q)
                  (if (member mode '(raz rup))
                      (spd$ p q)
                     0)))
  :hints (("Goal" :in-theory (enable ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p)
                  :use ((:instance drnd-tiny (mode (old-mode mode)))))))

(defthm drnd$-tiny-equal
    (implies (and (common-mode-p mode)
                  (natp p)
                  (> p 1)
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd$ p q) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd$ p q) 2)))
             (equal (drnd$ x mode p q)
                    (drnd$ y mode p q)))
    :rule-classes ()
  :hints (("Goal" :use ((:instance drnd-tiny-equal (mode (old-mode mode)))))))

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
           (let* ((x (rtz$ r k))
                  (sticky (if (< x r) 1 0)))
	     (equal (rnd$ r mode n)
                    (if (round-up-p x sticky mode n)
                        (fp+$ (rtz$ r n) n)
                      (rtz$ r n)))))
  :hints (("Goal" :in-theory (enable round-up-p ieee-mode-p ieee-rounding-mode-p common-rounding-mode-p common-mode-p rnd-const rnd$-const)
                  :use ((:instance round-up-thm (mode (old-mode mode)))))))

)) ;; (local (encapsulate

(local (include-book "basic"))
(local (include-book "bits"))
(local (include-book "float"))
(include-book "reps")

(local (include-book "arithmetic-5/top" :dir :system))

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

(defnd expo (x)
  (declare (xargs :measure (:? x)
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))

(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (declare (xargs :guard (and (real/rationalp x) (integerp n))
                  :verify-guards nil))
  (integerp (* (sig x) (expt 2 (1- n)))))

(local-defthm exactp-rewrite
  (equal (exactp x n) (exactp$ x n))
  :hints (("Goal" :in-theory (enable exactp exactp$))))

(defun fp+ (x n)
  (declare (xargs :guard (and (real/rationalp x) (integerp n))
                  :verify-guards nil))
  (+ x (expt 2 (- (1+ (expo x)) n))))

(local-defthm fp+-rewrite
  (equal (fp+ x n) (fp+$ x n))
  :hints (("Goal" :in-theory (enable fp+ fp+$))))

;; From reps.lisp:
#|
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
|#

;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

(defund rtz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm rtz-rewrite-to-rtz$
  (equal (rtz x n) (rtz$ x n))
  :hints (("Goal" :in-theory (enable rtz rtz$))))

(defthmd rtz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (rtz x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (rtz$-rewrite))))

(defthmd rtz-minus
  (equal (rtz (- x) n) (- (rtz x n)))
  :hints (("Goal" :use rtz$-minus)))

(defthmd abs-rtz
  (equal (abs (rtz x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))
  :hints (("Goal" :use (abs-rtz$))))

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
  :hints (("Goal" :use (sgn-rtz$))))

(defthm rtz-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n)))
            (< 0 (rtz x n)))
   :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (rtz$-positive))))

(defthm rtz-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (rtz x n) 0))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (rtz$-negative))))

(defthm rtz-neg-bits
    (implies (and (integerp n)
		  (<= n 0))
	     (equal (rtz x n) 0))
  :hints (("Goal" :use (rtz$-neg-bits))))

(defthm rtz-0
  (equal (rtz 0 n) 0)
  :hints (("Goal" :use (rtz$-0))))

(defthmd rtz-shift
  (implies (integerp n)
           (equal (rtz (* x (expt 2 k)) n)
                  (* (rtz x n) (expt 2 k))))
  :hints (("Goal" :use (rtz$-shift))))

(defthm expo-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (rtz x n))
                    (expo x)))
  :hints (("Goal" :use (expo-rtz$))))

(defthmd rtz-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (rtz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use (rtz$-upper-bound))))

(defthmd rtz-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (rtz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use (rtz$-upper-pos))))

(defthmd rtz-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (rtz x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use (rtz$-lower-bound))))

(defthm rtz-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (abs (- x (rtz x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use (rtz$-diff))))

(defthmd rtz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n)))
           (equal (rtz x n) a))
  :hints (("Goal" :use (rtz$-squeeze))))

(defthm rtz-exactp-a
  (exactp (rtz x n) n)
  :hints (("Goal" :use (rtz$-exactp$-a))))

(defthmd rtz-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rtz x n))))
  :hints (("Goal" :use (rtz$-exactp$-b))))

(defthm rtz-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use (rtz$-exactp$-c))))

(defthmd rtz-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (rtz x n) (rtz y n)))
  :rule-classes :linear
  :hints (("Goal" :use (rtz$-monotone))))

(defthmd rtz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rtz x n)
                    (- x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use (rtz$-midpoint))))

(defthm rtz-rtz
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (rtz (rtz x n) m)
		    (rtz x m)))
  :hints (("Goal" :use (rtz$-rtz$))))

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
  :hints (("Goal" :use (plus-rtz$))))

(defthm minus-rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (- x (rtz y k))
                (- (rtz (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ()
  :hints (("Goal" :use (minus-rtz$))))

(defthmd bits-rtz
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (equal (rtz x k)
                  (* (expt 2 (- n k))
                     (bits x (1- n) (- n k)))))
  :hints (("Goal" :use (bits-rtz$))))

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
  :hints (("Goal" :use (bits-rtz$-bits))))

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
  :hints (("Goal" :use (rtz$-split))))

(defthmd rtz-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) ;(> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (equal (rtz x k)
                  (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :hints (("Goal" :use (rtz$-logand))))


;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************

(defund raz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm raz-rewrite-to-raz$
  (equal (raz x n) (raz$ x n))
  :hints (("Goal" :in-theory (enable raz raz$))))

(defthmd raz-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (raz x n)
		    (* (sgn x)
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use (raz$-rewrite))))

(defthmd raz-minus
  (equal (raz (- x) n) (- (raz x n)))
  :hints (("Goal" :use raz$-minus)))

(defthmd abs-raz
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (raz x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :use abs-raz$)))


(defthm raz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (raz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-raz
  (equal (sgn (raz x n))
         (sgn x))
  :hints (("Goal" :use sgn-raz$)))

(defthm raz-positive
  (implies (and (< 0 x)
                (case-split (rationalp x)))
           (< 0 (raz x n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use raz$-positive)))

(defthm raz-negative
    (implies (and (< x 0)
                  (case-split (rationalp x)))
	     (< (raz x n) 0))
    :rule-classes (:rewrite :linear)
  :hints (("Goal" :use raz$-negative)))

(defthm raz-neg-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n))
           (equal (raz x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
  :hints (("Goal" :use raz$-neg-bits)))

(defthm raz-0
  (equal (raz 0 n) 0)
  :hints (("Goal" :use raz$-0)))

(defthm raz-shift
    (implies (integerp n)
	     (= (raz (* x (expt 2 k)) n)
		(* (raz x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use raz$-shift)))

(defthmd raz-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (raz x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :use raz$-lower-bound)))

(defthmd raz-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (raz x n) x))
  :rule-classes :linear
  :hints (("Goal" :use raz$-lower-pos)))

(defthmd raz-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (raz x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :use raz$-upper-bound)))

(defthmd raz-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (raz x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use raz$-diff)))

(defthm raz-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (raz x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use raz$-expo-upper)))

(defthmd expo-raz-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (raz x n)) (expo x)))
  :rule-classes :linear
  :hints (("Goal" :use expo-raz$-lower-bound)))

(defthmd expo-raz
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (raz x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (raz x n))
                    (expo x)))
  :hints (("Goal" :use expo-raz$)))

(defthmd expo-raz-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (raz x n)) (1+ (expo x))))
  :rule-classes :linear
  :hints (("Goal" :use expo-raz$-upper-bound)))

(defthmd raz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (<= x (fp+ a n)))
           (equal (raz x n) (fp+ a n)))
  :hints (("Goal" :use (raz$-squeeze))))

(defthm raz-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (raz x n) n))
  :hints (("Goal" :use raz$-exactp$-a)))

(defthmd raz-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (raz x n))))
  :hints (("Goal" :use raz$-exactp$-b)))

(defthm raz-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use raz$-exactp$-c)))

(defthmd raz-up
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (raz x n)) (expt 2 k)))
           (equal (abs (raz x m)) (expt 2 k)))
  :hints (("Goal" :use raz$-up)))

(defthmd raz-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (raz x n) (raz y n)))
  :rule-classes :linear
  :hints (("Goal" :use raz$-monotone)))

(defthmd rtz-raz
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (equal (raz x n)
	            (+ (rtz x n)
		       (expt 2 (+ (expo x) 1 (- n))))))
  :hints (("Goal" :use rtz$-raz$)))

(defthmd raz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (raz x n)
		    (+ x (expt 2 (- (expo x) n)))))
  :hints (("Goal" :use raz$-midpoint)))

(defthmd raz-raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (raz (raz x n) m)
		    (raz x m)))
  :hints (("Goal" :use raz$-raz$)))

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
  :hints (("Goal" :use plus-raz$)))

(defthm minus-rtz-raz
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (exactp x (+ k (- (expo x) (expo y)))))
           (= (- x (rtz y k))
              (raz (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :use minus-rtz$-raz$)))

(defthm rtz-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (- (expo y))))
                  (exactp x k1)
                  (> k2 0))
             (= (+ x (rtz y k))
                (if (= (sgn (+ x y)) (sgn y))
                    (rtz (+ x y) k2)
                  (raz (+ x y) k2))))
  :rule-classes ()
  :hints (("Goal" :use rtz$-plus-minus)))

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
  :hints (("Goal" :use raz$-imp)))

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defun re (x)
  (declare (xargs :guard (real/rationalp x)))
  (- x (fl x)))

(local-defthm re-rewrite
  (equal (re x) (re$ x)))

(defund rne (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(local-defthm rne-rewrite
  (equal (rne x n) (rne$ x n))
  :hints (("Goal" :in-theory (enable rne rne$))))

(defthm rne-choice
    (or (= (rne x n) (rtz x n))
	(= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use rne$-choice)))

(defthmd rne-minus
  (equal (rne (- x) n) (- (rne x n)))
  :hints (("Goal" :use rne$-minus)))

(defthmd sgn-rne
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rne x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-rne$)))

(defthm rne-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (rne x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use rne$-positive)))

(defthmd rne-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n))
           (< (rne x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use rne$-negative)))

(defthm rne-0
  (equal (rne 0 n) 0)
  :hints (("Goal" :use rne$-0)))

(defthm expo-rne
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (rne x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rne x n))
                    (expo x)))
  :hints (("Goal" :use expo-rne$)))

(defthm rne<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use rne$<=raz$)))

(defthm rne>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rne x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use rne$>=rtz$)))

(defthm rne-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (rne (* x (expt 2 k)) n)
		(* (rne x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use rne$-shift)))

(defthm rne-exactp-a
    (implies (< 0 n)
	     (exactp (rne x n) n))
  :hints (("Goal" :use rne$-exactp$-a)))

(defthmd rne-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rne x n))))
  :hints (("Goal" :use rne$-exactp$-b)))

(defthm rne-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use rne$-exactp$-c)))

(defthm rne-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use rne$-exactp$-d)))

(defthmd rne-rtz
    (implies (and (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (rne x n)
                    (rtz x n)))
  :hints (("Goal" :use rne$-rtz$)))

(defthmd rne-raz
  (implies (and (> (abs (- x (rtz x n)))
                   (abs (- (raz x n) x)))
                (rationalp x)
                (integerp n))
           (equal (rne x n)
                  (raz x n)))
  :hints (("Goal" :use rne$-raz$)))

(defthmd rne-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) a))
  :hints (("Goal" :use (rne$-down))))

(defthmd rne-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) (fp+ a n)))
  :hints (("Goal" :use (rne$-up))))

(defthmd rne-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rne x n)) (expt 2 k)))
           (equal (abs (rne x m)) (expt 2 k)))
  :hints (("Goal" :use (rne$-up-2))))

(defthm rne-nearest
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rne x n)))))
  :rule-classes ()
  :hints (("Goal" :use rne$-nearest)))

(defthm rne-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use rne$-diff)))

(defthm rne-diff-cor
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :use rne$-diff-cor)))

(defthm rf-1
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (>= (expo z) e)))
  :rule-classes ()
  :hints (("Goal" :use (expo-rne))))

(defthm rf-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
             (> (expt 2 (expo x)) (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use (expo-lower-bound))))

(defthm rf-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
                  (> x 0))
             (> x (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use (rf-2 expo-lower-bound)
                  :in-theory (disable ACL2::EXPT-IS-INCREASING-FOR-BASE->-1 ACL2::|(< (expt x n) (expt x m))|
                                      ACL2::|(* (expt x m) (expt x n))| ACL2::|(* (expt c m) (expt d n))|
                                      ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthm rf-4
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (> y 0))
  :rule-classes ()
  :hints (("Goal" :use (rf-3))))

(defthm rf-5
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)))
               (>= (expo y) e)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp-2**n fp-) (exactp-rewrite))
                  :use (rf-4 expo-lower-bound
                        (:instance expo>= (x y) (n (expo x)))
                        (:instance fp-2 (x (expt 2 (expo x))))))))

(defthm rf-6
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (< (+ (abs (- x y)) (abs (- x z))) (+ (expt 2 (- e n)) (expt 2 (- e n))))))
  :rule-classes ()
  :hints (("Goal" :use (rne-diff)
                  :in-theory (disable exactp-rewrite abs ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS))))

(defthm rf-7
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (< (abs (- y z)) (expt 2 (1+ (- e n))))))
  :rule-classes ()
  :hints (("Goal" :use (rf-6))))

(defthm rf-8
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)))
               (<= (+ y (expt 2 (1+ (- e n))))
                   (fp+ y n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fp+) :use (rf-5))))

(defthm rf-9
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (< z (+ y (expt 2 (1+ (- e n)))))))
  :rule-classes ()
  :hints (("Goal" :use (rf-7))))

(defthm rf-10
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((z (rne x n)))
               (< z (fp+ y n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ACL2::|(+ (+ x y) z)| ACL2::|(+ 0 x)|
ACL2::|(+ x (- x))| ACL2::|(+ y (+ x z))| ACL2::|(+ y x)|
ACL2::|(- (+ x y))| ACL2::|(- (- x))| ACL2::|(< (expt x n) (expt x m))|
ACL2::|(< (if a b c) x)| ACL2::BUBBLE-DOWN-+-MATCH-1
ACL2::BUBBLE-DOWN-+-MATCH-3 ACL2::NORMALIZE-ADDENDS
ACL2::PREFER-POSITIVE-ADDENDS-< ACL2::REMOVE-STRICT-INEQUALITIES
ACL2::SIMPLIFY-SUMS-<)
                  :use (rf-9 rf-8))))

(defthm rf-11
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((z (rne x n)))
               (>= y z)))
  :rule-classes ()
  :hints (("Goal" :use (rf-4 rf-10 (:instance fp+2 (y (rne x n)) (x y))))))

(defthm rf-12
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (<= (+ z (expt 2 (1+ (- e n))))
                   (fp+ z n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fp+) :use (rf-1))))

(defthm rf-13
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((e (expo x)) (z (rne x n)))
               (< y (+ z (expt 2 (1+ (- e n)))))))
  :rule-classes ()
  :hints (("Goal" :use (rf-7))))

(defthm rf-14
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((z (rne x n)))
               (< y (fp+ z n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ACL2::|(+ (+ x y) z)| ACL2::|(+ 0 x)|
ACL2::|(+ x (- x))| ACL2::|(+ y (+ x z))| ACL2::|(+ y x)|
ACL2::|(- (+ x y))| ACL2::|(- (- x))| ACL2::|(< (expt x n) (expt x m))|
ACL2::|(< (if a b c) x)| ACL2::BUBBLE-DOWN-+-MATCH-1
ACL2::BUBBLE-DOWN-+-MATCH-3 ACL2::NORMALIZE-ADDENDS
ACL2::PREFER-POSITIVE-ADDENDS-< ACL2::REMOVE-STRICT-INEQUALITIES
ACL2::SIMPLIFY-SUMS-< ACL2::REDUCE-ADDITIVE-CONSTANT-<)
                  :use (rf-12 rf-13))))

(defthm rf-15
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (let ((z (rne x n)))
               (<= y z)))
  :rule-classes ()
  :hints (("Goal" :use (rf-4 rf-14 (:instance fp+2 (x (rne x n)))))))

(defthm rf-16
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (> x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (= y (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use (rf-11 rf-15))))

(defthm rf-17
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
                  (< x 0)
                  (< (abs (- x y)) (expt 2 (- (expo x) n))))
             (= y (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use (rne-minus
                       (:instance minus-exactp (x y))
                       (:instance rf-16 (x (- x)) (y (- y)))))))

(defthm rne-force
    (implies (and (integerp n)
		  (> n 0)
                  (rationalp x)
                  (not (= x 0))
		  (rationalp y)
                  (exactp y n)
		  (< (abs (- x y)) (expt 2 (- (expo x) n))))
	     (= y (rne x n)))
  :rule-classes ()
  :hints (("Goal" :use (rf-16 rf-17))))

(defthm rne-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  ;(<= 0 x) ;; not necessary
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (rne y n)))
  :rule-classes ()
  :hints (("Goal" :use rne$-monotone)))

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
  :hints (("Goal" :in-theory (enable rne-witness rne$-witness)
                  :use rne$-rne$-lemma)))

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
  :hints (("Goal" :use rne$-rne$)))

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
  :hints (("Goal" :use rne$-boundary)))

(defthm rne-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (rne x n) (1- n)))
  :rule-classes ()
  :hints (("Goal" :use rne$-midpoint)))

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
  :hints (("Goal" :use plus-rne$)))

(defthmd rne-imp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (equal (rne x n)
   		    (if (and (exactp x (1+ n)) (not (exactp x n)))
		        (rtz (+ x (expt 2 (- (expo x) n))) (1- n))
		      (rtz (+ x (expt 2 (- (expo x) n))) n))))
  :hints (("Goal" :use rne$-imp)))

(defund rna (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(local-defthm rna-rewrite
  (equal (rna x n) (rna$ x n))
  :hints (("Goal" :in-theory (enable rna rna$))))

(defthm rna-choice
    (or (= (rna x n) (rtz x n))
	(= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use rna$-choice)))

(defthmd rna-minus
  (equal (rna (- x) n) (- (rna x n)))
  :hints (("Goal" :use rna$-minus)))

(defthm rna<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rna x n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use rna$<=raz$)))

(defthm rna>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rna x n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use rna$>=rtz$)))

(defthm rna-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (rna (* x (expt 2 k)) n)
		(* (rna x n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use rna$-shift)))

(defthm rna-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use rna$-positive)))

(defthm rna-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (rna x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use rna$-negative)))

(defthm rna-0
  (equal (rna 0 n) 0)
  :hints (("Goal" :use rna$-0)))

(defthm sgn-rna
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rna x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-rna$)))

(defthm rna-exactp-a
    (implies (> n 0)
	     (exactp (rna x n) n))
  :hints (("Goal" :use rna$-exactp$-a)))

(defthmd rna-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rna x n))))
  :hints (("Goal" :use rna$-exactp$-b)))

(defthm rna-exactp-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use rna$-exactp$-c)))

(defthm rna-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rna x n)))
  :rule-classes ()
  :hints (("Goal" :use rna$-exactp$-d)))

(defthmd expo-rna
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (rna x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rna x n))
                    (expo x)))
  :hints (("Goal" :use expo-rna$)))

(defthmd rna-rtz
    (implies (and (rationalp x)
		  (integerp n)
		  (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (rtz x n)))
  :hints (("Goal" :use rna$-rtz$)))

(defthmd rna-raz
    (implies (and (rationalp x)
		  (integerp n)
		  (> (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (raz x n)))
  :hints (("Goal" :use rna$-raz$)))

(defthmd rna-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna x n) a))
  :hints (("Goal" :use (rna$-down))))

(defthmd rna-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna x n) (fp+ a n)))
  :hints (("Goal" :use (rna$-up))))

(defthmd rna-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rna x n)) (expt 2 k)))
           (equal (abs (rna x m)) (expt 2 k)))
  :hints (("Goal" :use (rna$-up-2))))

(defthm rna-nearest
    (implies (and (exactp y n)
                  (rationalp x)
                  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rna x n)))))
  :rule-classes ()
  :hints (("Goal" :use rna$-nearest)))

(defthm rna-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rna x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("Goal" :use rna$-diff)))

(defthm rna-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rna x n) (rna y n)))
  :rule-classes ()
  :hints (("Goal" :use rna$-monotone)))

(encapsulate ()

(local (include-book "basic"))
(local (include-book "bits"))
(local (include-book "log"))
(local (include-book "float"))

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(defun rna-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rna x n) (rna y n)) 2)
    (expt 2 (expo y))))
(local (in-theory (enable rna-witness)))

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
  :hints (("Goal" :in-theory (e/d (exactp2) (exactp-rewrite))
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
  :hints (("Goal" :in-theory (e/d (exactp2) (exactp-rewrite))
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
  :hints (("Goal" :use rna$-midpoint)))

(defthm rne-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rne x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use rne$-power-2)))

(defthm rtz-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rtz (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use rtz$-power-2)))

(defthm rna-power-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (rna x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use rna$-power-2)))

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
  :hints (("Goal" :use plus-rna$)))

(defthmd rna-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (equal (rna x n)
		    (rtz (+ x (expt 2 (- (expo x) n))) n)))
  :hints (("Goal" :use rna$-imp)))

(defthmd rna-imp-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (equal (rna (rtz x n) m)
                    (rna x m)))
  :hints (("Goal" :use rna$-imp-cor)))

;;;**********************************************************************
;;;                          Odd Rounding
;;;**********************************************************************

(defund rto (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(local-defthm rto-rewrite
  (equal (rto x n) (rto$ x n))
  :hints (("Goal" :in-theory (enable rto rto$))))

(defthm sgn-rto
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rto x n))
		    (sgn x)))
  :hints (("Goal" :use sgn-rto$)))

(defthmd rto-minus
  (equal (rto (- x) n) (- (rto x n)))
  :hints (("Goal" :use rto$-minus)))

(defthmd rto-positive
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use rto$-positive)))

(defthmd rto-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (rto x n) 0))
  :rule-classes :linear
  :hints (("Goal" :use rto$-negative)))

(defthm rto-0
  (equal (rto 0 n) 0)
  :hints (("Goal" :use rto$-0)))

(defthmd rto-minus
  (equal (rto (- x) n) (- (rto x n)))
  :hints (("Goal" :use rto$-minus)))

(defthm rto-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (rto (* (expt 2 k) x) n)
		(* (expt 2 k) (rto x n))))
  :rule-classes ()
  :hints (("Goal" :use rto$-shift)))

(defthm expo-rto
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (equal (expo (rto x n))
		    (expo x)))
  :hints (("Goal" :use expo-rto$)))

(defthm rto-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (rto x n) n))
  :hints (("Goal" :use rto$-exactp$-a)))

(defthmd rto-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rto x n))))
  :hints (("Goal" :use rto$-exactp$-b)))

(defthm rto-exactp-c
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (rto x n) m)
		  (exactp x m)))
  :hints (("Goal" :use rto$-exactp$-c)))

(defthmd rto-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rto x n) (rto y n)))
  :rule-classes :linear
  :hints (("Goal" :use rto$-monotone)))

(defthmd rtz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (rtz (rto x n) m)
		    (rtz x m)))
  :hints (("Goal" :use rtz$-rto$)))

(defthmd raz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (raz (rto x n) m)
		    (raz x m)))
  :hints (("Goal" :use raz$-rto$)))

(defthmd rne-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rne (rto x n) m)
		    (rne x m)))
  :hints (("Goal" :use rne$-rto$)))

(defthmd rna-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rna (rto x n) m)
		    (rna x m)))
  :hints (("Goal" :use rna$-rto$)))

(defthm rto-rto
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (equal (rto (rto x n) m)
		    (rto x m)))
  :hints (("Goal" :use rto$-rto$)))

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
  :hints (("Goal" :use rto$-plus)))


;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

(defun rup (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(local-defthm rup-rewrite
  (equal (rup x n) (rup$ x n)))

(local (in-theory (disable rup)))

(defthmd rup-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (rup x n) x))
  :rule-classes :linear
  :hints (("Goal" :use rup$-lower-bound)))

(defun rdn (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))
                  :verify-guards nil))
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(local-defthm rdn-rewrite
  (equal (rdn x n) (rdn$ x n)))

(local (in-theory (disable rdn)))

(defthmd rdn-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (rdn x n) x))
  :rule-classes :linear
  :hints (("Goal" :use rdn$-lower-bound)))

(defnd IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defnd common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defthm ieee-mode-is-common-mode
  (implies (IEEE-rounding-mode-p mode)
           (common-mode-p mode))
  :hints (("Goal" :in-theory (enable common-mode-p))))

(defund rnd (x mode n)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (integerp n))
                  :verify-guards nil))
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(local-defthm rnd-rewrite
  (equal (rnd x mode n) (rnd$ x mode n))
  :hints (("Goal" :in-theory (enable rnd rnd$))))
#|
(local-defthm rnd-rnd
  (equal (rnd$ x mode n) (rnd x mode n)))
|#
(defthm rationalp-rnd
  (rationalp (rnd x mode n))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use rationalp-rnd$)))

(defthm rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode))
           (or (= (rnd x mode n) (rtz x n))
	       (= (rnd x mode n) (raz x n))))
  :rule-classes ()
  :hints (("Goal" :use rnd$-choice)))

(defthmd sgn-rnd
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd x mode n))
		    (sgn x)))
  :hints (("Goal" :use sgn-rnd$)))

(defthm rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (> (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use rnd$-positive)))

(defthm rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (< (rnd x mode n) 0))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use rnd$-negative)))

(defthm rnd-0
  (equal (rnd 0 mode n)
         0)
  :hints (("Goal" :use rnd$-0)))

(defthm rnd-non-pos
    (implies (<= x 0)
	     (<= (rnd x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use rnd$-non-pos)))

(defthm rnd-non-neg
    (implies (<= 0 x)
	     (<= 0 (rnd x mode n)))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :use rnd$-non-neg)))

(defund flip-mode (m)
  (declare (xargs :guard (common-mode-p m)))
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
  (equal (rnd (- x) mode n)
         (- (rnd x (flip-mode mode) n)))
  :hints (("Goal" :use rnd$-minus)))

(defthm rnd-exactp-a
    (implies (< 0 n)
	     (exactp (rnd x mode n) n))
  :hints (("Goal" :use rnd$-exactp$-a)))

(defthmd rnd-exactp-b
  (implies (and (rationalp x)
                (common-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (exactp x n)
                  (equal x (rnd x mode n))))
  :hints (("Goal" :use rnd$-exactp$-b)))

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
  :hints (("Goal" :use rnd$-exactp$-c)))

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
  :hints (("Goal" :use rnd$-exactp$-d )))

(defthm rnd<=raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (Common-mode-p mode)
		  (natp n))
	     (<= (rnd x mode n) (raz x n)))
  :rule-classes ()
  :hints (("Goal" :use rnd$<=raz$)))

(defthm rnd>=rtz
    (implies (and (rationalp x)
		  (> x 0) ;;
		  (common-mode-p mode)
                  (integerp n)
                  (> N 0))
	     (>= (rnd x mode n) (rtz x n)))
  :rule-classes ()
  :hints (("Goal" :use rnd$>=rtz$)))

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
  :hints (("Goal" :use (rnd$<equal
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
  :hints (("Goal" :use (rnd$>equal
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
  :hints (("Goal" :use (rnd$-near-equal
                        (:instance rna-rna (y x) (x y) (k n) (a (rtz x (1+ n))))
                        (:instance rna-rna (k n) (a (rtz x (1+ n))))))))

(defthm rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ()
  :hints (("Goal" :use rnd$-diff)))

(defthmd expo-rnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (equal (expo (rnd x mode n))
                    (expo x)))
  :hints (("Goal" :use expo-rnd$)))

(defthm rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-mode-p mode)
                  (integerp N)
                  (> N 0))
	     (<= (rnd x mode n) (rnd y mode n)))
  :rule-classes ()
  :hints (("Goal" :use rnd$-monotone)))

(defthm rnd-shift
    (implies (and (rationalp x)
 (integerp n)
		  (common-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use rnd$-shift)))

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
  :hints (("Goal" :use plus-rnd$)))

(defthmd rnd-rto
  (implies (and (common-mode-p mode)
                (rationalp x)
                (integerp m)
		(> m 0)
                (integerp n)
		(>= n (+ m 2)))
           (equal (rnd (rto x n) mode m)
                  (rnd x mode m)))
  :hints (("Goal" :use rnd$-rto$)))

(defthmd rnd-up
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (common-mode-p mode)
                (= (abs (rnd x mode n)) (expt 2 k)))
           (equal (abs (rnd x mode m)) (expt 2 k)))
  :hints (("Goal" :in-theory (e/d (common-mode-p rup rdn rnd) (rnd-rewrite))
                  :use (raz-up rne-up-2 rna-up-2 rtz-upper-bound))))

(defun rnd-const (e mode n)
  (declare (xargs :guard (and (integerp e)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(local-defthm rnd$-rnd-const
  (equal (rnd$-const e mode n) (rnd-const e mode n)))

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
  :hints (("Goal" :use rnd$-const-thm)))

(local-defund round-up-p (x sticky mode n)
  (case mode
    (rna (= (bitn x (- (expo x) n)) 1))
    (rne (and (= (bitn x (- (expo x) n)) 1)
               (or (not (= (bits x (- (expo x) (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((rup raz) (or (not (= (bits x (- (expo x) n) 0) 0))
                    (= sticky 1)))
    (otherwise ())))

(local-defthmd round-up-p-thm
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

(defund roundup-pos (x e sticky mode n)
  (declare (xargs :guard (and (integerp x)
                              (integerp e)
                              (integerp sticky)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rup raz) (or (not (= (bits x (- e n) 0) 0))
                   (= sticky 1)))
    (rna (= (bitn x (- e n)) 1))
    (rne (and (= (bitn x (- e n)) 1)
               (or (not (= (bits x (- e (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ e) n)) 1))))
    (otherwise ())))

(local-defthmd rp-1
  (implies (and (rationalp z)
                (> z 0))
           (equal (fl z) (rtz z (1+ (expo z)))))
  :hints (("Goal" :in-theory (e/d (rtz sgn) (rtz-rewrite-to-rtz$))
                  :use ((:instance fp-rep (x z))))))

(local-defthmd rp-2
  (implies (and (common-mode-p mode)
                (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z))
                 (sticky (if (integerp z) 0 1)))
             (equal (rnd z mode n)
                    (if (roundup-pos x (expo x) sticky mode n)
                        (fp+ (rtz x n) n)
                      (rtz x n)))))
  :hints (("Goal" :in-theory (enable round-up-p roundup-pos)
                  :use (rp-1
                        (:instance round-up-p-thm (k (1+ (expo z))))
                        (:instance expo>= (x z))))))

(local-defthmd rp-3
  (implies (and (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z)))
             (iff (exactp z n)
                  (and (integerp z) (= (rtz x n) x)))))
  :hints (("Goal" :in-theory (e/d (rtz-exactp-b) (rtz-rtz rtz-rewrite-to-rtz$ exactp-rewrite))
                  :use (rp-1
                        (:instance rtz-rtz (x z) (m (1+ (expo z))))
                        (:instance rtz-upper-pos (x (rtz z (1+ (expo z)))))
                        (:instance expo>= (x z))))))

(local-defthmd rp-4
  (implies (and (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (equal (expo (fl z)) (expo z)))
  :hints (("Goal" :use ((:instance expo>= (x z))
                        (:instance expo-lower-bound (x z))
                        (:instance expo-upper-bound (x z))
                        (:instance n<=fl-linear (x z) (n (expt 2 (expo z))))
                        (:instance expo-unique (x (fl z)) (n (expo z)))))))

(local-defthmd rp-5
  (implies (and (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z)))
             (iff (exactp z n)
                  (and (integerp z) (= (bits x (- (expo x) n) 0) 0)))))
  :hints (("Goal" :use (rp-3 rp-4
                        (:instance rtz-exactp-b (x z))
                        (:instance exact-bits-1 (x (fl z)) (n (1+ (expo z))) (k (- (1+ (expo z)) n)))
                        (:instance exact-bits-3 (x (fl z)) (k (- (1+ (expo z)) n)))))))

(defthmd roundup-pos-thm-1
  (implies (and (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z)))
             (iff (exactp z n)
                  (and (integerp z) (= (bits x (- (expo x) n) 0) 0)))))
  :hints (("Goal" :use rp-5)))

(defthmd roundup-pos-thm-2
  (implies (and (common-mode-p mode)
                (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z))
                 (sticky (if (integerp z) 0 1)))
             (equal (rnd z mode n)
                    (if (roundup-pos x (expo x) sticky mode n)
                        (fp+ (rtz x n) n)
                      (rtz x n)))))
  :hints (("Goal" :use rp-2)))

(defthmd roundup-pos-thm
  (implies (and (common-mode-p mode)
                (rationalp z)
                (> z 0)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z))
                 (sticky (if (integerp z) 0 1)))
             (and (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo x) n) 0) 0)))
	          (equal (rnd z mode n)
                         (if (roundup-pos x (expo x) sticky mode n)
                             (fp+ (rtz x n) n)
                           (rtz x n))))))
  :hints (("Goal" :use (rp-2 rp-5))))

(defund roundup-neg (x e sticky mode n)
  (declare (xargs :guard (and (integerp x)
                              (integerp e)
                              (integerp sticky)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rdn raz) t)
    ((rup rtz) (and (= (bits x (- e n) 0) 0)
                    (= sticky 0)))
    (rna (or (= (bitn x (- e n)) 0)
             (and (= (bits x (- e (1+ n)) 0) 0)
                  (= sticky 0))))
    (rne (or (= (bitn x (- e n)) 0)
             (and (= (bitn x (- (1+ e) n)) 0)
                  (= (bits x (- e (1+ n)) 0) 0)
                  (= sticky 0))))
    (otherwise ())))

(local-defthmd rn-1
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n))))
           (let* ((x (+ (fl z) (expt 2 k)))
                  (xc (1- (- (expt 2 k) x)))
                  (f (- z (fl z))))
             (and (<= 0 f)
                  (< f 1)
                  (= (abs z) (- (1+ xc) f))))))

(local-defthm rn-2
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k))))
           (and (<= 0 x)
                (< x (- (expt 2 k) (expt 2 n)))))
  :rule-classes ())

(local-defthm rn-3
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x))))
           (and (<= xc (1- (expt 2 k)))
                (>= xc (expt 2 n))))
  :rule-classes ())

(local-defthm rn-4
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x))))
           (>= (expo xc) n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo>= (x xc))))))

(local-defthm rn-5
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
           (<= xc (1- (expt 2 (1+ e)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4
                        (:instance expo-upper-bound (x xc))))))

(local-defthm rn-6
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
           (>= (expo z) e))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-monotone (x xc) (y (abs z)))))))

(local-defthm rn-7
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (or (= (expo z) e)
                 (= z (-(expt 2 (1+ e))))))
  :rule-classes ()
  :hints (("Goal" :use (rn-5 rn-6
                        (:instance expo<= (x (abs z)) (n e))))))

(local-defthm rn-8
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (bvecp xc (1+ e)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance expo-upper-bound (x xc))))))

(local-defthm rn-9
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= xc (+ (rtz xc n)
                      (bits xc (- e n) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8
                        (:instance bits-rtz (x xc) (k n) ( n (1+ e)))
                        (:instance bits-plus-bits (x xc) (n e) (m 0) (p (- (1+ e) n)))))))

(local-defthm rn-10
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z))))
             (= (abs z)
                (+ (rtz xc n)
                   (bits xc (- e n) 0)
                   (- 1 f))))
  :rule-classes ()
  :hints (("Goal" :use (rn-1 rn-9))))

(include-book "log")

(local-defthm rn-11
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits (bits (lognot x) (+ -1 k) 0) (- e n) 0)
                (bits xc (- e n) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lognot)
                  :use ((:instance bits-lognot (i (1- k)) (j 0))))))

(local-defthm rn-12
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (< e k))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-lower-bound (x xc))))))

(local-defthm rn-13
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits xc (- e n) 0)
                (bits (lognot x) (- e n) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-11 rn-12)
                  :in-theory (enable bits-bits))))

(local-defthm rn-14
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits (lognot x) (- e n) 0)
                (1- (- (expt 2 (1+ (- e n))) (bits x (- e n) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 (:instance bits-lognot (i (- e n)) (j 0))))))

(local-defthm rn-15
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (= (abs z) (fp+ (rtz xc n) n)))
  :rule-classes ()
  :hints (("Goal" :use (rn-10 rn-13 rn-14))))

(local-defthm rn-16
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (exactp (fp+ (rtz xc n) n) n))
  :rule-classes ()
  :hints (("Goal" :use (rn-3 rn-15
                        (:instance sgn-rtz (x xc))
                        (:instance fp+1 (x (rtz xc n)))))))

(local-defthm rn-17
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (exactp (abs z) n))
  :rule-classes ()
  :hints (("Goal" :use (rn-16 rn-15)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-18
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (exactp z n))
  :rule-classes ()
  :hints (("Goal" :use (rn-17)
                  :in-theory (disable exactp-rewrite))))

(local-defthm rn-19
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (= (abs (rnd z mode n)) (abs z)))
  :rule-classes ()
  :hints (("Goal" :use (rn-17
                        (:instance rnd-minus (x z))
                        (:instance rnd-exactp-b (x z)))
                  :in-theory (disable rnd-rewrite exactp-rewrite))))

(local-defthm rn-20
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (roundup-neg x (expo xc) sticky mode n))
  :hints (("Goal" :use (rn-4 (:instance bitn-plus-bits (n (- e n)) (m 0)))
                  :in-theory (enable common-mode-p ieee-rounding-mode-p roundup-neg))))

(local-defthm rn-21
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (= f 0)
                (= (bits x (- e n) 0) 0))
             (and (implies (not (= (expo z) e))
                           (= z (- (expt 2 (1+ e)))))
                  (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo xc) n) 0) 0)))
	          (equal (abs (rnd z mode n))
                         (if (roundup-neg x (expo xc) sticky mode n)
                             (fp+ (rtz xc n) n)
                           (rtz xc n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-20 rn-19 rn-18 rn-15 rn-7))))

(local-defthm rn-22
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (not (and (= f 0) (= (bits x (- e n) 0) 0))))
             (and (< (rtz xc n) (abs z))
                  (< (abs z) (fp+ (rtz xc n) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-10 rn-13 rn-14))))

(local-defthm rn-23
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (not (and (= f 0) (= (bits x (- e n) 0) 0))))
             (not (exactp (abs z) n)))
  :rule-classes ()
  :hints (("Goal" :use (rn-22
                        (:instance fp+2 (x (rtz xc n)) (y (abs z)))))))

(local-defthm rn-24
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (> f 0))
             (= xc (fl (abs z))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-minus (x z))))))

(local-defthm rn-25
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
           (= (bitn (bits xc (- e n) 0) (- e n))
              (bitn (bits (lognot x) (- e n) 0) (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-13))))

(local-defthm rn-26
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
           (not (= (bitn xc (- e n))
                   (bitn x (- e n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-bits)
                  :use (rn-25 rn-4
                        (:instance bitn-lognot (n (- e n)))))))

(local-defthm rn-27
  (implies (and (rationalp z)
                (< (fl z) z))
             (equal (+ -1 (- (FL Z))) (fl (- z))))
  :hints (("Goal" :use ((:instance fl-minus (x z))))))

(local-defthm rn-28
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z)))
                (> f 0))
            (equal (rnd (abs z) (flip-mode mode) n)
                   (if (roundup-neg x (expo xc) sticky mode n)
                       (fp+ (rtz xc n) n)
                     (rtz xc n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-24 rn-26
                        (:instance bitn-0-1 (n (- e n)))
                        (:instance bitn-0-1 (x xc) (n (- e n)))
                        (:instance roundup-pos-thm (mode (flip-mode mode)) (z (abs z))))
                  :in-theory (enable rnd roundup-pos roundup-neg common-mode-p ieee-rounding-mode-p flip-mode))))

(local-defthm rn-29
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (integerp z))
            (= (abs z)
               (+ (* (expt 2 (- (1+ e) n)) (bits xc e (- (1+ e) n)))
                  (bits xc (- e n) 0)
                  1)))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4
                        (:instance bits-plus-bits (x xc) (n e) (p (- (1+ e) n)) (m 0))))))


(local-defthm rn-30
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<= (bits xc (- e n) 0) (- (expt 2 (- (1+ e) n)) 2)))
  :rule-classes ()
  :hints (("Goal" :use (rn-13 rn-14))))

(local-defthm rn-31
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<=  (bits xc e (- (1+ e) n))
                 (1- (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4
                        (:instance bits-bounds (x xc) (i e) (j (- (1+ e) n)))))))

(local-defthm hack-1
  (implies (and (rationalp x) (> x 0) (rationalp y) (rationalp z) (<= y z))
           (<= (* x y) (* x z)))
  :rule-classes ())

(local-defthm rn-32
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<= (* (expt 2 (- (1+ e) n)) (bits xc e (- (1+ e) n)))
                (* (expt 2 (- (1+ e) n)) (1- (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-31
                        (:instance hack-1 (x (expt 2 (- (1+ e) n))) (y (bits xc e (- (1+ e) n))) (z (1- (expt 2 n))))))))

(local-defthm hack-2
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp x1)
                (rationalp y1)
                (= a (+ x y 1))
                (<= x x1)
                (<= y y1))
           (<= a (+ x1 y1 1)))
  :rule-classes ())

(local-defthm rn-33
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<= (abs z) (1- (expt 2 (1+ e)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-29 rn-30 rn-32
                        (:instance hack-2 (a (abs z))
                                          (x (* (expt 2 (- (1+ e) n)) (bits xc e (- (1+ e) n))))
                                          (y (bits xc (- e n) 0))
                                          (x1 (* (expt 2 (- (1+ e) n)) (1- (expt 2 n))))
                                          (y1 (- (expt 2 (- (1+ e) n)) 2)))))))

(local-defthm rn-34
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (expo z) e))
  :rule-classes ()
  :hints (("Goal" :use (rn-33 rn-7))))

(local-defthm rn-35
  (implies (and (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x))))
             (= xc (bits (lognot x) (1- k) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance bits-lognot (x (+ (fl z) (expt 2 k))) (i (1- k)) (j 0))))))

(local-defthm rn-36
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bitn xc (- (1+ e) n))
                (bitn (bits (lognot x) (1- k) 0) (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-35)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-37
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bitn xc (- (1+ e) n))
                (bitn (lognot x) (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-36 rn-4 rn-12)
                  :in-theory (enable bitn-bits))))

(local-defthm rn-38
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (not (= (bitn xc (- (1+ e) n))
                     (bitn x (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-37 rn-4 rn-12
                        (:instance bitn-lognot (n (- (1+ e) n)))))))

(local-defthm rn-39
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bitn (bits xc (- e n) 0) (- e n))
                (bitn (bits (lognot x) (- e n) 0) (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-13)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-40
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bitn xc (- e n))
                (bitn (lognot x) (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-39 rn-4)
                  :in-theory (enable bitn-bits))))

(local-defthm rn-41
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (not (= (bitn xc (- e n))
                     (bitn x (- e n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-40 rn-4
                        (:instance bitn-lognot (n (- e n)))))))

(local-defthm rn-42
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits (bits xc (- e n) 0) (1- (- e n)) 0)
                (bits (bits (lognot x) (- e n) 0) (1- (- e n)) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-13)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-43
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits xc (1- (- e n)) 0)
                (bits (lognot x) (1- (- e n)) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-42 rn-4)
                  :in-theory (enable bits-bits))))

(local-defthm rn-44
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc)))
             (= (bits xc (1- (- e n)) 0)
                (1- (- (expt 2 (- e n)) (bits x (1- (- e n)) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-43 rn-4
                        (:instance bits-lognot (i (1- (- e n))) (j 0))))))

(local-defthm rn-45
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) e (- (1+ e) n))
               (fl (/ (mod (abs z) (expt 2 (1+ e))) (expt 2 (- (1+ e) n))))))
  :rule-classes ()
  :hints (("Goal" :use (rn-33 rn-4)
                  :in-theory (enable bits))))

(local-defthm rn-46
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) e (- (1+ e) n))
               (fl (/ (abs z) (expt 2 (- (1+ e) n))))))
  :rule-classes ()
  :hints (("Goal" :use (rn-45 rn-33 rn-4
                        (:instance mod-does-nothing (m (abs z)) (n (expt 2 (1+ e)))))
                  :in-theory (disable mod-does-nothing))))

(local-defthm rn-47
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (integerp z))
            (>=  (abs z) (* (expt 2 (- (1+ e) n)) (bits xc e (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4 rn-29))))

(local-defthm rn-48
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<  (abs z) (* (expt 2 (- (1+ e) n)) (1+ (bits xc e (- (1+ e) n))))))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4 rn-29 rn-30))))

(local-defthm hack-3
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x (* y z))
                (> y 0))
           (>= (/ x y) z))
  :hints (("Goal" :use ((:instance hack-1 (x (/ y)) (y (* y z)) (z x)))))
  :rule-classes ())

(local-defthm rn-49
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (>=  (/ (abs z) (expt 2 (- (1+ e) n)))
                 (bits xc e (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4 rn-47 (:instance hack-3 (y (expt 2 (- (1+ e) n))) (x (abs z)) (z (bits xc e (- (1+ e) n))))))))

(local-defthm hack-4
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (< x (* y z))
                (> y 0))
           (< (/ x y) z))
  :hints (("Goal" :use ((:instance hack-1 (z (/ x y)) (y z) (x y)))))
  :rule-classes ())

(local-defthm rn-50
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (<  (/ (abs z) (* (expt 2 (- (1+ e) n))))
                (1+ (bits xc e (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4 rn-48 (:instance hack-4 (y (expt 2 (- (1+ e) n))) (x (abs z)) (z (1+ (bits xc e (- (1+ e) n)))))))))

(local-defthm rn-51
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (fl  (/ (abs z) (* (expt 2 (- (1+ e) n)))))
               (bits xc e (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-8 rn-4 rn-49 rn-50))))

(local-defthm rn-52
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) e (- (1+ e) n))
               (bits xc e (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-51 rn-46))))

(local-defthm rn-53
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bitn (bits (abs z) e (- (1+ e) n)) 0)
               (bitn (bits xc e (- (1+ e) n)) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-52) :in-theory (theory 'minimal-theory))))

(local-defthm rn-54
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bitn (abs z) (- (1+ e) n))
               (bitn xc (- (1+ e) n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-53 rn-4 rn-8) :in-theory (enable bitn-bits))))

(local-defthm rn-55
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (not (= (bitn (abs z) (- (1+ e) n))
                    (bitn x (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-54 rn-38))))

(local-defthm rn-56
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (rtz (abs z) n)
               (rtz xc n)))
  :rule-classes ()
  :hints (("Goal" :use (rn-52 rn-4 rn-8 rn-3 rn-34
                        (:instance bits-rtz (x (abs z)) (n (1+ e)) (k n))
                        (:instance bits-rtz (x xc) (n (1+ e)) (k n))))))

(local-defthm rn-57
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) (- e n) 0)
               (mod (abs z) (expt 2 (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8) :in-theory (enable bits))))

(local (in-theory (disable ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)))

(local-defthm rn-58
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (mod (+ (* (expt 2 (- (1+ e) n)) (bits xc e (- (1+ e) n)))
                       (bits xc (- e n) 0)
                       1)
                    (expt 2 (- (1+ e) n)))
               (mod (1+ (bits xc (- e n) 0))
                    (expt 2 (- (1+ e) n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8 rn-30
                        (:instance mod-mult (m (1+ (bits xc (- e n) 0))) (a (bits xc e (- (1+ e) n))) (n (expt 2 (- (1+ e) n))))))))

(local-defthm rn-59
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
           (= (mod (1+ (bits xc (- e n) 0))
                   (expt 2 (- (1+ e) n)))
              (1+ (bits xc (- e n) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8 rn-30
                        (:instance mod-does-nothing (m (1+ (bits xc (- e n) 0))) (n (expt 2 (- (1+ e) n)))))
                  :in-theory (disable mod-does-nothing))))

(local-defthm rn-60
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) (- e n) 0)
               (1+ (bits xc (- e n) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8 rn-57 rn-29 rn-59 rn-58)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-61
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0)))
            (= (bits (abs z) (- e n) 0)
               (- (expt 2 (- (1+ e) n)) (bits x (- e n) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rn-4 rn-8 rn-60 rn-13 rn-14))))

(local-defthm rn-62
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (= (bitn x (- e n)) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-plus-bits (n (- e n)) (m 0))))))

(local-defthm rn-63
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (= (bits x (- e n) 0) (expt 2 (- e n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-plus-bits (n (- e n)) (m 0))))))

(local-defthm rn-64
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (= (bits (abs z) (- e n) 0) (- (expt 2 (- (1+ e) n)) (expt 2 (- e n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-63 rn-61))))

(local-defthm hack-5
  (implies (integerp k)
           (equal (expt 2 (1+ k)) (+ (expt 2 k) (expt 2 k))))
  :rule-classes ())

(local-defthm hack-6
  (implies (and (not (zp n))
                (= e  (expo xc)))
           (equal (- (expt 2 (- (1+ e) n)) (expt 2 (- e n)))
                  (expt 2 (- e n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-5 (k (- e n)))))))

(local-defthm rn-65
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (= (bits (abs z) (- e n) 0) (expt 2 (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-64 hack-6)
                  :in-theory (theory 'minimal-theory))))

(local-defthm rn-66
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (and (= (bitn (abs z) (- e n)) 1)
                 (= (bits (abs z) (1- (- e n)) 0) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-65 rn-4
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bits-bounds (x (abs z)) (i (1- (- e n))) (j 0))))))

(local-defthm rn-67
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0)))
            (< (bits xc (- (1- e) n) 0)
               (1- (expt 2 (- e n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-44 rn-4))))

(local-defthm rn-68
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0))
                (= (bitn xc (- e n)) 0))
            (< (bits xc (- e n) 0)
               (1- (expt 2 (- e n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-67 rn-4
                        (:instance bitn-plus-bits (x xc) (n (- e n)) (m 0))))))

(local-defthm rn-69
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0))
                (= (bitn xc (- e n)) 0))
            (< (bits (abs z) (- e n) 0)
               (expt 2 (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-68 rn-60))))

(local-defthm rn-70
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0))
                (= (bitn xc (- e n)) 0))
            (= (bitn (abs z) (- e n)) 0))
  :rule-classes ()
  :hints (("Goal" :use (rn-69 rn-4
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bits-bounds (x (abs z)) (i (1- (- e n))) (j 0))))))

(local-defthm rn-71
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0))
                (= (bitn xc (- e n)) 1))
            (= (bitn (abs z) (- e n)) 1))
  :rule-classes ()
  :hints (("Goal" :use (rn-60 rn-4
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bits-bounds (x (abs z)) (i (1- (- e n))) (j 0))
                        (:instance bitn-plus-bits (x xc) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x xc) (n (- e n)))
                        (:instance bits-bounds (x xc) (i (1- (- e n))) (j 0))))))

(local-defthm rn-72
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0)))
           (= (bitn xc (- e n))
              (bitn (abs z) (- e n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-70 rn-71
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bitn-0-1 (x xc) (n (- e n)))))))

(local-defthm rn-73
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0)))
           (not (= (bitn x (- e n))
                   (bitn (abs z) (- e n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-72 rn-41))))

(local-defthm rn-74
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0)))
           (not (= (bits (abs z) (1- (- e n)) 0) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rn-72 rn-4 rn-60
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bits-bounds (x (abs z)) (i (1- (- e n))) (j 0))
                        (:instance bitn-plus-bits (x xc) (n (- e n)) (m 0))
                        (:instance bitn-0-1 (x xc) (n (- e n)))
                        (:instance bits-bounds (x xc) (i (1- (- e n))) (j 0))))))

(local-defthm rn-75
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (= (bits x (- (1- e) n) 0) 0))
            (equal (rnd (abs z) (flip-mode mode) n)
                   (if (roundup-neg x (expo xc) sticky mode n)
                       (fp+ (rtz xc n) n)
                     (rtz xc n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-55 rn-56 rn-66 rn-4 rn-34
                        (:instance bitn-0-1 (n (- (1+ e) n)))
                        (:instance bitn-0-1 (x (abs z)) (n (- (1+ e) n)))
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bitn-0-1 (n (- e n)))
                        (:instance bitn-plus-bits (n (- e n)) (m 0))
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance roundup-pos-thm (mode (flip-mode mode)) (z (abs z))))
                  :in-theory (enable rnd roundup-pos roundup-neg common-mode-p ieee-rounding-mode-p flip-mode))))

(local-defthm rn-76
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (integerp z)
                (not (= (bits x (- e n) 0) 0))
                (not (= (bits x (- (1- e) n) 0) 0)))
            (equal (rnd (abs z) (flip-mode mode) n)
                   (if (roundup-neg x (expo xc) 0 mode n)
                       (fp+ (rtz xc n) n)
                     (rtz xc n))))
  :rule-classes ()
  :hints (("Goal" :use (rn-56 rn-73 rn-74 rn-4 rn-34
                        (:instance bitn-0-1 (x (abs z)) (n (- e n)))
                        (:instance bitn-0-1 (n (- e n)))
                        (:instance bitn-plus-bits (n (- e n)) (m 0))
                        (:instance bitn-plus-bits (x (abs z)) (n (- e n)) (m 0))
                        (:instance roundup-pos-thm (mode (flip-mode mode)) (z (abs z))))
                  :in-theory (enable rnd roundup-pos roundup-neg common-mode-p ieee-rounding-mode-p flip-mode))))

(local-defthm rn-77
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1))
                (= f (- z (fl z))))
             (and (implies (not (= (expo z) e))
                           (= z (- (expt 2 (1+ e)))))
                  (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo xc) n) 0) 0)))
	          (equal (abs (rnd z mode n))
                         (if (roundup-neg x (expo xc) sticky mode n)
                             (fp+ (rtz xc n) n)
                           (rtz xc n)))))
  :rule-classes ()
  :hints (("Goal" :use (rn-7 rn-21 rn-23 rn-28 rn-7 rn-75 rn-76 (:instance rnd-minus (x (- z))))
                  :in-theory (disable rnd-rewrite exactp-rewrite))))

(local-defthm rn-78
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n)))
                (= x (+ (fl z) (expt 2 k)))
                (= xc (1- (- (expt 2 k) x)))
                (= e (expo xc))
                (= sticky (if (integerp z) 0 1)))
             (and (implies (not (= (expo z) e))
                           (= z (- (expt 2 (1+ e)))))
                  (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo xc) n) 0) 0)))
	          (equal (abs (rnd z mode n))
                         (if (roundup-neg x (expo xc) sticky mode n)
                             (fp+ (rtz xc n) n)
                           (rtz xc n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rn-77 (f (- z (fl z))))))))

(defthm roundup-neg-thm
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (natp k)
                (< n k)
                (<= (- (expt 2 k)) z)
                (< z (- (expt 2 n))))
           (let* ((x (+ (fl z) (expt 2 k)))
                  (xc (1- (- (expt 2 k) x)))
                  (e (expo xc))
                  (sticky (if (integerp z) 0 1)))
             (and (implies (not (= (expo z) e))
                           (= z (- (expt 2 (1+ e)))))
                  (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo xc) n) 0) 0)))
	          (equal (abs (rnd z mode n))
                         (if (roundup-neg x (expo xc) sticky mode n)
                             (fp+ (rtz xc n) n)
                           (rtz xc n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rn-78 (x (+ (fl z) (expt 2 k)))
                                         (xc (1- (- (expt 2 k) (+ (fl z) (expt 2 k)))))
                                         (e (expo (1- (- (expt 2 k) (+ (fl z) (expt 2 k))))))
                                         (sticky (if (integerp z) 0 1)))))))


;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************

(defund drnd (x mode f)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (formatp f))
                  :verify-guards nil))
  (rnd x mode (+ (prec f) (expo x) (- (expo (spn f))))))

(local-defthm bias-rewrite
  (equal (bias f) (bias$ (expw f)))
  :hints (("Goal" :in-theory (enable bias bias$))))

(local-defthm spn-rewrite
  (equal (spn f) (spn$ (expw f)))
  :hints (("Goal" :in-theory (enable spn$ spn))))

(local-defthm spd-rewrite
  (equal (spd f) (spd$ (prec f) (expw f)))
  :hints (("Goal" :in-theory (enable spd$ spd))))

(local-defthm drepp-rewrite
  (implies (formatp f)
           (equal (drepp r f) (drepp$ r (prec f) (expw f))))
  :hints (("Goal" :in-theory (enable bias$ formatp prec expw drepp drepp$))))

(local-defthm drnd-drnd$
  (equal (drnd x mode f) (drnd$ x mode (prec f) (expw f)))
  :hints (("Goal" :in-theory (enable drnd$ drnd))))

(defthmd drnd-minus
  (equal (drnd (- x) mode f)
         (- (drnd x (flip-mode mode) f)))
  :hints (("Goal" :use (:instance drnd$-minus (p (prec f)) (q (expw f))))))

(defthm drnd-exactp-a
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (or (drepp (drnd x mode f) f)
               (= (drnd x mode f) 0)
               (= (drnd x mode f) (* (sgn x) (spn f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-exactp-a (p (prec f)) (q (expw f))))))

(defthmd drnd-exactp-b
  (implies (and (formatp f)
                (rationalp x)
	        (drepp x f)
                (common-mode-p mode))
           (equal (drnd x mode f)
                  x))
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-exactp-b (p (prec f)) (q (expw f))))))

(defthm drnd-exactp-d
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
		(rationalp a)
                (drepp a f)
		(>= a x)
                (common-mode-p mode))
           (>= a (drnd x mode f)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-exactp-c (p (prec f)) (q (expw f))))))

(defthm drnd-exactp-e
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
		(rationalp a)
                (drepp a f)
		(<= a x)
                (common-mode-p mode))
           (<= a (drnd x mode f)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-exactp-d (p (prec f)) (q (expw f))))))

(defthm drnd-rtz
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (<= (abs (drnd x 'rtz f))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rtz$ (p (prec f)) (q (expw f))))))

(defthm drnd-raz
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (>= (abs (drnd x 'raz f))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-raz$ (p (prec f)) (q (expw f))))))

(defthm drnd-rdn
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (<= (drnd x 'rdn f)
               x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rdn$ (p (prec f)) (q (expw f))))))

(defthm drnd-rup
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (>= (drnd x 'rup f)
               x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rup$ (p (prec f)) (q (expw f))))))

(defthm drnd-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (< (abs (- x (drnd x mode f))) (spd f)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-diff (p (prec f)) (q (expw f))))))

(defthm drnd-rne-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (drepp a f))
           (>= (abs (- x a)) (abs (- x (drnd x 'rne f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rne$-diff (p (prec f)) (q (expw f))))))

(defthm drnd-rna-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (drepp a f))
           (>= (abs (- x a)) (abs (- x (drnd x 'rna f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rna$-diff (p (prec f)) (q (expw f))))))

(defthmd drnd-rto
    (implies (and (formatp f)
                  (common-mode-p mode)
		  (rationalp x)
                  (<= (abs x) (spn f))
		  (natp n)
		  (>= n (+ (prec f) (expo x) (- (expo (spn f))) 2)))
	     (equal (drnd (rto x n) mode f)
		    (drnd x mode f)))
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rto$ (p (prec f)) (q (expw f))))))

(defthmd drnd-rewrite
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (equal (drnd x mode f)
                  (- (rnd (+ x (* (sgn x) (spn f))) mode (prec f))
		     (* (sgn x) (spn f)))))
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-rewrite (p (prec f)) (q (expw f))))))

(defthmd drnd-tiny-a
  (implies (and (formatp f)
                (common-mode-p mode)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd f) 2)))
           (equal (drnd x mode f)
                  (if (member mode '(raz rup))
                      (spd f)
                     0)))
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-tiny (p (prec f)) (q (expw f))))))

(defthm drnd-tiny-equal
    (implies (and (formatp f)
                  (common-mode-p mode)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd f) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd f) 2)))
             (equal (drnd x mode f)
                    (drnd y mode f)))
    :rule-classes ()
  :hints (("Goal" :in-theory (enable formatp prec expw)
                  :use (:instance drnd$-tiny-equal (p (prec f)) (q (expw f))))))

(local-in-theory (disable drnd-drnd$ bias-rewrite spn-rewrite spd-rewrite))

(local (include-book "arithmetic-5/top" :dir :system))

(defthmd drnd-tiny-1
  (implies (formatp f)
           (< (+ 2 (- (bias f)) (- (prec f)))
              (+ 1 (- (bias f)))))
  :hints (("goal" :in-theory (enable bias formatp prec expw spd spn ))))

(defthmd drnd-tiny-2
  (implies (formatp f)
            (< (spd f) (spn f)))
  :hints (("Goal" :use (drnd-tiny-1)
                  :in-theory (enable spd spn ))))

(defthmd drnd-tiny-3
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (< x (spd f))
                (common-mode-p mode))
           (equal (drnd x mode f)
                  (- (rnd (+ x (spn f)) mode (prec f))
                     (spn f))))
  :hints (("Goal" :in-theory (enable sgn drnd-rewrite)
                  :use (drnd-tiny-2))))

(defthmd drnd-tiny-4
  (implies (formatp f)
           (equal (fp+ (spn f) (prec f))
                  (+ (spn f) (spd f))))
  :hints (("Goal" :in-theory (enable spn spd fp+))))

(defthmd drnd-tiny-5
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (< x (spd f)))
           (equal (rtz (+ (spn f) x) (prec f))
                  (spn f)))
  :hints (("Goal" :use (drnd-tiny-4
                        (:instance rtz-squeeze (a (spn f)) (n  (prec f)) (x (+ x (spn f)))))
                  :in-theory (e/d (exactp-2**n formatp expw bias prec spn)
                                  (exactp-rewrite)))))

(defthmd drnd-tiny-6
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (< x (spd f)))
           (equal (raz (+ (spn f) x) (prec f))
                  (+ (spn f) (spd f))))
  :hints (("Goal" :use (drnd-tiny-4
                        (:instance raz-squeeze (a (spn f)) (n  (prec f)) (x (+ x (spn f)))))
                  :in-theory (e/d (exactp-2**n formatp expw bias prec spn)
                                  (exactp-rewrite)))))

(defthmd drnd-tiny-7
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd f) 2)))
           (< (abs (- (+ (spn f) x) (rtz (+ (spn f) x) (prec f))))
              (abs (- (+ (spn f) x) (raz (+ (spn f) x) (prec f))))))
  :hints (("Goal" :use (drnd-tiny-5 drnd-tiny-6))))

(defthmd drnd-tiny-8
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd f) 2)))
           (and (equal (rne (+ (spn f) x) (prec f)) (rtz (+ (spn f) x) (prec f)))
                (equal (rna (+ (spn f) x) (prec f)) (rtz (+ (spn f) x) (prec f)))))
  :hints (("Goal" :use (drnd-tiny-7
                        (:instance rne-rtz (x (+ (spn f) x)) (n (prec f)))
                        (:instance rna-rtz (x (+ (spn f) x)) (n (prec f)))))))

(defthmd drnd-tiny-9
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (> x (/ (spd f) 2))
                (< x (spd f)))
           (> (abs (- (+ (spn f) x) (rtz (+ (spn f) x) (prec f))))
              (abs (- (+ (spn f) x) (raz (+ (spn f) x) (prec f))))))
  :hints (("Goal" :use (drnd-tiny-5 drnd-tiny-6))))

(defthmd drnd-tiny-10
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x)
                (> x (/ (spd f) 2))
                (< x (spd f)))
           (and (equal (rne (+ (spn f) x) (prec f)) (raz (+ (spn f) x) (prec f)))
                (equal (rna (+ (spn f) x) (prec f)) (raz (+ (spn f) x) (prec f)))))
  :hints (("Goal" :use (drnd-tiny-9                        (:instance rne-raz (x (+ (spn f) x)) (n (prec f)))
                        (:instance rna-raz (x (+ (spn f) x)) (n (prec f)))))))

(defthmd drnd-tiny-11
  (implies (formatp f)
           (equal (sig (+ (spn f) (/ (spd f) 2)))
                  (1+ (expt 2 (- (prec f))))))
  :hints (("Goal" :in-theory (enable formatp expw bias prec spn spd)
                   :use ((:instance fp-rep-unique (x (+ (spn f) (/ (spd f) 2))) (m (1+ (expt 2 (- (prec f))))) (e (- 2 (expt 2 (1- (expw f))))))))))

(defthmd drnd-tiny-12
  (implies (formatp f)
           (exactp (+ (spn f) (/ (spd f) 2)) (1+ (prec f))))
  :hints (("Goal" :in-theory (e/d (formatp expw bias prec exactp) (exactp-rewrite))
                  :use (drnd-tiny-11))))

(defthmd drnd-tiny-13
  (implies (formatp f)
           (not (exactp (+ (spn f) (/ (spd f) 2)) (prec f))))
  :hints (("Goal" :in-theory (e/d (formatp expw bias prec exactp) (exactp-rewrite))
                  :use (drnd-tiny-11))))

(defthmd drnd-tiny-14
  (implies (formatp f)
           (not (exactp (+ (spn f) (spd f)) (1- (prec f)))))
  :hints (("Goal" :in-theory (e/d (formatp expw bias prec spn spd fp+ exactp-2**n)
                                  (exactp-rewrite))
                  :use (:instance fp+2 (x (spn f)) (n (1- (prec f))) (y (+ (spn f) (spd f)))))))

(defthmd drnd-tiny-15
  (implies (formatp f)
           (equal (rne (+ (spn f) (/ (spd f) 2)) (prec f))
                  (rtz (+ (spn f) (/ (spd f) 2)) (prec f))))
  :hints (("Goal" :in-theory (enable formatp expw bias prec)
                   :use (drnd-tiny-12 drnd-tiny-13 drnd-tiny-14
                         (:instance drnd-tiny-6 (x (/ (spd f) 2)))
                         (:instance rne-choice (x (+ (spn f) (/ (spd f) 2))) (n (prec f)))
                         (:instance rne-midpoint (x (+ (spn f) (/ (spd f) 2))) (n (prec f)))))))

(defthmd drnd-tiny-16
  (implies (formatp f)
           (equal (rna (+ (spn f) (/ (spd f) 2)) (prec f))
                  (raz (+ (spn f) (/ (spd f) 2)) (prec f))))
  :hints (("Goal" :in-theory (enable formatp expw bias prec)
                   :use (drnd-tiny-12 drnd-tiny-13
                         (:instance drnd-tiny-6 (x (/ (spd f) 2)))
                         (:instance rna-midpoint (x (+ (spn f) (/ (spd f) 2))) (n (prec f)))))))

(defthmd drnd-tiny-b
  (implies (and (formatp f)
                (common-mode-p mode))
           (equal (drnd (/ (spd f) 2) mode f)
                  (if (member mode '(raz rup rna))
                      (spd f)
                     0)))
  :hints (("Goal" :in-theory (e/d (formatp expw bias prec rnd common-mode-p ieee-rounding-mode-p spn spd drnd-tiny-3)
                                  (rnd-rewrite))
                  :use (drnd-tiny-15 drnd-tiny-16
                         (:instance drnd-tiny-5 (x (/ (spd f) 2)))
                         (:instance drnd-tiny-6 (x (/ (spd f) 2)))))))

(defthmd drnd-tiny-c
  (implies (and (formatp f)
                (common-mode-p mode)
                (rationalp x)
                (< (/ (spd f) 2) x)
                (< x (spd f)))
           (equal (drnd x mode f)
                  (if (member mode '(rtz rdn))
                      0
                    (spd f))))
  :hints (("Goal" :in-theory (e/d (formatp expw bias prec rnd common-mode-p ieee-rounding-mode-p spn spd drnd-tiny-3)
                                  (rnd-rewrite))
                  :use (drnd-tiny-5 drnd-tiny-6 drnd-tiny-10))))

