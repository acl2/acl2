; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory")
(local (in-theory nil))

(include-book "defs")

;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************

(defsection-rtl |Truncation| |Rounding|

(defund rtz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
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
		       (expt 2 (- (1+ (expo x)) n))))))

(defthm rtz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (rtz x n)))
  :rule-classes :type-prescription)

(defthm rtz-neg-bits
    (implies (and (integerp n)
		  (<= n 0))
	     (equal (rtz x n) 0)))

(defthmd sgn-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (sgn (rtz x n))
		    (sgn x))))

(defthm rtz-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n)))
            (< 0 (rtz x n)))
   :rule-classes (:rewrite :linear))

(defthm rtz-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (rtz x n) 0))
  :rule-classes (:rewrite :linear))

(defthm rtz-0
  (equal (rtz 0 n) 0))

(defthmd abs-rtz
  (equal (abs (rtz x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))

(defthmd rtz-minus
  (equal (rtz (- x) n) (- (rtz x n))))

(defthmd rtz-shift
  (implies (integerp n)
           (equal (rtz (* x (expt 2 k)) n)
                  (* (rtz x n) (expt 2 k)))))

(defthmd rtz-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (rtz x n)) (abs x)))
  :rule-classes :linear)

(defthmd rtz-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (rtz x n) x))
  :rule-classes :linear)

(defthm expo-rtz
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (rtz x n))
                    (expo x))))

(defthmd rtz-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (rtz x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)

(defthm rtz-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (abs (- x (rtz x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm rtz-exactp-a
  (exactp (rtz x n) n))

(defthmd rtz-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rtz x n)))))

(defthm rtz-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (rtz x n)))
  :rule-classes ())

(defthmd rtz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n)))
           (equal (rtz x n) a)))

(defthmd rtz-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (rtz x n) (rtz y n)))
  :rule-classes :linear)

(defthmd rtz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rtz x n)
                    (- x (expt 2 (- (expo x) n))))))

(defthm rtz-rtz
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (rtz (rtz x n) m)
		    (rtz x m))))

(defthm plus-rtz
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (rtz y k))
		(rtz (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())

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
  :rule-classes ())

(defthmd bits-rtz
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (equal (rtz x k)
                  (* (expt 2 (- n k))
                     (bits x (1- n) (- n k))))))

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
                  (bits x i j))))

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
                        (bits x (1- (- n k)) (- n m)))))))

(defthmd rtz-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (equal (rtz x k)
                  (logand x (- (expt 2 m) (expt 2 (- n k)))))))
)

;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************

(defsection-rtl |Rounding Away from Zero| |Rounding|

(defund raz (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
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
		       (expt 2 (- (1+ (expo x)) n))))))

(defthmd abs-raz
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (raz x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))

(defthm raz-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n)))
           (integerp (raz x n)))
  :rule-classes :type-prescription)

(defthmd sgn-raz
  (equal (sgn (raz x n))
         (sgn x)))

(defthm raz-positive
  (implies (and (< 0 x)
                (case-split (rationalp x)))
           (< 0 (raz x n)))
  :rule-classes (:rewrite :linear))

(defthm raz-negative
    (implies (and (< x 0)
                  (case-split (rationalp x)))
	     (< (raz x n) 0))
    :rule-classes (:rewrite :linear))

(defthm raz-0
  (equal (raz 0 n) 0))

(defthmd raz-minus
  (equal (raz (- x) n) (- (raz x n))))

(defthm raz-shift
    (implies (integerp n)
	     (= (raz (* x (expt 2 k)) n)
		(* (raz x n) (expt 2 k))))
  :rule-classes ())

(defthm raz-neg-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n))
           (equal (raz x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n)))))))

(defthmd raz-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (raz x n)) (abs x)))
  :rule-classes :linear)

(defthmd raz-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (raz x n) x))
  :rule-classes :linear)

(defthmd raz-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (raz x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)

(defthmd raz-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (raz x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear)

(defthm raz-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (raz x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthmd expo-raz-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (raz x n)) (1+ (expo x))))
  :rule-classes :linear)

(defthmd expo-raz-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (raz x n)) (expo x)))
  :rule-classes :linear)

(defthmd expo-raz
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (raz x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (raz x n))
                    (expo x))))

(defthm raz-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (raz x n) n)))

(defthmd raz-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (raz x n)))))

(defthm raz-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (raz x n)))
  :rule-classes ())

(defthmd raz-squeeze
  (implies (and (rationalp x)
                (rationalp a)
                (> x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (<= x (fp+ a n)))
           (equal (raz x n) (fp+ a n))))

(defthmd raz-up
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (raz x n)) (expt 2 k)))
           (equal (abs (raz x m)) (expt 2 k))))

(defthmd raz-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (raz x n) (raz y n)))
  :rule-classes :linear)

(defthmd rtz-raz
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (equal (raz x n)
	            (+ (rtz x n)
		       (expt 2 (+ (expo x) 1 (- n)))))))

(defthmd raz-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (raz x n)
		    (+ x (expt 2 (- (expo x) n))))))

(defthmd raz-raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (raz (raz x n) m)
		    (raz x m))))

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
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

(defthmd raz-impl
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
		         n))))
)

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defsection-rtl |Unbiased Rounding| |Rounding|

(defun re (x)
  (declare (xargs :guard (real/rationalp x)))
  (- x (fl x)))

(defund rne (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
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
  :rule-classes ())

(defthmd sgn-rne
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rne x n))
		    (sgn x))))

(defthm rne-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (rne x n)))
  :rule-classes (:type-prescription :linear))

(defthmd rne-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n))
           (< (rne x n) 0))
  :rule-classes (:type-prescription :linear))

(defthm rne-0
  (equal (rne 0 n) 0))

(defthm rne-exactp-a
    (implies (< 0 n)
	     (exactp (rne x n) n)))

(defthmd rne-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rne x n)))))

(defthm rne-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (rne x n)))
  :rule-classes ())

(defthm rne-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rne x n)))
  :rule-classes ())

(defthm expo-rne
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (rne x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rne x n))
                    (expo x))))

(defthm rne<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (raz x n)))
  :rule-classes ())

(defthm rne>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rne x n) (rtz x n)))
  :rule-classes ())

(defthm rne-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (rne (* x (expt 2 k)) n)
		(* (rne x n) (expt 2 k))))
  :rule-classes ())

(defthmd rne-minus
  (equal (rne (- x) n) (- (rne x n))))

(defthmd rne-rtz
    (implies (and (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (rne x n)
                    (rtz x n))))

(defthmd rne-raz
  (implies (and (> (abs (- x (rtz x n)))
                   (abs (- (raz x n) x)))
                (rationalp x)
                (integerp n))
           (equal (rne x n)
                  (raz x n))))

(defthmd rne-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) a)))

(defthmd rne-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rne x n) (fp+ a n))))

(defthmd rne-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rne x n)) (expt 2 k)))
           (equal (abs (rne x m)) (expt 2 k))))

(defthm rne-nearest
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rne x n)))))
  :rule-classes ())

(defthm rne-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())

(defthm rne-diff-cor
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rne x n)))
		 (* (abs x) (expt 2 (- n)))))
  :rule-classes ())

(defthm rne-force
    (implies (and (integerp n)
		  (> n 0)
                  (rationalp x)
                  (not (= x 0))
		  (rationalp y)
                  (exactp y n)
		  (< (abs (- x y)) (expt 2 (- (expo x) n))))
	     (= y (rne x n)))
  :rule-classes ())

(defthm rne-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (<= (rne x n) (rne y n)))
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

(defthm rne-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (rne x n) (1- n)))
    :rule-classes ())

(defund xfp (k m x0)
  (+ x0 (* (expt 2 (- (1+ (expo x0)) m)) k)))

(defund err-rne (k m n x0)
  (- (rne (xfp k m x0) n) (xfp k m x0)))

(defund sum-err-rne (i j m n x0)
  (declare (xargs :measure (nfix (1+ (- j i)))))
  (if (and (natp i) (natp j) (<= i j))
      (+ (sum-err-rne i (1- j) m n x0)
         (err-rne j m n x0))
    0))

(defthmd rne-unbiased
  (implies (and (natp m)
                (natp n)
                (< 1 n)
                (< n m)
                (rationalp x0)
                (> x0 0)
                (exactp x0 (1- n)))
           (equal (sum-err-rne 0 (1- (expt 2 (- (1+ m) n))) m n x0)
	          0)))

(defund rna (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(defthm rna-choice
    (or (= (rna x n) (rtz x n))
	(= (rna x n) (raz x n)))
  :rule-classes ())

(defthm sgn-rna
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rna x n))
		    (sgn x))))

(defthm rna-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (rna x n) 0))
  :rule-classes :linear)

(defthm rna-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (rna x n) 0))
  :rule-classes :linear)

(defthm rna-0
  (equal (rna 0 n) 0))

(defthm rna-exactp-a
    (implies (> n 0)
	     (exactp (rna x n) n)))

(defthmd rna-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rna x n)))))

(defthm rna-exactp-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rna x n)))
  :rule-classes ())

(defthm rna-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rna x n)))
  :rule-classes ())

(defthmd expo-rna
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (rna x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (rna x n))
                    (expo x))))

(defthm rna<=raz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (rna x n) (raz x n)))
  :rule-classes ())

(defthm rna>=rtz
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (rna x n) (rtz x n)))
  :rule-classes ())

(defthm rna-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (rna (* x (expt 2 k)) n)
		(* (rna x n) (expt 2 k))))
  :rule-classes ())

(defthmd rna-minus
  (equal (rna (- x) n) (- (rna x n))))

(defthmd rna-rtz
    (implies (and (rationalp x)
		  (integerp n)
		  (< (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (rtz x n))))

(defthmd rna-raz
    (implies (and (rationalp x)
		  (integerp n)
		  (> (abs (- x (rtz x n)))
                     (abs (- (raz x n) x))))
	     (equal (rna x n) (raz x n))))

(defthmd rna-down
  (implies (and (rationalp x)
                (rationalp a)
                (>= x a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna x n) a))
  :hints (("Goal" :use (near+-down))))

(defthmd rna-up
  (implies (and (rationalp x)
                (rationalp a)
                (> a 0)
                (not (zp n))
                (exactp a n)
                (< x (fp+ a n))
                (> x (+ a (expt 2 (- (expo a) n)))))
           (equal (rna x n) (fp+ a n))))

(defthmd rna-up-2
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (= (abs (rna x n)) (expt 2 k)))
           (equal (abs (rna x m)) (expt 2 k))))

(defthm rna-nearest
    (implies (and (exactp y n)
                  (rationalp x)
                  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (rna x n)))))
  :rule-classes ())

(defthm rna-force
    (implies (and (integerp n)
		  (> n 0)
                  (rationalp x)
                  (not (= x 0))
		  (rationalp y)
                  (exactp y n)
		  (< (abs (- x y)) (expt 2 (- (expo x) n))))
	     (= y (rna x n)))
  :rule-classes ())

(defthm rna-diff
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (rna x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())

(defthm rna-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rna x n) (rna y n)))
  :rule-classes ())

(defund rna-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (rna x n) (rna y n)) 2)
    (expt 2 (expo y))))

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
  :rule-classes ())

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
  :rule-classes ())

(defthmd rna-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (rna x n) (raz x n))))

(defthm rne-pow-2
  (implies (and (rationalp x) (> x 0)
                (not (zp n))
	        (>= (+ x (expt 2 (- (expo x) n)))
	            (expt 2 (1+ (expo x)))))
	   (= (rne x n)
	      (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm rtz-pow-2
  (implies (and (rationalp x) (> x 0)
                (not (zp n))
	        (>= (+ x (expt 2 (- (expo x) n)))
	            (expt 2 (1+ (expo x)))))
	   (= (rtz (+ x (expt 2 (- (expo x) n))) n)
	      (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm rna-pow-2
  (implies (and (rationalp x) (> x 0)
                (not (zp n))
	        (>= (+ x (expt 2 (- (expo x) n)))
	            (expt 2 (1+ (expo x)))))
	   (= (rna x n)
	      (expt 2 (1+ (expo x)))))
  :rule-classes ())

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
  :rule-classes ())

(defthmd rne-impl
    (implies (and (rationalp x) (> x 0)
		  (not (zp n)))
	     (equal (rne x n)
		    (if (and (> n 1) (exactp x (1+ n)) (not (exactp x n)))
		        (rtz (+ x (expt 2 (- (expo x) n))) (1- n))
		      (rtz (+ x (expt 2 (- (expo x) n))) n)))))

(defthmd rna-impl
    (implies (and (rationalp x) (> x 0)
		  (not (zp n)))
	     (equal (rna x n)
		    (rtz (+ x (expt 2 (- (expo x) n))) n))))

(defthmd rna-imp-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (equal (rna (rtz x n) m)
                    (rna x m))))
)

;;;**********************************************************************
;;;                          Odd Rounding
;;;**********************************************************************

(defsection-rtl |Odd Rounding| |Rounding|

(defund rto (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defthm sgn-rto
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rto x n))
		    (sgn x))))

(defthmd rto-positive
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (rto x n) 0))
  :rule-classes :linear)

(defthmd rto-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (rto x n) 0))
  :rule-classes :linear)

(defthm rto-0
  (equal (rto 0 n) 0))

(defthmd rto-minus
  (equal (rto (- x) n) (- (rto x n))))

(defthm rto-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (rto (* (expt 2 k) x) n)
		(* (expt 2 k) (rto x n))))
    :rule-classes ())

(defund err-rto (k m n x0)
  (- (rto (xfp k m x0) n) (xfp k m x0)))

(defund sum-err-rto (i j m n x0)
  (declare (xargs :measure (nfix (1+ (- j i)))))
  (if (and (natp i) (natp j) (<= i j))
      (+ (sum-err-rto i (1- j) m n x0)
         (err-rto j m n x0))
    0))

(defthm rto-unbiased
  (implies (and (natp m)
                (natp n)
                (< 1 n)
                (< n m)
                (rationalp x0)
                (> x0 0)
                (exactp x0 (1- n)))
           (equal (sum-err-rto 0 (1- (expt 2 (- (1+ m) n))) m n x0)
                  0)))

(defthm expo-rto
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 0))
	     (equal (expo (rto x n))
		    (expo x))))

(defthm rto-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (rto x n) n)))

(defthmd rto-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (exactp x n)
                  (= x (rto x n)))))

(defthmd rto-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (rto x n) (rto y n)))
  :rule-classes :linear)

(defthm rto-exactp-c
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (rto x n) m)
		  (exactp x m))))

(defthm rtz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (rtz (rto x n) m)
		    (rtz x m))))

(defthm raz-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (equal (raz (rto x n) m)
		    (raz x m))))

(defthm rne-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rne (rto x n) m)
		    (rne x m))))

(defthm rna-rto
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (equal (rna (rto x n) m)
		    (rna x m))))

(defthm rto-rto
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (equal (rto (rto x n) m)
		    (rto x m))))

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
  :rule-classes ())
)

;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************

(defsection-rtl |IEEE Rounding| |Rounding|

(defun rup (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defun rdn (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp n))))
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defthmd rup-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (rup x n) x))
  :rule-classes :linear)

(defthmd rdn-upper-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (rdn x n) x))
  :rule-classes :linear)

(defnd IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defnd common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defthm ieee-mode-is-common-mode
  (implies (IEEE-rounding-mode-p mode)
           (common-mode-p mode)))

(defund rnd (x mode n)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(defthm rationalp-rnd
  (rationalp (rnd x mode n))
  :rule-classes (:type-prescription))

(defthm rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode))
           (or (= (rnd x mode n) (rtz x n))
	       (= (rnd x mode n) (raz x n))))
  :rule-classes ())

(defthmd sgn-rnd
    (implies (and (common-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd x mode n))
		    (sgn x))))

(defthm rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-mode-p mode))
           (> (rnd x mode n) 0))
  :rule-classes (:type-prescription))

(defthm rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (< (rnd x mode n) 0))
  :rule-classes (:type-prescription))

(defthm rnd-0
  (equal (rnd 0 mode n) 0))

(defthm rnd-non-pos
    (implies (<= x 0)
	     (<= (rnd x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear))

(defthm rnd-non-neg
    (implies (<= 0 x)
	     (<= 0 (rnd x mode n)))
  :rule-classes (:rewrite :type-prescription :linear))

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
         (- (rnd x (flip-mode mode) n))))

(defthm rnd-exactp-a
    (implies (< 0 n)
	     (exactp (rnd x mode n) n)))

(defthmd rnd-exactp-b
  (implies (and (rationalp x)
                (common-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (exactp x n)
                  (equal x (rnd x mode n)))))

(defthm rnd-exactp-c
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rnd x mode n)))
  :rule-classes ())

(defthm rnd-exactp-d
    (implies (and (rationalp x)
		  (common-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rnd x mode n)))
  :rule-classes ())

(defthm rnd<=raz
    (implies (and (rationalp x)
		  (>= x 0)
		  (common-mode-p mode)
		  (natp n))
	     (<= (rnd x mode n) (raz x n)))
  :rule-classes ())

(defthm rnd>=rtz
    (implies (and (rationalp x)
		  (> x 0) ;;
		  (common-mode-p mode)
                  (integerp n)
                  (> n 0))
	     (>= (rnd x mode n) (rtz x n)))
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

(defthmd expo-rnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (equal (expo (rnd x mode n))
		    (expo x))))

(defthm rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-mode-p mode)
                  (integerp n)
                  (> n 0))
	     (<= (rnd x mode n) (rnd y mode n)))
  :rule-classes ())

(defthm rnd-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (common-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ())

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
  :rule-classes ())

(defthmd rnd-rto
  (implies (and (common-mode-p mode)
                (rationalp x)
                (integerp m)
		(> m 0)
                (integerp n)
		(>= n (+ m 2)))
           (equal (rnd (rto x n) mode m)
                  (rnd x mode m))))

(defthmd rnd-up
  (implies (and (rationalp x)
                (integerp k)
                (not (zp n))
                (not (zp m))
                (< m n)
                (< (abs x) (expt 2 k))
                (common-mode-p mode)
                (= (abs (rnd x mode n)) (expt 2 k)))
           (equal (abs (rnd x mode m)) (expt 2 k))))

(defun rnd-const (e mode n)
  (declare (xargs :guard (and (integerp e)
                              (common-mode-p mode)
                              (integerp n))))
  (case mode
    ((rne rna) (expt 2 (- e n)))
    ((rup raz) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))

(defthmd rnd-const-lemma
    (implies (and (common-mode-p mode)
		  (not (zp n))
		  (not (zp x))
		  (implies (or (= mode 'raz) (= mode 'rup))
		           (>= (expo x) (1- n))))
	     (equal (rnd x mode n)
		    (if (and (eql mode 'rne)
		             (> n 1)
			     (exactp x (1+ n))
                             (not (exactp x n)))
                        (rtz (+ x (rnd-const (expo x) mode n)) (1- n))
                      (rtz (+ x (rnd-const (expo x) mode n)) n)))))

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

(defthmd rnd-const-cor-a
  (implies (and (common-mode-p mode)
                (posp n)
                (posp m)
		(> (expo m) n))
	   (let* ((e (expo m))
	          (sum (+ m (rnd-const e mode n)))
		  (sh (bits sum (1+ e) (1+ (- e n))))
		  (sl (bits sum (- e n) 0)))
             (equal (rnd m mode n)
	            (if (and (= mode 'rne) (= sl 0))
		        (* (expt 2 (+ 2 (- e n))) (bits sh n 1))
		      (* (expt 2 (1+ (- e n))) sh))))))

(defthmd rnd-const-cor-b
  (implies (and (common-mode-p mode)
                (posp n)
                (posp m)
		(> (expo m) n))
	   (let* ((e (expo m))
                  (c (rnd-const e mode n))
	          (sum (+ m c))
		  (sl (bits sum (- e n) 0)))
             (iff (= m (rnd m mode n))
	          (= sl c)))))

(defthmd roundup-pos-thm-1
  (implies (and (rationalp z)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z)))
             (iff (exactp z n)
                  (and (integerp z) (= (bits x (- (expo x) n) 0) 0))))))

(defthmd roundup-pos-thm-2
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z))
                 (sticky (if (integerp z) 0 1)))
             (equal (rnd z mode n)
                    (if (roundup-pos x (expo x) sticky mode n)
                        (fp+ (rtz x n) n)
                      (rtz x n))))))

(defthmd roundup-pos-thm
  (implies (and (common-mode-p mode)
                (rationalp z)
                (not (zp n))
                (<= (expt 2 n) z))
           (let ((x (fl z))
                 (sticky (if (integerp z) 0 1)))
             (and (iff (exactp z n)
                       (and (integerp z) (= (bits x (- (expo x) n) 0) 0)))
	          (equal (rnd z mode n)
                         (if (roundup-pos x (expo x) sticky mode n)
                             (fp+ (rtz x n) n)
                           (rtz x n)))))))

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
  :rule-classes ())
)
;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************

(defsection-rtl |Denormal Rounding| |Rounding|

(defund drnd (x mode f)
  (declare (xargs :guard (and (real/rationalp x)
                              (common-mode-p mode)
                              (formatp f))))
  (rnd x mode (+ (prec f) (expo x) (- (expo (spn f))))))

(defthmd drnd-minus
  (equal (drnd (- x) mode f)
         (- (drnd x (flip-mode mode) f))))

(defthmd drnd-pos
  (implies (and (formatp f)
                (rationalp x)
                (>= x 0)
	        (<= x (spn f))
	        (common-mode-p mode))
	   (>= (drnd x mode f) 0)))

(defthmd drnd-rewrite
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (equal (drnd x mode f)
                  (- (rnd (+ x (* (sgn x) (spn f))) mode (prec f))
		     (* (sgn x) (spn f))))))

(defthm drnd-exactp-a
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (or (drepp (drnd x mode f) f)
               (= (drnd x mode f) 0)
               (= (drnd x mode f) (* (sgn x) (spn f)))))
  :rule-classes ())

(defthmd drnd-exactp-b
  (implies (and (formatp f)
                (rationalp x)
	        (drepp x f)
                (common-mode-p mode))
           (equal (drnd x mode f)
                  x)))

(defthmd drnd-exactp-c
  (implies (and (formatp f)
                (rationalp x)
                (<= (expo x) (- (bias f)))
                (>= (expo x) (+ 2 (- (bias f)) (- (prec f))))
                (common-mode-p mode))
           (iff (equal x (drnd x mode f))
                (exactp x (+ (1- (prec f)) (bias f) (expo x))))))

(defthm drnd-exactp-d
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
		(rationalp a)
                (drepp a f)
		(>= a x)
                (common-mode-p mode))
           (>= a (drnd x mode f)))
  :rule-classes ())

(defthm drnd-exactp-e
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
		(rationalp a)
                (drepp a f)
		(<= a x)
                (common-mode-p mode))
           (<= a (drnd x mode f)))
  :rule-classes ())

(defthm drnd-rtz
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (<= (abs (drnd x 'rtz f))
               (abs x)))
  :rule-classes ())

(defthm drnd-raz
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (>= (abs (drnd x 'raz f))
               (abs x)))
  :rule-classes ())

(defthm drnd-rdn
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (<= (drnd x 'rdn f)
               x))
  :rule-classes ())

(defthm drnd-rup
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f)))
           (>= (drnd x 'rup f)
               x))
  :rule-classes ())

(defthm drnd-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (< (abs (- x (drnd x mode f))) (spd f)))
  :rule-classes ())

(defthm drnd-rne-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (drepp a f))
           (>= (abs (- x a)) (abs (- x (drnd x 'rne f)))))
  :rule-classes ())

(defthm drnd-rna-diff
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (drepp a f))
           (>= (abs (- x a)) (abs (- x (drnd x 'rna f)))))
  :rule-classes ())

(defthmd drnd-rto
    (implies (and (formatp f)
                  (common-mode-p mode)
		  (rationalp x)
                  (<= (abs x) (spn f))
		  (natp n)
		  (>= n (+ (prec f) (expo x) (- (expo (spn f))) 2)))
	     (equal (drnd (rto x n) mode f)
		    (drnd x mode f))))

(defthmd rnd-drnd-exactp
  (implies (and (formatp f)
                (rationalp x)
                (< (abs x) (spn f))
                (common-mode-p mode)
                (= (drnd x mode f) x))
           (equal (rnd x mode (prec f)) x)))

(defthmd drnd-tiny-a
  (implies (and (formatp f)
                (common-mode-p mode)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd f) 2)))
           (equal (drnd x mode f)
                  (if (member mode '(raz rup))
                      (spd f)
                     0))))

(defthmd drnd-tiny-b
  (implies (and (formatp f)
                (common-mode-p mode))
           (equal (drnd (/ (spd f) 2) mode f)
                  (if (member mode '(raz rup rna))
                      (spd f)
                     0))))

(defthmd drnd-tiny-c
  (implies (and (formatp f)
                (common-mode-p mode)
                (rationalp x)
                (< (/ (spd f) 2) x)
                (< x (spd f)))
           (equal (drnd x mode f)
                  (if (member mode '(rtz rdn))
                      0
                    (spd f)))))

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
    :rule-classes ())

;;;**********************************************************************
;;;                         Detecting Underflow
;;;**********************************************************************

(defthmd rnd-drnd
  (implies (and (formatp f)
                (> (prec f) 2)
		(rationalp m)
		(< 0 m)
		(< m 1)
		(common-mode-p mode))
	   (let* ((x (* (spn f) m))
		  (p (prec f))
		  (r (rnd x mode p))
		  (d (drnd x mode f)))
	     (case mode
	       ((rdn rtz) (and (< r (spn f)) (< d (spn f))))
	       ((rup raz) (and (iff (< r (spn f)) (<= m (- 1 (expt 2 (- p)))))
	                       (iff (< d (spn f)) (<= m (- 1 (expt 2 (- 1 p)))))))
	       ((rne rna) (and (iff (< r (spn f)) (< m (- 1 (expt 2 (- (1+ p))))))
	                       (iff (< d (spn f)) (< m (- 1 (expt 2 (- p)))))))))))

(defthmd rnd-drnd-up
  (implies (and (formatp f)
                (rationalp x)
                (< (abs x) (spn f))
                (common-mode-p mode)
                (= (abs (rnd x mode (prec f))) (spn f)))
           (equal (abs (drnd x mode f)) (spn f))))

)
