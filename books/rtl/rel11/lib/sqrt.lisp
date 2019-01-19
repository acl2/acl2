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

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;;**********************************************************************
;;;		    	      RTZ-SQRT
;;;**********************************************************************

(defsection-rtl |Truncated Square Root| |IEEE-Compliant Square Root|

(defund rtz-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (natp n))))
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defthm rtz-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (rtz-sqrt x n))
                (<= (rtz-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ())


(defthm expo-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (rtz-sqrt x n))
                  -1)))

(defthm exactp-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (rtz-sqrt x n)
                   n))
  :rule-classes ())

(defthm rtz-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (and (<= (* (rtz-sqrt x n)
                       (rtz-sqrt x n))
                    x)
                (< x
                   (* (+ (rtz-sqrt x n) (expt 2 (- n)))
                      (+ (rtz-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ())

(defthm rtz-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (rtz-sqrt x n)))
  :rule-classes ())

(defthmd rtz-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m))))
)

;;;**********************************************************************
;;;		    	    RTO-SQRT
;;;**********************************************************************

(defsection-rtl |Odd-Rounded Square Root| |IEEE-Compliant Square Root|

(defund rto-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))))
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(defthm rto-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (rto-sqrt x n))
                (< (rto-sqrt x n) 1)))
  :rule-classes ())

(defthm expo-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (rto-sqrt x n))
                  -1)))

(defthmd exactp-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (rto-sqrt x n) n)))

(defthmd rto-rto-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rto (rto-sqrt x m) n)
                  (rto-sqrt x n))))

(defthm rnd-rto-sqrt
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rnd (rto-sqrt x m) mode k)
              (rnd (rto-sqrt x n) mode k)))
  :rule-classes ())

(defthmd rtz-rto-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rtz (rto-sqrt x m) n)
                  (rtz-sqrt x n))))

(defthm rtz-rtz-rto
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (iff (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x)
                (= (rto-sqrt x m) (rtz-sqrt x n))))
  :rule-classes ())

(defthm rto-sqrt-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ())

(defthm rto-sqrt-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (rto h n)
               (rto-sqrt x n)))
  :rule-classes ())

(defthm exactp-cmp-rto-sqrt
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (rto-sqrt x n)))
                (iff (> (* q q) x) (> q (rto-sqrt x n)))))
  :rule-classes ())
)

;;;**********************************************************************
;;;		    	       QSQRT
;;;**********************************************************************

(defsection-rtl |IEEE-Rounded Square Root| |IEEE-Compliant Square Root|

(defund qsqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))))
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))

(defthm qsqrt-expo
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 xp)
                  (< xp 1))))
  :rule-classes ())

(defthmd qsqrt-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt x n)
                  (rto-sqrt x n))))

(defthmd qsqrt-pos
  (implies (and (rationalp x)
                (> x 0))
           (> (qsqrt x n) 0)))

(defthmd qsqrt-shift
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (integerp n)
                (> n 1))
           (equal (qsqrt (* (expt 2 (* 2 k)) x) n)
                  (* (expt 2 k) (qsqrt x n)))))

(defthm rnd-qsqrt-equal
  (implies (and (rationalp x)
                (> x 0)
                (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
		(common-mode-p mode))
           (equal (rnd (qsqrt x m) mode k)
	          (rnd (qsqrt x n) mode k)))
  :rule-classes ())

(defthm qsqrt-lower
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (rnd l mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ())

(defthm qsqrt-upper
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (rnd h mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ())

(defthm exactp-cmp-qsqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (qsqrt x n)))
                (iff (> (* q q) x) (> q (qsqrt x n)))
                (iff (= (* q q) x) (= q (qsqrt x n)))))
  :rule-classes ())

(defthmd qsqrt-sqrt
  (implies (and (rationalp x) (> x 0)
                (integerp n) (> n 1)
		(exactp (qsqrt x n) (1- n)))
	   (equal (* (qsqrt x n) (qsqrt x n))
	          x)))

(defthm qsqrt-exact-equal
  (implies (and (rationalp x)
                (> x 0)
                (not (zp k))
                (natp n)
                (> n k)
                (natp m)
		(> m k)
		(exactp (qsqrt x n) k))
	   (equal (qsqrt x n) (qsqrt x m)))
  :rule-classes ())

)
