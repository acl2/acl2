; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/top/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

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

;; From round.lisp:

(defund away (x n)
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))

(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(defund inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defund minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))


(defund IEEE-mode-p (mode)
  (member mode '(trunc inf minf near)))

(defund common-rounding-mode-p (mode)
  (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

(defund rnd (x mode n)
  (case mode
    (away (away x n))
    (near+ (near+ x n))
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))
    (otherwise 0)))


;;;**********************************************************************
;;;		    	      TRUNC-SQRT
;;;**********************************************************************

(defund trunc-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (trunc-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defthm trunc-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (trunc-sqrt x n))
                (<= (trunc-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ())


(defthm expo-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (trunc-sqrt x n))
                  -1)))

(defthm exactp-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (trunc-sqrt x n)
                   n))
  :rule-classes ())

(defthmd trunc-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (trunc (trunc-sqrt x n) m)
                  (trunc-sqrt x m))))

(defthm trunc-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (and (<= (* (trunc-sqrt x n)
                       (trunc-sqrt x n))
                    x)
                (< x
                   (* (+ (trunc-sqrt x n) (expt 2 (- n)))
                      (+ (trunc-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ())

(defthm trunc-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (trunc-sqrt x n)))
  :rule-classes ())


;;;**********************************************************************
;;;		    	    STICKY-SQRT
;;;**********************************************************************

(defund sticky-sqrt (x n)
  (let ((trunc (trunc-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(defthm sticky-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (sticky-sqrt x n))
                (< (sticky-sqrt x n) 1)))
  :rule-classes ())

(defthm expo-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (sticky-sqrt x n))
                  -1)))

(defthmd exactp-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (sticky-sqrt x n) n)))

(defthm sticky-sqrt-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ())

#|
Proof: Let a = trunc-sqrt(n-2, x) and r = sticky-sqrt(x, n).
Suppose a^2 = x.  Then r = a, l^2 <= x = a^2 = r^2, and l <= r.
By sticky-monotone, sticky-exactp-b, and exactp-trunc-sqrt,

  sticky(l, n) <= sticky(r, n) = r.

Thus, we may assume a^2 < x and r = a + 2^(1-n).  By trunc-sqrt-square-bounds,
l^2 <= x < (a + 2^(2-n))^2, and hence l < a + 2^(2-n) = fp+(a, n-1).
It follows from trunc-upper-pos, trunc-exactp-a, and fp+2 that
trunc(l, n-1) <= a.  Thus,

  sticky(l, n) <= trunc(l, n-1) + 2^(1+expo(l)-n)
               <= a + 2^(1-n)
                = r.
|#

(defthm sticky-sqrt-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (sticky h n)
               (sticky-sqrt x n)))
  :rule-classes ())

#|
Proof: Let a = trunc-sqrt(x, n-1) and r = sticky-sqrt(x, n).
We may assume that h < r; otherwise, by sticky-monotone,
sticky-exactp-b, and exactp-trunc-sqrt,

  sticky(h, n) >= sticky(r, n) = r.

If a^2 = x, then r = a, h^2 >= x = a^2 = r^2, and h >= r.
Thus, by trunc-sqrt-square-bounds, a^2 < x and r = a + 2^(1-n) = fp+(a, n).
Since h^2 >= x > a^2, h > a.  It follows from trunc-exactp-c that
trunc(h, n-1) >= a.  By fp+2, h is not n-exact, and hence

  sticky(h, n) = trunc(h, n-1) + 2^(1-n)
              >= a + 2^(1-n)
               = r.
|#

(defthmd sticky-sticky-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (sticky (sticky-sqrt x m) n)
                  (sticky-sqrt x n))))

(defthm rnd-sticky-sqrt
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-rounding-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rnd (sticky-sqrt x m) mode k)
              (rnd (sticky-sqrt x n) mode k)))
  :rule-classes ())

(defthmd trunc-sticky-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (trunc (sticky-sqrt x m) n)
                  (trunc-sqrt x n))))

(defthm trunc-trunc-sticky
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (iff (= (* (trunc-sqrt x n) (trunc-sqrt x n)) x)
                (= (sticky-sqrt x m) (trunc-sqrt x n))))
  :rule-classes ())

(defthm exactp-cmp-sticky-sqrt
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (sticky-sqrt x n)))
                (iff (> (* y y) x) (> y (sticky-sqrt x n)))))
  :rule-classes ())


;;;**********************************************************************
;;;		    	      QSQRT
;;;**********************************************************************

(defund qsqrt (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (sticky-sqrt (/ x (expt 2 (* 2 e))) n))))

(defthmd sqrt-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt x n)
                  (sticky-sqrt x n))))

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

(defthm exactp-cmp-qsqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (qsqrt x n)))
                (iff (> (* y y) x) (> y (qsqrt x n)))))
  :rule-classes ())

(defthm qsqrt-lower
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-rounding-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (rnd l mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ())

#|
Proof: Let e = fl(expo(x)/2), x0 = x/2^(2*e), and l0 = l/2^e.
Then 1 <= x0 < 4 and l0^2 = l^2/2^(2*e) <= x/2^(2*e) = x0.
By sticky-shift and sticky-sqrt-lower,

  sticky(l, 66) = 2^e * sticky(l0, n)
               <= 2^e * sticky-sqrt(x0, n)
                = sqrt(x, n).

By rnd-sticky and rnd-monotone,

  rnd(l, mode, k) = rnd(sticky(l, n), mode, k)
                 <= rnd(sqrt(x, n), mode, k)
|#

(defthm qsqrt-upper
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-rounding-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (rnd h mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ())

