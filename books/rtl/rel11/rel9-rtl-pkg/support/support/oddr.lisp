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

(in-package "RTL")

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(local (include-book "oddr-proofs"))

;; Necessary functions:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defnd expo (x)
  (declare (xargs :measure (expo-measure x)
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

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

;make defund?
(defun sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0)
        -1
      1)))

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund re (x)
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

;;
;; New stuff:
;;

(defund oddr (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x)))))
    (if (evenp z)
	(* (sgn x) (1+ z) (expt 2 (- (1+ (expo x)) n)))
      (* (sgn x) z (expt 2 (- (1+ (expo x)) n))))))

(defthm oddr-pos
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< 0 (oddr x n)))
  :rule-classes ())

(defthm oddr>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (oddr x n) (trunc x n)))
  :rule-classes ())

;BOZO just opens up ODDR when x is positive
;leave disabled!
(defthmd oddr-rewrite
    (implies (and (< 0 x) ;note this hyp
                  (rationalp x)
		  (integerp n)
		  (< 0 n))
	     (equal (oddr x n)
		    (let ((z (fl (* (expt 2 (- (1- n) (expo x))) x))))
		      (if (evenp z)
			  (* (1+ z) (expt 2 (- (1+ (expo x)) n)))
			(* z (expt 2 (- (1+ (expo x)) n))))))))

;move!
(defthm fl/2
  (implies (integerp z)
           (= (fl (/ z 2))
              (if (evenp z)
                  (/ z 2)
                (/ (1- z) 2))))
  :rule-classes ())

(defthm oddr-other
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (oddr x n)
		(+ (trunc x (1- n))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ())

(defthm expo-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (equal (expo (oddr x n)) (expo x))))

(defthm exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (exactp (oddr x n) n))
	     :rule-classes ())


(defthm not-exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (not (exactp (oddr x n) (1- n))))
	     :rule-classes ())

(defthm trunc-oddr
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (> n m))
	     (= (trunc (oddr x n) m)
		(trunc x m)))
  :rule-classes ())

;disable?
(defun kp (k x y)
  (+ k (- (expo (+ x y)) (expo y))))

(defthm oddr-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (> x 0)
		  (> y 0)
		  (> k 1)
		  (> (+ (1- k) (- (expo x) (expo y))) 0)
		  (exactp x (+ (1- k) (- (expo x) (expo y)))))
	     (= (+ x (oddr y k))
		(oddr (+ x y) (kp k x y))))
  :rule-classes ())

(defthm trunc-trunc-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (trunc x k) (trunc (oddr y m) k)))
  :rule-classes ())

(defthm away-away-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (away x k) (away (oddr y m) k)))
  :rule-classes ())

(defthm near-near-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (near x k) (near (oddr y m) k)))
  :rule-classes ())

