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

(local (include-book "near-proofs"))

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

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

;;
;; New stuff:
;;

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

(defthm near-minus
  (equal (near (* -1 x) n)
         (* -1 (near x n))))

(defthm near-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (near x n)
                  0))
  :hints (("goal" :in-theory (enable near sig))))

(defthm near-0
  (equal (near 0 n)
         0))

(defthm near-rational-type-prescription
  (rationalp (near x n))
  :rule-classes (:rewrite :type-prescription))


(defthm near-non-negative-rational-type-prescription
  (implies (<= 0 x)
           (and (<= 0 (near x n))
                (rationalp (near x n))))
  :rule-classes :type-prescription)

(defthm near-non-positive-rational-type-prescription
  (implies (<= x 0)
           (and (<= (near x n) 0)
                (rationalp (near x n))))
  :rule-classes :type-prescription)

(defthm near-pos
  (implies (and (< 0 x)
                (< 0 n)
                (rationalp x)
                (integerp n)
                )
           (< 0 (near x n)))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use ((:instance near-choice)))))

(defthm near-neg
    (implies (and (< x 0)
		  (< 0 n)
                  (rationalp x)
		  (integerp n)
		  )
	     (< (near x n) 0))
  :rule-classes (:type-prescription :linear)
  :hints (("Goal" :use ((:instance near-choice)))))



;; (defthm near1-a-support
;;   (implies (and (< (- x (trunc x n)) (- (away x n) x))
;;                 (rationalp x)
;;                 (>= x 0)
;;                 (integerp n)
;;                 )
;;            (equal (near x n)
;;                   (trunc x n)))
;;   :rule-classes ())

(defthm near1-a
  (implies (and (< (abs (- x (trunc x n)))
                   (abs (- (away x n) x)))
                (rationalp x)
                (integerp n))
           (equal (near x n)
                  (trunc x n)))
  :rule-classes ())


;; (defthm near1-b
;;   (implies (and (> (- x (trunc x n)) (- (away x n) x))
;;                 (rationalp x)
;;                 (>= x 0)
;;                 (integerp n)
;;                 (> n 0)
;;                 )
;;            (equal (near x n)
;;                   (away x n)))
;;   :rule-classes ())

(defthm near1-b
  (implies (and (> (abs (- x (trunc x n))) (abs (- (away x n) x)))
                (rationalp x)
                (integerp n))
           (equal (near x n)
                  (away x n)))
  :rule-classes ())

(defthm near2-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (>= x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near x n) (trunc x n)))
	     (>= (abs (- x y)) (- x (trunc x n))))
  :rule-classes ())

(defthm near2-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near x n) (away x n)))
	     (>= (abs (- x y)) (- (away x n) x)))
  :rule-classes ())

(defthm near-choice
  (or (= (near x n) (trunc x n))
      (= (near x n) (away x n)))
  :rule-classes ())

;; (defthm near2
;;   (implies (and (exactp y n)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (> x 0)
;;                 (> y 0)
;;                 (integerp n)
;;                 (> n 0)
;;                 )
;;            (>= (abs (- x y)) (abs (- x (near x n)))))
;;   :rule-classes ())

(defthm near2
  (implies (and (exactp y n)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (>= (abs (- x y)) (abs (- x (near x n)))))
  :rule-classes ())

(defthm near-exactp-a
  (implies (< 0 n)
           (exactp (near x n) n)))

(defthm sgn-near-2
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (equal (sgn (near x n))
                  (sgn x))))

(defthm near-exactp-b
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (iff (= x (near x n))
                (exactp x n)))
  :rule-classes ())


(defthmd near-exactp-c
      (implies (and (exactp a n)
  		  (>= a x)
                    (rationalp x)
  		  (integerp n)
  		  (> n 0)
  		  (rationalp a)
  		  )
  	     (>= a (near x n))))

;; (defthmd near-exactp-c-support
;;   (implies (and (exactp a n)
;;                 (>= a x)
;;                 (rationalp x)
;;                 (> x 0)
;;                 (integerp n)
;;                 (> n 0)
;;                 (rationalp a)
;;                 )
;;            (>= a (near x n))))

;; (defthm near-exactp-d-support
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (<= a x))
;; 	     (<= a (near x n))))

(defthmd near-exactp-d
      (implies (and (rationalp x)
  		  (integerp n)
  		  (> n 0)
  		  (rationalp a)
  		  (exactp a n)
  		  (<= a x))
  	     (<= a (near x n))))


(defthm near-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (<= (near x n) (near y n))))


(defund near-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (near x n) (near y n)) 2)
    (expt 2 (expo y))))

(defthm near<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (away x n)))
  :rule-classes ())

(defthm near>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (near x n) (trunc x n)))
  :rule-classes ())



(defthm near-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (equal (equal (near x n) 0)
		  (equal x 0)))
  :rule-classes ())

(defthm near-near-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near x n) (near y n))))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)
		  (exactp (near-witness x y n) (1+ n))))
  :rule-classes ())

;bad name?
(defthm near-near
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
           (<= (near y k) (near x k)))
  :rule-classes ())

;BOZO why disabled?
(defthmd near-shift
  (implies (and (rationalp x)
                (integerp n)
                (integerp k))
           (= (near (* x (expt 2 k)) n)
              (* (near x n) (expt 2 k)))))

(defthm near-a-a
  (implies (and (rationalp x) (> x 0)
                (rationalp a) (> a 0)
                (integerp n) (> n 0)
                (exactp a n)
                (> x (+ a (expt 2 (- (expo a) n)))))
           (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ())

(defthm near-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near x n) a))
  :rule-classes ())

(defthm near-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near x n) a))
  :rule-classes ())

;bad name?

(defthm near-exact
  (implies (and (rationalp x)
                (integerp n)
                (> n 1)
                (exactp x (1+ n))
                (not (exactp x n)))
           (exactp (near x n) (1- n)))
  :rule-classes ())

(defthm near-est
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())


(defthm near-power-a
  (implies (and (rationalp x) (> x 0)
                (integerp n) (> n 1)
                (>= (+ x (expt 2 (- (expo x) n)))
                    (expt 2 (1+ (expo x)))))
           (= (near x n)
              (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm near-power-b
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

;bad name?
(defthm near-exactp
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x n))
	     (equal (near x n) x))
  :rule-classes ())

(defthm near-trunc
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ())

;; ;BOZO yuck? bad name!
;; (defthm sgn-near
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (> n 0))
;;            (= (near x n)
;;               (* (sgn x) (near (abs x) n))))
;;   :rule-classes ())



(defthm plus-near-1
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                )
           (= (re (* (expt 2 (1- k)) (sig y)))
              (re (* (expt 2 (1- (+ k (- (expo (+ x y)) (expo y)))))
                     (sig (+ x y))))))
  :rule-classes nil)

(defthm plus-near-2
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (iff (evenp (fl (* (expt 2 (1- k)) (sig y))))
                (evenp (fl (* (expt 2
                                    (1- (+ k (- (expo (+ x y)) (expo y)))))
                              (sig (+ x y)))))))

  :rule-classes nil)

(defthm plus-near
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (= (+ x (near y k))
              (near (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes nil)



