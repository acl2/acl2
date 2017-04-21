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

;(include-book "near")
(local (include-book "../../arithmetic/top"))
(local (include-book "float"))
(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "near"))

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
  :rule-classes ()
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (oddr) ( SIG-LESS-THAN-1-MEANS-X-0 sig-lower-bound))
           :use ((:instance sig-lower-bound)))))

(defthm oddr>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (oddr x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable oddr)
		  :use ((:instance trunc)
                        ))))

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
			(* z (expt 2 (- (1+ (expo x)) n)))))))
  :hints (("Goal" :in-theory (enable sig sgn oddr expt-split))))

(local
 (defthm hack2
    (implies (and (integerp n)
		  (rationalp x))
	     (= (fl (* 1/2 x (expt 2 n)))
		(fl (* x (expt 2 (1- n))))))
    :hints (("Goal" :in-theory (enable expt)))
  :rule-classes ()))

(local
 (defthm oddr-other-1
    (implies (and (rationalp x)
		 (> x 0)
		 (integerp n)
		 (> n 1))
	     (= (trunc x (1- n))
		(* (fl (/ (* (expt 2 (- (1- n) (expo x))) x) 2))
		   (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-pos-rewrite)
		  :use ((:instance hack2 (n (- (1- n) (expo x)))))))))

(local
 (defthm oddr-other-2
    (implies (and (rationalp x)
		 (> x 0)
		 (integerp n)
		 (> n 1))
	     (= (trunc x (1- n))
		(* (fl (/ (fl (* (expt 2 (- (1- n) (expo x))) x)) 2))
		   (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl/int-rewrite)
		  :use ((:instance oddr-other-1)
			(:instance fl/int-rewrite (x (* (expt 2 (- (1- n) (expo x))) x)) (n 2)))))))

;move!
(defthm fl/2
  (implies (integerp z)
           (= (fl (/ z 2))
              (if (evenp z)
                  (/ z 2)
                (/ (1- z) 2))))
  :hints (("Goal" :in-theory (enable evenp)))
  :rule-classes ())

(local
 (defthm oddr-other-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1)
		  (= z (fl (* (expt 2 (- (1- n) (expo x))) x)))
		  (evenp z))
	     (= (trunc x (1- n))
		(* z (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl/2)
			(:instance expt-split (r 2) (j (- (1+ (expo x)) n)) (i 1))
			(:instance oddr-other-2))))))

(local
 (defthm oddr-other-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1)
		  (= z (fl (* (expt 2 (- (1- n) (expo x))) x)))
		  (not (evenp z)))
	     (= (* (fl (/ (fl (* (expt 2 (- (1- n) (expo x))) x)) 2))
		   (expt 2 (- (+ 2 (expo x)) n)))
		(* (fl (/ z 2)) (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()))

(local
 (defthm oddr-other-5
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1)
		  (= z (fl (* (expt 2 (- (1- n) (expo x))) x)))
		  (not (evenp z)))
	     (= (trunc x (1- n))
		(* (fl (/ z 2)) (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance oddr-other-2)
			(:instance oddr-other-4))))))

(local
 (defthm hack3
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (equal x y))
	     (= (* x z) (* y z)))
  :rule-classes ()))

(local
 (defthm oddr-other-6
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1)
		  (= z (fl (* (expt 2 (- (1- n) (expo x))) x)))
		  (not (evenp z)))
	     (= (trunc x (1- n))
		(* (/ (1- z) 2) (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl/2)
			(:instance oddr-other-5)
			(:instance hack3
				   (x (/ (1- z) 2))
				   (y (fl (/ z 2)))
				   (z (expt 2 (- (+ 2 (expo x)) n)))))))))

(local
 (defthm oddr-other-7
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 1)
                 (= z (fl (* (expt 2 (- (1- n) (expo x))) x)))
                 (not (evenp z)))
            (= (trunc x (1- n))
               (* (1- z) (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable expt-split)
            :use ((:instance oddr-other-6)
                  (:instance expt-split (r 2) (j (- (1+ (expo x)) n)) (i 1)))))))

(defthm oddr-other
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (oddr x n)
		(+ (trunc x (1- n))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance oddr-other-3 (z (fl (* (expt 2 (- (1- n) (expo x))) x))))
			(:instance oddr-other-7 (z (fl (* (expt 2 (- (1- n) (expo x))) x))))
			(:instance oddr-rewrite)))))

(local
 (defthm expo-oddr-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 0))
	     (< (trunc x n) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d () ( expo-trunc abs-trunc))
		  :use ((:instance expo-trunc)
;			(:instance trunc-pos)
			(:instance expo-upper-bound (x (trunc x n))))))))

(local
 (defthm expo-oddr-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (< (oddr x n) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (expt-split) ( expo-trunc abs-trunc))
		  :use ((:instance expo-oddr-1 (n (1- n)))
			(:instance oddr-other)
			(:instance exactp-2**n (m (1- n)) (n (1+ (expo x))))
			(:instance expo-trunc (n (1- n)))
			(:instance expt-strong-monotone (n (- (1+ (expo x)) n)) (m (- (1+ (expo x)) (1- n))))
;			(:instance trunc-pos (n (1- n)))
			(:instance fp+2 (n (1- n)) (x (trunc x (1- n))) (y (expt 2 (1+ (expo x))))))))))

(local
 (defthm expo-oddr-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (<= (expo (oddr x n)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-oddr-2)
			(:instance oddr-pos)
			(:instance expo-upper-2 (x (oddr x n)) (n (1+ (expo x)))))))))

(defthm expo-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (equal (expo (oddr x n)) (expo x)))
  :hints (("Goal" :in-theory (e/d ( expt-split ) (EXPO-COMPARISON-REWRITE-TO-BOUND
                                                  EXPO-COMPARISON-REWRITE-TO-BOUND-2))
		  :use ((:instance expo-oddr-3)
			(:instance oddr-other)
;			(:instance expt-pos (x (- (1+ (expo x)) n)))
			(:instance expo-monotone (y (oddr x n)) (x (trunc x (1- n))))
			(:instance oddr-pos)
;			(:instance trunc-pos (n (1- n)))
                        ))))

(local
 (defthm exactp-oddr-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (= (* (+ (trunc x (1- n))
		      (expt 2 (- (1+ (expo x)) n)))
		   (expt 2 (- (1- n) (expo x))))
		(1+ (* (trunc x (1- n)) (expt 2 (- (1- n) (expo x)))))))
	     :rule-classes ()
  :hints (("Goal" :in-theory (disable ;expt-pos
                                      abs-trunc)
		  :use ((:instance expt-split (r 2) (j (- (1- n) (expo x))) (i (- (1+ (expo x)) n))))))))

(local
 (defthm exactp-oddr-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (= (* (oddr x n) (expt 2 (- (1- n) (expo x))))
		(1+ (* (trunc x (1- n)) (expt 2 (- (1- n) (expo x)))))))
	     :rule-classes ()
  :hints (("Goal" :in-theory (disable ;expt-pos
                                      abs-trunc)
		  :use ((:instance oddr-other)
			(:instance exactp-oddr-1))))))

(local
 (defthm exactp-oddr-3
    (implies (and (rationalp x)
		  (integerp n))
	     (= (expt 2 (- (1- n) (expo x)))
		(* 2 (expt 2 (- (- n 2) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-split (r 2) (j (- (- n 2) (expo x))) (i 1)))))))

(local
 (defthm exactp-oddr-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n))
	     (= (* y 2 (expt 2 (- (- n 2) (expo x))))
		(* 2 y (expt 2 (- (- n 2) (expo x))))))
  :rule-classes ()))

(local
 (defthm exactp-oddr-5
    (implies (and (rationalp x)
		  (integerp n))
	     (= (* (trunc x (1- n)) (expt 2 (- (1- n) (expo x))))
		(* 2 (trunc x (1- n)) (expt 2 (- (- n 2) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-oddr-3)
			(:instance exactp-oddr-4 (y (trunc x (1- n)))))))))

(local
 (defthm exactp-oddr-6
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (= (* (oddr x n) (expt 2 (- (1- n) (expo x))))
		(1+ (* 2 (* (trunc x (1- n)) (expt 2 (- (- n 2) (expo x))))))))
	     :rule-classes ()
  :hints (("Goal" :in-theory (disable ;expt-pos
                                      abs-trunc)
		  :use ((:instance exactp-oddr-2)
			(:instance exactp-oddr-5))))))

(defthm exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (exactp (oddr x n) n))
	     :rule-classes ()
  :hints (("Goal" :in-theory (disable ;expt-pos
                                      abs-trunc)
		  :use ((:instance exactp-oddr-6)
			(:instance exactp2 (x (oddr x n)))
			(:instance exactp2 (x (trunc x (1- n))) (n (1- n)))))))
(local
 (defthm not-exactp-oddr-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (= (* (+ (trunc x (1- n)) (expt 2 (- (1+ (expo x)) n)))
		   (expt 2 (- (- n 2) (expo x))))
		(+ (* (trunc x (1- n)) (expt 2 (- (- n 2) (expo x)))) 1/2)))
	     :rule-classes ()
	     :hints (("Goal" :use ((:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (- (1+ (expo x)) n))))))))

(local
 (defthm not-exactp-oddr-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (= (* (oddr x n)
		   (expt 2 (- (- n 2) (expo x))))
		(+ (* (trunc x (1- n)) (expt 2 (- (- n 2) (expo x)))) 1/2)))
	     :rule-classes ()
  :hints (("Goal" :use ((:instance oddr-other)
			(:instance not-exactp-oddr-1))))))

(defthm not-exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (not (exactp (oddr x n) (1- n))))
	     :rule-classes ()
  :hints (("Goal" :in-theory (disable ;expt-pos
                              EQUAL-MULTIPLY-THROUGH-BY-inverted-factor-FROM-RIGHT-HAND-SIDE
                                      abs-trunc)
		  :use ((:instance not-exactp-oddr-2)
			(:instance exactp2 (x (oddr x n)) (n (1- n)))
			(:instance exactp2 (x (trunc x (1- n))) (n (1- n)))))))

(local
 (defthm trunc-oddr-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (trunc (oddr x n) (1- n))
		(* (fl (* (expt 2 (- (- n 2) (expo x)))
			  (+ (* (fl (* (expt 2 (- (- n 2) (expo x)))
				       x))
				(expt 2 (- (+ (expo x) 2) n)))
			     (expt 2 (- (1+ (expo x)) n)))))
		   (expt 2 (- (+ (expo x) 2) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-pos-rewrite)
		  :use ((:instance oddr-other)
			(:instance oddr-pos))))))

(local
 (defthm trunc-oddr-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (trunc (oddr x n) (1- n))
		(* (fl (+ (fl (* (expt 2 (- (- n 2) (expo x)))
				 x))
			  1/2))
		   (expt 2 (- (+ (expo x) 2) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a15)
           :use ((:instance trunc-oddr-1)
			(:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (- (+ (expo x) 2) n)))
			(:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (- (+ (expo x) 1) n))))))))

(local
 (defthm trunc-oddr-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (trunc (oddr x n) (1- n))
		(* (fl (* (expt 2 (- (- n 2) (expo x)))
			  x))
		   (expt 2 (- (+ (expo x) 2) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-oddr-2))))))

(local
 (defthm trunc-oddr-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (trunc (oddr x n) (1- n))
		(trunc x (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-pos-rewrite)
		  :use ((:instance trunc-oddr-3))))))

(defthm trunc-oddr
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (> n m))
	     (= (trunc (oddr x n) m)
		(trunc x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-trunc)
           :use ((:instance trunc-oddr-4)
			(:instance oddr-pos)
			(:instance trunc-trunc (n (1- n)))
			(:instance trunc-trunc (n (1- n)) (x (oddr x n)))
                        ))))

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
  :rule-classes ()
  :hints (("Goal" :use ((:instance oddr-other (n k) (x y))
			(:instance expo-monotone (x y) (y (+ x y)))
			(:instance plus-trunc (k (1- k)))
			(:instance oddr-other (x (+ x y)) (n (kp k x y)))))))

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
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-oddr (x y) (m k) (n m))
			(:instance trunc-monotone (x y) (y x) (n k))))))

(local
 (defthm away-away-oddr-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (> (away x k) (trunc y (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-lower-pos (n k))
			(:instance trunc-upper-pos (x y) (n (1- m))))))))

(local
 (defthm away-away-oddr-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (away x k) (+ (trunc y (1- m)) (expt 2 (- (+ (expo y) 2) m)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-away-oddr-1)
			(:instance fp+2 (x (trunc y (1- m))) (y (away x k)) (n (1- m)))
			(:instance expo-trunc (x y) (n (1- m)))
			(:instance trunc-exactp-a (x y) (n (1- m)))
			(:instance away-exactp-a (n k))
;			(:instance trunc-pos (x y) (n (1- m)))
			(:instance exactp-<= (x (away x k)) (m k) (n (1- m))))))))

(local
 (defthm away-away-oddr-3
   (implies (and (rationalp x)
                 (rationalp y)
                 (integerp m)
                 (integerp k)
                 (> x y)
                 (> y 0)
                 (> k 0)
                 (>= (- m 2) k))
            (> (away x k) (oddr y m)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable EXPT-COMPARE)
            :use ((:instance away-away-oddr-2)
                  (:instance oddr-other (x y) (n m))
                  (:instance expt-strong-monotone (n (- (1+ (expo y)) m)) (m (- (+ (expo y) 2) m))))))))

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
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-away-oddr-3)
			(:instance oddr-pos (x y) (n m))
			(:instance away-exactp-c (a (away x k)) (x (oddr y m)) (n k))
			(:instance away-exactp-a (n k))))))

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
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-exactp-a (n (1- m)) (x y))
			(:instance oddr-pos (x y) (n m))
;			(:instance trunc-pos (x y) (n (1- m)))
			(:instance trunc-upper-pos (x y) (n (1- m)))
			(:instance expo-trunc (x y) (n (1- m)))
			(:instance oddr-other (x y) (n m))
			(:instance expt-strong-monotone
				   (n (- (1+ (expo y)) m))
				   (m (- (+ 2 (expo y)) m)))
			(:instance near-near
				   (n (- m 2))
				   (a (trunc y (1- m)))
				   (y (oddr y m)))))))
