; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

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

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

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

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defund rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defund rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))


(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

;;;**********************************************************************
;;;		    	      RTZ-SQRT
;;;**********************************************************************

(defsection-rtl |Truncation {Square Root}| |IEEE-Compliant Square Root|

(defund rtz-sqrt (x n)
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

(defsection-rtl |Odd Rounding {Square Root}| |IEEE-Compliant Square Root|

(defund rto-sqrt (x n)
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

(defsection-rtl |IEEE Rounding {Square Root}| |IEEE-Compliant Square Root|

(defund qsqrt (x n)
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
                (iff (> (* q q) x) (> q (qsqrt x n)))))
  :rule-classes ())
)
