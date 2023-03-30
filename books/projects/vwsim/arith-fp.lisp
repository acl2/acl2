
; arith-fp.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")

; (ld "arith-fp.lisp" :ld-pre-eval-print t)
; (certify-book "arith-fp.lisp" ?)
; (include-book "arith-fp.lisp")

; WARNING!  If the arithmetic definitions below are INLINEd, we must
; reload all files that include this file. If they are not INLINEd,
; then we only need to reload this file and nothing else.

; Macro to aid use of floating-point numbers in place of rationals.
(defun-inline r2f (x)
  (declare (xargs :guard t))
  ;; Maybe make a macro later...
  #-raw
  x
  #+raw
  (the double-float (coerce x 'double-float)))

(defun r2f-tree (x)
  (declare (xargs :guard t))
  #-raw
  x
  #+raw
  (if (atom x)
      ;; Consider moving r2f-tree out of this file since it uses
      ;; ``nump''.
      (if (nump x)
          (r2f x)
        x)
    (cons (r2f-tree (car x))
          (r2f-tree (cdr x)))))

(defun-inline f+ (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  #+raw (declare (type double-float x y))
  #-raw
  (+ x y)
  #+raw
  (the double-float
       (+ (the double-float x)
          (the double-float y))))

(defthm rationalp-f+
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f+ x y))))

(in-theory (disable f+))

(defun-inline f- (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  #+raw (declare (type double-float x y))
  #-raw
  (- x y)
  #+raw
  (the double-float
       (- (the double-float x)
          (the double-float y))))

(defthm rationalp-f-
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f- x y))))

(in-theory (disable f-))

(defun-inline f0- (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw
  (- x)
  #+raw
  (the double-float
    (- (the double-float x))))

(defthm rationalp-f0-
  (implies (rationalp x)
           (rationalp (f0- x))))

(in-theory (disable f0-))

(defun-inline f* (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  #+raw (declare (type double-float x y))
  #-raw
  (* x y)
  #+raw
  (the double-float
       (* (the double-float x)
          (the double-float y))))

(defthm rationalp-f*
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f* x y))))

(in-theory (disable f*))

(defun-inline f/ (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y)
                              (not (= y 0)))))
  #+raw (declare (type double-float x y))
  #-raw
  (/ x y)
  #+raw
  (the double-float
       (/ (the double-float x)
          (the double-float y))))

(defthm rationalp-f/
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f/ x y))))

(in-theory (disable f/))

(defun-inline f= (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  #+raw (declare (type double-float x y))
  #-raw
  (if (= x y) 1 0)
  #+raw
  (if (= (the double-float x)
         (the double-float y))
      1.0d0 ;; (coerce 1 'double-float)
    0.0d0 ;; (coerce 0 'double-float)
    ))

(defthm rationalp-f=
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f= x y))))

(in-theory (disable f=))

(defun-inline f< (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  #+raw (declare (type double-float x y))
  #-raw
  (if (< x y) 1 0)
  #+raw
  (if (< (the double-float x)
         (the double-float y))
      1.0d0 ;;(coerce 1 'double-float)
    0.0d0 ;;(coerce 0 'double-float)
    ))

(defthm rationalp-f<
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f< x y))))

(in-theory (disable f<))

(defun-inline f-not (x)
  (declare (xargs :guard (and (rationalp x))))
  #+raw (declare (type double-float x))
  #-raw (if (= x 0) 1 0)
  #+raw (if (= (the double-float x) ;;(coerce 0 'double-float)
               0.0d0)
            1.0d0 ;;(coerce 1 'double-float)
          0.0d0 ;;(coerce 0 'double-float)
          ))

(defthm rationalp-f-not
  (implies (rationalp x)
           (rationalp (f-not x))))

(in-theory (disable f-not))

(defun-inline f-1/x (x)
  (declare (xargs :guard (and (rationalp x)
                              (not (= x 0)))))
  #+raw (declare (type double-float x))
  #-raw
  (/ x)
  #+raw
  (the double-float
       (/ (the double-float x))))

(defthm rationalp-f-1/x
  (implies (rationalp x)
           (rationalp (f-1/x x))))

(in-theory (disable f-1/x))

(defun-inline f-abs (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw
  (abs x)
  #+raw
  (the double-float
       (abs (the double-float x))))

(defthm rationalp-f-abs
  (implies (rationalp x)
           (rationalp (f-abs x))))

(in-theory (disable f-abs))

(encapsulate
  (((r-sqrt *) => *))
  (local (defun r-sqrt (x)
           (declare (ignore x))
           0))
  (defthm rationalp-r-sqrt
    (implies (rationalp x)
             (rationalp (r-sqrt x))))
  (defthm r-sqrt-bounds
    (implies (and (rationalp x)
                  (<= 0 x))
             (<= 0 (r-sqrt x)))
    :rule-classes :linear)
  (defthm r-sqrt-0
    (equal (r-sqrt 0) 0)))

#||
(defun r-sqrt-help (x sqrt count)
  ;; Babylonian method for square root
  (declare (xargs :guard (and (rationalp x)
                              (< 0 x)
                              (rationalp sqrt)
                              (< 0 sqrt)
                              (natp count))))
  (if (zp count)
      sqrt
    (r-sqrt-help x (/ (+ sqrt (/ x sqrt)) 2) (1- count))))

(defun f2r (x)
  #-raw
  x
  #+raw
  (the rational (rational x)))

(defun r-sqrt (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  (if (= 0 x)
      0
    (f2r (r2f (r-sqrt-help x (/ x 2) 10)))))

||#

(defun-inline f-sqrt (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  #+raw (declare (type double-float x))
  #-raw (r-sqrt x)
  #+raw (the double-float
          (sqrt (the double-float x))))

(defthm rationalp-f-sqrt
  (implies (rationalp x)
           (rationalp (f-sqrt x))))

(in-theory (disable f-sqrt))

(encapsulate
  (((r-sin *) => *))
  (local (defun r-sin (x)
           (declare (ignore x))
           0))
  (defthm rationalp-r-sin
    (rationalp (r-sin x))
    :rule-classes :type-prescription)
  (defthm r-sin-bounds
    (and (<= -1 (r-sin x))
         (<= (r-sin x) 1))
    :rule-classes :linear)
  (defthm r-sin-0
    (equal (r-sin 0) 0))
  (defthm r-sin-minus
    (equal (r-sin (- x))
           (- (r-sin x)))))

(defun-inline f-sin (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw (r-sin x)
  #+raw (the double-float (sin (the double-float x))))

(defthm rationalp-f-sin
  (implies (rationalp x)
           (rationalp (f-sin x))))

(in-theory (disable f-sin))

(encapsulate
  (((r-cos *) => *))
  (local (defun r-cos (x)
           (declare (ignore x))
           1))
  (defthm rationalp-r-cos
    (rationalp (r-cos x))
    :rule-classes :type-prescription)
  (defthm r-cos-bounds
    (and (<= -1 (r-cos x))
         (<= (r-cos x) 1))
    :rule-classes :linear)
  (defthm r-cos-0
    (equal (r-cos 0) 1))
  (defthm r-cos-minus
    (equal (r-cos (- x))
           (r-cos x))))

(defun-inline f-cos (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw (r-cos x)
  #+raw (the double-float (cos (the double-float x))))

(defthm rationalp-f-cos
  (implies (rationalp x)
           (rationalp (f-cos x))))

(in-theory (disable f-cos))

(encapsulate
  (((r-tan *) => *))
  (local (defun r-tan (x)
           (declare (ignore x))
           0))
  (defthm rationalp-r-tan
    (rationalp (r-tan x))
    :rule-classes :type-prescription)
  (defthm r-tan-0
    (equal (r-tan 0) 0))
  (defthm r-tan-minus
    (equal (r-tan (- x))
           (r-tan x))))

(defun-inline f-tan (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw (r-tan x)
  #+raw (the double-float (tan (the double-float x))))

(defthm rationalp-f-tan
  (implies (rationalp x)
           (rationalp (f-tan x))))

(in-theory (disable f-tan))

(encapsulate
  (((r-tanh *) => *))
  (local (defun r-tanh (x)
           (declare (ignore x))
           0))
  (defthm rationalp-r-tanh
    (rationalp (r-tanh x))
    :rule-classes :type-prescription)
  (defthm r-tanh-0
    (equal (r-tanh 0) 0))
  (defthm r-tanh-minus
    (equal (r-tanh (- x))
           (r-tanh x))))

(defun-inline f-tanh (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw (r-tanh x)
  #+raw (the double-float (tanh (the double-float x))))

(defthm rationalp-f-tanh
  (implies (rationalp x)
           (rationalp (f-tanh x))))

(in-theory (disable f-tanh))

(encapsulate
  (((r-exp *) => *))
  (local (defun r-exp (x)
           (declare (ignore x))
           1))
  (defthm rationalp-r-exp
    (rationalp (r-exp x))
    :rule-classes :type-prescription)
  (defthm r-exp-0
    (equal (r-exp 0) 1)))

(defun-inline f-exp (x)
  (declare (xargs :guard (rationalp x)))
  #+raw (declare (type double-float x))
  #-raw (r-exp x)
  #+raw (the double-float (exp (the double-float x))))

(defthm rationalp-f-exp
  (implies (rationalp x)
           (rationalp (f-exp x))))

(in-theory (disable f-exp))

(defun-inline f-mod (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y)
                              (not (equal y 0)))))
  #+raw (declare (type double-float x y))
  #-raw
  (mod x y)
  #+raw
  (the double-float
    (mod (the double-float x)
         (the double-float y))))

(defthm rationalp-f-mod
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (f-mod x y))))

(in-theory (disable f-mod))
