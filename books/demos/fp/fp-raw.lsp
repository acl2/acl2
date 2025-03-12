; Copyright (C) 2024, Matt Kaufmann and J Strother Moore
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains raw Lisp redefinitions of functions introduced in the book
; fp.lisp.

(in-package "ACL2")

; As in ACL2, read floating-point numbers as double-floats.  This might not be
; necessary here but could become necessary with future modifications.
(setq *read-default-float-format* 'double-float)

(defun to-fp (x)
  (declare (type rational x))
  (float x 0.0D0))

(defun make-fp (x)

; This is based on ACL2 source function make-df.  If x is a double-float or a
; representable rational, we return the suitable double-float; else nil is
; returned.

  (cond ((typep x 'double-float) x)
        ((rationalp x)
         (let ((xf (to-fp x)))
           (and (= xf x)
                xf)))
        (t nil)))

; The defun-*1* macro expands to the corresponding defun in which the first
; argument is replaced by the executable-counterpart ("*1*") function for that
; name.  See :DOC evaluation.

(defun-*1* to-fp (x)
  (cond ((typep x 'double-float)
         (rational x))
        ((rationalp x)
         (rational (to-fp x)))
        (t ; really a guard violation, but we use simpler code here
         (constrained-to-fp x))))

(defun fp-sqrt (x)
  (declare (type double-float x))
  (sqrt x))

(defun-*1* fp-sqrt (x)
  (let ((xf (make-fp x)))
    (cond ((and xf (<= 0 x))
           (rational (fp-sqrt xf)))
          (t ; really a guard violation, but we use simpler code here
           (constrained-fp-sqrt x)))))

(defun fp+ (x y)
  (declare (type double-float x y))
  (+ x y))

(defun-*1* fp+ (x y)
  (let ((xf (make-fp x)) (yf (make-fp y)))
    (cond ((and xf yf) (rational (+ xf yf)))
          (t ; really a guard violation, but we use simpler code here
           (fp-round (funcall (*1*-symbol 'binary-+) x y))))))
