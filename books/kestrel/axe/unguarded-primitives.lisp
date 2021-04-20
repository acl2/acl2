; Versions of primitive functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines functions that are equivalent to ACL2 primitive functions
;; but have guards of t (for use in evaluators).

(defund car-unguarded (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defthm car-unguarded-correct
  (equal (car-unguarded x)
         (car x))
  :hints (("Goal" :in-theory (enable car-unguarded))))

(defund cdr-unguarded (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defthm cdr-unguarded-correct
  (equal (cdr-unguarded x)
         (cdr x))
  :hints (("Goal" :in-theory (enable cdr-unguarded))))

(defund binary-+-unguarded (x y)
  (declare (xargs :guard t))
  (binary-+ (fix x) (fix y)))

(defthm binary-+-unguarded-correct
  (equal (binary-+-unguarded x y)
         (binary-+ x y))
  :hints (("Goal" :in-theory (enable binary-+-unguarded))))

(defund binary-*-unguarded (x y)
  (declare (xargs :guard t))
  (binary-* (fix x) (fix y)))

(defthm binary-*-unguarded-correct
  (equal (binary-*-unguarded x y)
         (binary-* x y))
  :hints (("Goal" :in-theory (enable binary-*-unguarded))))

;; consider defun$inline, and making the rare case separate
(defund <-unguarded (x y)
  (declare (xargs :guard t))
  (if (and (real/rationalp x)
           (real/rationalp y))
      (< x y)
    (let ((x1 (if (acl2-numberp x) x 0))
          (y1 (if (acl2-numberp y) y 0)))
      (or (< (realpart x1) (realpart y1))
          (and (equal (realpart x1) (realpart y1))
               (< (imagpart x1) (imagpart y1)))))))

(defthm <-unguarded-correct
  (equal (<-unguarded x y)
         (< x y))
  :hints (("Goal" :in-theory (enable <-unguarded)
           :use (:instance completion-of-<))))

(defund unary---unguarded (x)
  (declare (xargs :guard t))
  (unary-- (fix x)))

(defthm unary---unguarded-correct
  (equal (unary---unguarded x)
         (unary-- x))
  :hints (("Goal" :in-theory (enable unary---unguarded))))

(defund unary-/-unguarded (x)
  (declare (xargs :guard t))
  (if (equal 0 (fix x))
      0
    (unary-/ x)))

(defthm unary-/-unguarded-correct
  (equal (unary-/-unguarded x)
         (unary-/ x))
  :hints (("Goal" :in-theory (enable unary-/-unguarded))))
