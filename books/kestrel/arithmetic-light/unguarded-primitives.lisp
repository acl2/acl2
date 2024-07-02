; Versions of primitive functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Because of complex-unguarded-correct (todo):
; cert_param: (non-acl2r)

(defund binary-+-unguarded (x y)
  (declare (xargs :guard t))
  (binary-+ (fix x) (fix y)))

(defthm binary-+-unguarded-correct
  (equal (binary-+-unguarded x y)
         (binary-+ x y))
  :hints (("Goal" :in-theory (enable binary-+-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-*-unguarded (x y)
  (declare (xargs :guard t))
  (binary-* (fix x) (fix y)))

(defthm binary-*-unguarded-correct
  (equal (binary-*-unguarded x y)
         (binary-* x y))
  :hints (("Goal" :in-theory (enable binary-*-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
           :use completion-of-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund unary---unguarded (x)
  (declare (xargs :guard t))
  ;; (unary-- (fix x))
  (if (acl2-numberp x) (- x) 0)
  )

(defthm unary---unguarded-correct
  (equal (unary---unguarded x)
         (unary-- x))
  :hints (("Goal" :in-theory (enable unary---unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund unary-/-unguarded (x)
  (declare (xargs :guard t))
  (if (equal 0 (fix x))
      0
    (unary-/ x)))

(defthm unary-/-unguarded-correct
  (equal (unary-/-unguarded x)
         (unary-/ x))
  :hints (("Goal" :in-theory (enable unary-/-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund numerator-unguarded (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (numerator x)
    0))

(defthm numerator-unguarded-correct
  (equal (numerator-unguarded x)
         (numerator x))
  :hints (("Goal" :in-theory (enable numerator-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund denominator-unguarded (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (denominator x)
    1))

(defthm denominator-unguarded-correct
  (equal (denominator-unguarded x)
         (denominator x))
  :hints (("Goal" :in-theory (enable denominator-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund complex-unguarded (x y)
  (declare (xargs :guard t))
  (complex (rfix x) (rfix y)))

(defthm complex-unguarded-correct
  (equal (complex-unguarded x y)
         (complex x y))
  :hints (("Goal" :in-theory (enable complex-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund realpart-unguarded (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x)
      (realpart x)
    0))

(defthm realpart-unguarded-correct
  (equal (realpart-unguarded x)
         (realpart x))
  :hints (("Goal" :in-theory (enable realpart-unguarded realpart))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund imagpart-unguarded (x)
  (declare (xargs :guard t))
  (if (acl2-numberp x)
      (imagpart x)
    0))

(defthm imagpart-unguarded-correct
  (equal (imagpart-unguarded x)
         (imagpart x))
  :hints (("Goal" :in-theory (enable imagpart-unguarded imagpart))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
