; Versions of built-in functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Because of differences in floor? (todo):
; cert_param: (non-acl2r)

(include-book "unguarded-primitives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund zp-unguarded (x)
  (declare (xargs :guard t))
  (zp (nfix x)))

(defthm zp-unguarded-correct
  (equal (zp-unguarded x)
         (zp x))
  :hints (("Goal" :in-theory (enable zp-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund nonnegative-integer-quotient-unguarded (i j)
  (declare (xargs :guard t))
  (if (or (= (nfix j) 0) (< (ifix i) j))
      0
    (nonnegative-integer-quotient i j)))

(defthm nonnegative-integer-quotient-unguarded-correct
  (equal (nonnegative-integer-quotient-unguarded x y)
         (nonnegative-integer-quotient x y))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient
                                     nonnegative-integer-quotient-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund floor-unguarded (i j)
  (declare (xargs :guard t))
  (if (and (real/rationalp i)
           (real/rationalp j)
           (not (equal j 0)))
      (floor i j)
    ;; may be slow:
    (let* ((q (binary-*-unguarded i (unary-/-unguarded j)))
           (n (numerator-unguarded q))
           (d (denominator-unguarded q)))
      (cond ((= d 1) n)
            ((>= n 0)
             (nonnegative-integer-quotient-unguarded n d))
            (t (+ (- (nonnegative-integer-quotient-unguarded (- n) d))
                  -1))))))

;; Doesn't work in ACL2(r)
(defthm floor-unguarded-correct
  (equal (floor-unguarded x y)
         (floor x y))
  :hints (("Goal" :in-theory (enable floor
                                     floor-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun truncate-unguarded (i j)
  (declare (xargs :guard t))
  (let* ((q (binary-*-unguarded i (unary-/-unguarded j)))
         (n (numerator-unguarded q))
         (d (denominator-unguarded q)))
    (cond ((= d 1) n)
          ((>= n 0)
           (nonnegative-integer-quotient-unguarded n d))
          (t (- (nonnegative-integer-quotient-unguarded (- n)
                                              d))))))

;; Doesn't work in ACL2(r)?
(defthm truncate-unguarded-correct
  (equal (truncate-unguarded x y)
         (truncate x y))
  :hints (("Goal" :in-theory (enable truncate
                                     truncate-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund ceiling-unguarded (i j)
  (declare (xargs :guard t))
  (if (and (rationalp i)
           (rationalp j)
           (not (equal j 0)))
      (ceiling i j)
    ;; may be slow:
    (let* ((q (binary-*-unguarded i (unary-/-unguarded j)))
           (n (numerator-unguarded q))
           (d (denominator-unguarded q)))
      (cond ((= d 1) n)
            ((>= n 0)
             (+ (nonnegative-integer-quotient-unguarded n d)
                1))
            (t (- (nonnegative-integer-quotient-unguarded (- n)
                                                          d)))))))

(defthm ceiling-unguarded-correct
  (equal (ceiling-unguarded i j)
         (ceiling i j))
  :hints (("Goal" :in-theory (enable ceiling
                                     ceiling-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund mod-unguarded (x y)
  (declare (xargs :guard t))
  (- (fix x) (binary-*-unguarded (floor-unguarded x y) y)))

(defthm mod-unguarded-correct
  (equal (mod-unguarded x y)
         (mod x y))
  :hints (("Goal" :in-theory (enable mod
                                     mod-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rem-unguarded (x y)
  (declare (xargs :guard t))
  (- (fix x) (binary-*-unguarded (truncate-unguarded x y) y)))

(defthm rem-unguarded-correct
  (equal (rem-unguarded x y)
         (rem x y))
  :hints (("Goal" :in-theory (enable rem
                                     rem-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund min-unguarded (x y)
  (declare (xargs :guard t))
  (if (<-unguarded x y) x y))

(defthm min-unguarded-correct
  (equal (min-unguarded x y)
         (min x y))
  :hints (("Goal" :in-theory (enable <-unguarded-correct
                                     min-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund max-unguarded (x y)
  (declare (xargs :guard t))
  (if (<-unguarded y x) x y))

(defthm max-unguarded-correct
  (equal (max-unguarded x y)
         (max x y))
  :hints (("Goal" :in-theory (enable <-unguarded-correct
                                     max-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund integer-length-unguarded (x)
  (declare (xargs :guard t))
  (integer-length (ifix x)))

(defthm integer-length-unguarded-correct
  (equal (integer-length-unguarded x)
         (integer-length x))
  :hints (("Goal" :in-theory (enable integer-length
                                     integer-length-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund =-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm =-unguarded-correct
  (equal (=-unguarded x y)
         (= x y))
  :hints (("Goal" :in-theory (enable =-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;TODO use fix functions here?
(defund expt-unguarded (r i)
  (declare (xargs :guard t))
  (cond ((not (integerp i)) 1)
        ((equal 0 i) 1)
        ((= (fix r) 0) 0)
        (t (expt r i))))

(defthm expt-unguarded-correct
  (equal (expt-unguarded r i)
         (expt r i))
  :hints (("Goal" :in-theory (enable expt-unguarded expt))))
