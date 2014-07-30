; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@aus.edsr.eds.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.


(in-package "ACL2")

(include-book "bdd-primitives")

(defun full-adder (c a b)
  (list (b-xor3 c a b)
        (b-or (b-and a b)
              (b-or (b-and a c)
                    (b-and b c)))))

(defun v-inc (x)

; Allows overflow; returns a vector of the same length.

  (cond
   ((nlistp x)
    nil)
   ((equal (car x) nil)
    (cons t (cdr x)))
   (t (cons nil (v-inc (cdr x))))))

(defthm len-v-inc
  (equal (len (v-inc x))
         (len x)))

(defthm bvp-v-inc
  (implies (bvp x)
           (bvp (v-inc x))))

(defthm v-if-is-if
  (implies (bv2p x y)
           (equal (v-if a x y)
                  (if a x y))))

(encapsulate
 ()

; Hide is a real pain!

 (local (defthm hack
          (equal (hide (v-inc x))
                 (v-inc x))
          :hints (("Goal" :expand (hide (v-inc x))))
          :rule-classes nil))

 (defthm v-inc-cons
   (equal (v-inc (cons a y))
          (if* (bvp y)
               (cons (b-not a)
                     (v-if a
                           (v-inc y)
                           y))
               (hide (v-inc (cons a y)))))
   :hints (("Goal" :use
            ((:instance
              hack
              (x (cons a y)))
             (:instance
              hack
              (x (cons nil y)))
             (:instance
              hack
              (x (cons t y))))))))

(defun v-logcount (input acc)
  (if (nlistp input)
      acc
    (v-logcount (cdr input)
                (v-if (car input)
                      (v-inc acc)
                      acc))))

(defthm v-logcount-nil
  (equal (v-logcount nil acc)
         acc))

(defthm v-logcount-cons
  (equal (v-logcount (cons a x) acc)
         (v-logcount x
                     (v-if a
                           (v-inc acc)
                           acc))))

(defun hamming (input)
  (let* ((s0-15 (firstn 16 input))
         (s16-19 (restn 16 input))
         (v0 (nth 0 s0-15))
         (v1 (nth 1 s0-15))
         (v2 (nth 2 s0-15))
         (v3 (nth 3 s0-15))
         (v4 (nth 4 s0-15))
         (v5 (nth 5 s0-15))
         (v6 (nth 6 s0-15))
         (v7 (nth 7 s0-15))
         (v8 (nth 8 s0-15))
         (v9 (nth 9 s0-15))
         (v10 (nth 10 s0-15))
         (v11 (nth 11 s0-15))
         (v12 (nth 12 s0-15))
         (v13 (nth 13 s0-15))
         (v14 (nth 14 s0-15))
         (v15 (nth 15 s0-15))
         (v16 (nth 0 s16-19))
         (v17 (nth 1 s16-19))
         (v18 (nth 2 s16-19))
         (v19 (nth 3 s16-19))
         (m11 (full-adder nil v18 v19))
         (m11o (nth 0 m11))
         (m11c (nth 1 m11))
         (m12 (full-adder v15 v16 v17))
         (m12o (nth 0 m12))
         (m12c (nth 1 m12))
         (m13 (full-adder v12 v13 v14))
         (m13o (nth 0 m13))
         (m13c (nth 1 m13))
         (m14 (full-adder v9 v10 v11))
         (m14o (nth 0 m14))
         (m14c (nth 1 m14))
         (m15 (full-adder v6 v7 v8))
         (m15o (nth 0 m15))
         (m15c (nth 1 m15))
         (m16 (full-adder v3 v4 v5))
         (m16o (nth 0 m16))
         (m16c (nth 1 m16))
         (m17 (full-adder v0 v1 v2))
         (m17o (nth 0 m17))
         (m17c (nth 1 m17))
         (m7 (full-adder m13o m12o m11o))
         (m7o (nth 0 m7))
         (m7c (nth 1 m7))
         (m8 (full-adder m13c m12c m11c))
         (m8o (nth 0 m8))
         (m8c (nth 1 m8))
         (m9 (full-adder m16o m15o m14o))
         (m9o (nth 0 m9))
         (m9c (nth 1 m9))
         (m10 (full-adder m16c m15c m14c))
         (m10o (nth 0 m10))
         (m10c (nth 1 m10))
         (m6 (full-adder m17c m9c m7c))
         (m6o (nth 0 m6))
         (m6c (nth 1 m6))
         (m4 (full-adder m6o m10o m8o))
         (m4o (nth 0 m4))
         (m4c (nth 1 m4))
         (m5 (full-adder m10c m8c m6c))
         (m5o (nth 0 m5))
         (m5c (nth 1 m5))
         (m0 (full-adder m17o m7o m9o))
         (m0o (nth 0 m0))
         (m0c (nth 1 m0))
         (m1 (full-adder m0c nil m4o))
         (m1o (nth 0 m1))
         (m1c (nth 1 m1))
         (m2 (full-adder m1c m4c m5o))
         (m2o (nth 0 m2))
         (m2c (nth 1 m2))
         (m3 (full-adder m2c m5c nil))
         (m3o (nth 0 m3))
         (m3c (nth 1 m3)))
    (list m0o m1o m2o m3o m3c)))

(defthm hamming-correct

; 7708 nodes.  Time on Sparc 10:
; Time:  2.10 seconds (prove: 1.93, print: 0.03, other: 0.13)

  (let ((input (list i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                     i16 i17 i18 i19)))
    (implies (bvp input)
             (equal (hamming input)
                    (v-logcount input (make-nils 5)))))
  :hints (("Goal" :bdd (:vars t)))
  :rule-classes nil)

(defthm hamming-correct-vars-reversed

; 4787 nodes.  Time on Sparc 10:
; Time:  1.52 seconds (prove: 1.38, print: 0.03, other: 0.10)

  (let ((input (list i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                     i16 i17 i18 i19)))
    (implies (bvp input)
             (equal (hamming input)
                    (v-logcount input (make-nils 5)))))
  :hints (("Goal" :bdd
           (:vars (i19 i18 i17 i16 i15 i14 i13 i12 i11 i10 i9 i8 i7 i6 i5 i4 i3
                       i2 i1 i0))))
  :rule-classes nil)

(defthm hamming-correct-v-20-bit-logcount

; 7734 nodes.  Time on Sparc 10:
; Time:  4.92 seconds (prove: 4.75, print: 0.03, other: 0.13)

  (let ((input (list i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                     i16 i17 i18 i19)))
    (implies (bvp input)
             (equal (hamming input)
                    (v-trunc (v-logcount input (make-nils 20)) 5))))
  :hints (("Goal" :bdd (:vars t))))

(defthm hamming-correct-v-20-bit-logcount-vars-reversed

; 4813 nodes.  Time on Sparc 10:
; Time:  4.30 seconds (prove: 4.12, print: 0.03, other: 0.15)

  (let ((input (list i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                     i16 i17 i18 i19)))
    (implies (bvp input)
             (equal (hamming input)
                    (v-trunc (v-logcount input (make-nils 20)) 5))))
  :hints (("Goal" :bdd
           (:vars (i19 i18 i17 i16 i15 i14 i13 i12 i11 i10 i9 i8 i7 i6 i5 i4 i3
                       i2 i1 i0)))))

#|
; Here is a nice example of a non-theorem, whose failure can be explored using
; (show-bdd).

(thm
  (let ((input (list i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15
                     i16 i17 i18 i19)))
    (implies (bvp input)
             (equal (hamming input)
                    (v-logcount (cddr input) (make-nils 5)))))
  :hints (("Goal" :bdd (:vars t))))
|#
