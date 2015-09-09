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

(in-package "ACL2")


(include-book "bits-new")
(include-book "logn-new")
(include-book "arith")


(local (include-book "../lib2/top"))

(local
 (encapsulate ()
              (local (include-book "bits-new-proofs"))

             (defthm bits_alt-is-bits
               (equal (bits_alt x i j)
                      (bits x i j)))


             (defthm bitn_alt-is-bitn
               (equal (bitn_alt x n)
                      (bitn x n)))


             (defthm binary-cat_alt-is-binary-cat
               (equal (binary-cat_alt x m y n)
                      (binary-cat x m y n)))

             ))

;; ;;;;;

(local
 (defthm lnot_alt-is-lnot
   (equal (lnot_alt x n)
          (lnot x n))
   :hints (("Goal" :in-theory (e/d (lnot_alt lnot))))))


(local (include-book "../lib2/simplify-model-helpers"))





(defthm equal-log=-0
  (equal (equal (log= k x)
                0)
         (not (equal k x))))

(defthm equal-log=-1 ; possibly not needed
  (equal (equal (log= k x)
                1)
         (equal k x)))

(defthm equal-lnot_alt-0
  (implies (bvecp x 1)
           (equal (equal (lnot_alt x 1) 0)
                  (equal x 1))))

(defthm equal-lnot_alt-1 ; possibly not needed
  (implies (bvecp x 1)
           (equal (equal (lnot_alt x 1) 1)
                  (equal x 0))))

(defthm bits_alt-if
  (equal (bits_alt (if x y z) i j)
         (if x (bits_alt y i j) (bits_alt z i j))))

(defthm bitn_alt-if
  (equal (bitn_alt (if x y z) i)
         (if x (bitn_alt y i) (bitn_alt z i))))

(defthm bits_alt-if1
  (equal (bits_alt (if1 x y z) i j)
         (if1 x (bits_alt y i j) (bits_alt z i j))))

(defthm bitn_alt-if1
  (equal (bitn_alt (if1 x y z) i)
         (if1 x (bitn_alt y i) (bitn_alt z i))))

(defthm log=-0-rewrite_alt
  (implies (bvecp k 1)
           (equal (log= 0 k)
                  (lnot_alt k 1))))

(defthm log=-1-rewrite
  (implies (bvecp k 1)
           (equal (log= 1 k)
                  k)))

(defthm log<>-is-lnot_alt-log=
  (equal (log<> x y) (lnot_alt (log= x y) 1)))

(defthm cat_alt-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep m)
                              (quotep y)
                              (quotep n)))
                (equal (+ n p) r)
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 p))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p)))
           (equal (cat_alt x m (cat_alt y n z p) r)
                  (cat_alt (cat_alt x m y n) (+ m n) z p))))

(defthm bvecp-if
  (equal (bvecp (if test x y) k)
         (if test (bvecp x k) (bvecp y k))))

; bvecp-if1 is analogous to the above, and is already included in rtl.lisp

; Setbits_alt can introduce a call of cat_alt, which can introduce (bits_alt (sig n) 2 0)
; say, even though sig is a single bit.  So we add the following.

(in-theory (enable bvecp-monotone))
