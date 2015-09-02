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

(include-book "rtl")
(include-book "bits")
(include-book "logn")
(include-book "arith")

(local (include-book "simplify-model-helpers-new"))



(local
 (defthm bits-is-bits_alt
   (equal (bits x i j)
          (bits_alt x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

(local
 (defthm bitn-is-bitn_alt
   (equal (bitn x n)
          (bitn_alt x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat x m y n)
          (binary-cat_alt x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat_alt binary-cat) ())))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat l n x)
          (mulcat_alt l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))


(local
 (defthm lnot_alt-is-lnot
   (equal (lnot_alt x n)
          (lnot x n))
   :hints (("Goal" :in-theory (e/d (lnot_alt lnot) ())))))




(defthm equal-log=-0
  (equal (equal (log= k x)
                0)
         (not (equal k x))))

(defthm equal-log=-1 ; possibly not needed
  (equal (equal (log= k x)
                1)
         (equal k x)))

(defthm equal-lnot-0
  (implies (bvecp x 1)
           (equal (equal (lnot x 1) 0)
                  (equal x 1))))

(defthm equal-lnot-1 ; possibly not needed
  (implies (bvecp x 1)
           (equal (equal (lnot x 1) 1)
                  (equal x 0))))

(defthm bits-if
  (equal (bits (if x y z) i j)
         (if x (bits y i j) (bits z i j))))

(defthm bitn-if
  (equal (bitn (if x y z) i)
         (if x (bitn y i) (bitn z i))))

(defthm bits-if1
  (equal (bits (if1 x y z) i j)
         (if1 x (bits y i j) (bits z i j))))

(defthm bitn-if1
  (equal (bitn (if1 x y z) i)
         (if1 x (bitn y i) (bitn z i))))

(defthm log=-0-rewrite
  (implies (bvecp k 1)
           (equal (log= 0 k)
                  (lnot k 1))))

(defthm log=-1-rewrite
  (implies (bvecp k 1)
           (equal (log= 1 k)
                  k)))

(defthm log<>-is-lnot-log=
  (equal (log<> x y) (lnot (log= x y) 1)))

(defthm cat-combine-constants
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
           (equal (cat x m (cat y n z p) r)
                  (cat (cat x m y n) (+ m n) z p))))

(defthm bvecp-if
  (equal (bvecp (if test x y) k)
         (if test (bvecp x k) (bvecp y k))))

; bvecp-if1 is analogous to the above, and is already included in rtl.lisp

; Setbits can introduce a call of cat, which can introduce (bits (sig n) 2 0)
; say, even though sig is a single bit.  So we add the following.

(in-theory (enable bvecp-monotone))
