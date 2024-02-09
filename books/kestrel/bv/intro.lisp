; Rules to introduce BV ops
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bv-syntax")
(local (include-book "logxor-b"))
(local (include-book "logior-b"))

;; We'll keep these disabled as they may conflict with opening up the BV
;; functions.

(defthmd bvchop-of-logand-becomes-bvand
  (equal (bvchop size (logand x y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd bvchop-of-logior-becomes-bvor
  (equal (bvchop size (logior x y))
         (bvor size x y))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd bvchop-of-logxor-becomes-bvxor
  (equal (bvchop size (logxor x y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthmd bvchop-of-+-becomes-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthmd bvchop-of---becomes-bvminus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (- x y))
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvminus))))

(defthm logand-becomes-bvand
  (implies (and (bind-free (bind-var-to-bv-term-size 'size x))
;                (bind-free (bind-var-to-bv-term-size 'size y))
                (unsigned-byte-p size x)
;               (unsigned-byte-p size y)
                (natp y)
                )
           (equal (logand x y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand logand-of-bvchop))))

(defthmd logand-of-bvchop-becomes-bvand
  (implies (and (natp width)
                (natp y)) ;gen
           (equal (logand y (bvchop width x))
                  (bvand width y x)))
  :hints (("Goal" :use (:instance logand-becomes-bvand (size width) (x (bvchop width x)))
           :in-theory (disable logand-becomes-bvand))))

(defthmd logand-of-bvchop-becomes-bvand-alt
  (implies (and (natp width)
                (natp y)) ;gen
           (equal (logand (bvchop width x) y)
                  (bvand width y x)))
  :hints (("Goal" :use (:instance logand-becomes-bvand (size width) (x (bvchop width x)))
           :in-theory (disable logand-becomes-bvand))))
