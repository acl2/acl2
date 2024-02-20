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
(include-book "bvcat-def")
(include-book "defs-bitwise")
(include-book "unsigned-byte-p-forced")
(local (include-book "logxor-b"))
(local (include-book "logior-b"))

;; See also ../axe/bv-intro-rules.lisp

;; We'll keep these disabled as they may conflict with opening up the BV
;; functions.

(defthm bvchop-of-lognot-becomes-bvnot
  (equal (bvchop size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable bvnot))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd logapp-becomes-bvcat-when-unsigned-byte-p-1
  (implies (unsigned-byte-p 1 j)
           (equal (logapp size i j)
                  (bvcat 1 j size i)))
  :hints (("Goal" :in-theory (enable bvcat))))

;; logapp does not indicate the size of the high bits, so we have to try to
;; figure it out.
(defthmd logapp-becomes-bvcat-when-bv
  (implies (and (bind-free (acl2::bind-var-to-bv-term-size 'jsize j) (jsize))
                (unsigned-byte-p-forced jsize j))
           (equal (logapp size i j)
                  (bvcat jsize j size i)))
  :hints (("Goal" :in-theory (enable bvcat))))
