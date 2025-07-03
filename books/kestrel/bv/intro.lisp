; Rules to introduce BV ops
;
; Copyright (C) 2022-2025 Kestrel Institute
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
(include-book "bvsx-def")
(include-book "bvif")
(include-book "defs-bitwise")
(include-book "unsigned-byte-p-forced")
(include-book "ihs/basic-definitions" :dir :system) ;for logmask
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "logxor-b"))
(local (include-book "logior-b"))
(local (include-book "logand-b"))
(local (include-book "slice-rules"))
(local (include-book "slice"))
(local (include-book "rules"))

;; See also ../axe/bv-intro-rules.lisp

;; We'll keep these disabled as they may conflict with opening up the BV
;; functions.

(defthmd bvchop-of-lognot-becomes-bvnot
  (equal (bvchop size (lognot x))
         (bvnot size x))
  :hints (("Goal" :in-theory (enable bvnot))))

;; todo: more theory invars?
;; todo: rules for bvchop, slice, and getbit or each thing?

(theory-invariant (incompatible (:rewrite bvchop-of-lognot-becomes-bvnot) (:definition bvnot)))

;; or got to getbit of bvnot first?
(defthm getbit-of-lognot
  (implies (natp m)
           (equal (getbit m (lognot x))
                  (bvnot 1 (getbit m x))))
  :hints (("Goal" :in-theory (e/d (lognot
                                   getbit
                                   SLICE-OF-SUM-CASES
                                   ifix)
                                  (;BITXOR-OF-SLICE-ARG2
                                   )))))

(defthm slice-of-lognot
  (implies (and (natp high) ;drop?
                (natp low))
           (equal (slice high low (lognot x))
                  (slice high low (bvnot (+ 1 high) x))))
  :hints (("Goal" ;:cases ((natp high))
           :in-theory (enable bvnot))))

(defthm getbit-of-logmask
  (implies (and (natp n)
                (integerp width))
           (equal (getbit n (logmask width))
                  (if (< n width)
                      1
                    0))))

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

(defthmd bvchop-of---becomes-bvminus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (- x y))
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvminus))))

;; We only need to get the size of one argument for logand
(defthm logand-becomes-bvand
  (implies (and (bind-free (bind-var-to-bv-term-size 'size x))
                (unsigned-byte-p-forced size x)
                (integerp y))
           (equal (logand x y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand logand-of-bvchop))))

(defthm logand-becomes-bvand-alt
  (implies (and (bind-free (bind-var-to-bv-term-size 'size y))
                (unsigned-byte-p-forced size y)
                (integerp x))
           (equal (logand x y)
                  (bvand size x y)))
  :hints (("Goal" :use (:instance logand-becomes-bvand (x y) (y x))
           :in-theory (disable logand-becomes-bvand))))

(defthmd logand-of-bvchop-becomes-bvand
  (equal (logand y (bvchop width x))
         (bvand width y x))
  :hints (("Goal" :use (:instance logand-becomes-bvand (size width) (x (bvchop width x)))
           :in-theory (disable logand-becomes-bvand))))

(defthmd logand-of-bvchop-becomes-bvand-alt
  (equal (logand (bvchop width x) y)
         (bvand width y x))
  :hints (("Goal" :use (:instance logand-becomes-bvand (size width) (x (bvchop width x)))
           :in-theory (disable logand-becomes-bvand))))

;; We only need to get the size of one argument for logand
(defthmd logand-becomes-bvand-when-unsigned-byte-p-arg1
  (implies (and (unsigned-byte-p size x) ;free var
                (unsigned-byte-p size y)
                (integerp y))
           (equal (logand x y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand logand-of-bvchop))))

;; We only need to get the size of one argument for logand
(defthmd logand-becomes-bvand-when-unsigned-byte-p-arg2
  (implies (and (unsigned-byte-p size y) ;free var
                (unsigned-byte-p size x)
                (integerp y))
           (equal (logand x y)
                  (bvand size x y)))
  :hints (("Goal" :in-theory (enable bvand logand-of-bvchop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd logapp-becomes-bvcat-when-unsigned-byte-p-1
  (implies (unsigned-byte-p 1 j)
           (equal (logapp size i j)
                  (bvcat 1 j size i)))
  :hints (("Goal" :in-theory (enable bvcat))))

;; logapp does not indicate the size of the high bits, so we have to try to
;; figure it out.
(defthmd logapp-becomes-bvcat-when-bv
  (implies (and (bind-free (bind-var-to-bv-term-size 'jsize j) (jsize))
                (unsigned-byte-p-forced jsize j))
           (equal (logapp size i j)
                  (bvcat jsize j size i)))
  :hints (("Goal" :in-theory (enable bvcat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm ash-of-bvchop-becomes-bvcat
  (implies (and (natp amt)
                (natp xsize))
           (equal (ash (bvchop xsize x) amt)
                  (bvcat (+ xsize amt)
                         (bvchop xsize x)
                         amt
                         0)))
  :hints (("Goal" :in-theory (enable bvcat ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvif-of---arg3
  (implies (integerp x)
           (equal (bvif size test (- x) z)
                  (bvif size test (bvuminus size x) z)))
  :hints (("Goal" :in-theory (enable bvif bvuminus bvminus))))

(defthm bvif-of---arg4
  (implies (integerp x)
           (equal (bvif size test z (- x))
                  (bvif size test z (bvuminus size x))))
  :hints (("Goal" :in-theory (enable bvif bvuminus bvminus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; replace with a general rule?
(defthm bvplus-of-logext-arg2-convert-to-bv
  (implies (and (< size2 size) ; could allow =
                (integerp size)
                (posp size2))
           (equal (bvplus size (logext size2 x) y)
                  (bvplus size (bvsx size size2 x) y)))
  :hints (("Goal" :cases ((equal size size2)))))

;; replace with a general rule?
(defthm bvplus-of-logext-arg3-convert-to-bv
  (implies (and (< size2 size) ; could allow =
                (integerp size)
                (posp size2))
           (equal (bvplus size x (logext size2 y))
                  (bvplus size x (bvsx size size2 y))))
  :hints (("Goal" :cases ((equal size size2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; replace with a general rule?
(defthm bvminus-of-logext-arg2-convert-to-bv
  (implies (and (< size2 size) ; could allow =
                (integerp size)
                (posp size2))
           (equal (bvminus size (logext size2 x) y)
                  (bvminus size (bvsx size size2 x) y)))
  :hints (("Goal" :cases ((equal size size2)))))

;; replace with a general rule?
(defthm bvminus-of-logext-arg3-convert-to-bv
  (implies (and (< size2 size) ; could allow =
                (integerp size)
                (posp size2))
           (equal (bvminus size x (logext size2 y))
                  (bvminus size x (bvsx size size2 y))))
  :hints (("Goal" :cases ((equal size size2)))))
