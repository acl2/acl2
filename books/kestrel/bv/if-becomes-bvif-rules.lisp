; Rules about that turn IF into BVIF inside BV ops
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bitnot")
(include-book "bitand")
(include-book "bitor")
(include-book "bitxor")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvmult")
(include-book "bvcat")
(include-book "bvif")
(include-book "bvsx")
(include-book "bvdiv")
(include-book "bvmod")
(include-book "sbvlt")
(include-book "sbvdiv")
(include-book "sbvrem")
(local (include-book "bvlt"))
(local (include-book "repeatbit"))

;; TODO: Add rules for bv-array operators?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvchop-of-if-becomes-bvif
  (equal (bvchop size (if test x1 x2))
         (bvif size test x1 x2))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd slice-of-if-becomes-slice-of-bvif
  (implies (and (natp low)
                (natp high))
           (equal (slice high low (if test x1 x2))
                  (slice high low (bvif (+ 1 high) test x1 x2))))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvcat-of-if-becomes-bvcat-of-bvif-arg2
  (equal (bvcat highsize (if test highval1 highval2) lowsize lowval)
         (bvcat highsize (bvif highsize test highval1 highval2) lowsize lowval)))

(defthmd bvcat-of-if-becomes-bvcat-of-bvif-arg4
  (equal (bvcat highsize highval lowsize (if test lowval1 lowval2))
         (bvcat highsize highval lowsize (bvif lowsize test lowval1 lowval2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd getbit-of-if-becomes-getbit-of-bvif
  (implies (natp n)
           (equal (getbit n (if test x1 x2))
                  (getbit n (bvif (+ 1 n) test x1 x2))))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bitand-of-if-becomes-bitand-of-bvif-arg1
  (equal (bitand (if test x1 x2) y)
         (bitand (bvif 1 test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bitand-of-if-becomes-bitand-of-bvif-arg2
  (equal (bitand x (if test y1 y2))
         (bitand x (bvif 1 test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bitor-of-if-becomes-bitor-of-bvif-arg1
  (equal (bitor (if test x1 x2) y)
         (bitor (bvif 1 test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bitor-of-if-becomes-bitor-of-bvif-arg2
  (equal (bitor x (if test y1 y2))
         (bitor x (bvif 1 test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bitxor-of-if-becomes-bitxor-of-bvif-arg1
  (equal (bitxor (if test x1 x2) y)
         (bitxor (bvif 1 test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bitxor-of-if-becomes-bitxor-of-bvif-arg2
  (equal (bitxor x (if test y1 y2))
         (bitxor x (bvif 1 test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Or we could push the bitnot into each branch
(defthmd bitnot-of-if-becomes-bitnot-of-bvif
  (equal (bitnot (if test x1 x2))
         (bitnot (bvif 1 test x1 x2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvand-of-if-becomes-bvand-of-bvif-arg2
  (equal (bvand size (if test x1 x2) y)
         (bvand size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvand-of-if-becomes-bvand-of-bvif-arg3
  (equal (bvand size x (if test y1 y2))
         (bvand size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvor-of-if-becomes-bvor-of-bvif-arg2
  (equal (bvor size (if test x1 x2) y)
         (bvor size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvor-of-if-becomes-bvor-of-bvif-arg3
  (equal (bvor size x (if test y1 y2))
         (bvor size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvxor-of-if-becomes-bvxor-of-bvif-arg2
  (equal (bvxor size (if test x1 x2) y)
         (bvxor size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvxor-of-if-becomes-bvxor-of-bvif-arg3
  (equal (bvxor size x (if test y1 y2))
         (bvxor size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Or we could push the bvnot into each branch
(defthmd bvnot-of-if-becomes-bvnot-of-bvif
  (equal (bvnot size (if test x1 x2))
         (bvnot size (bvif size test x1 x2)))
  :hints (("Goal" :in-theory (enable bvif))))

;; Or we could push the bvuminus into each branch
(defthmd bvuminus-of-if-becomes-bvuminus-of-bvif
  (equal (bvuminus size (if test x1 x2))
         (bvuminus size (bvif size test x1 x2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvplus-of-if-becomes-bvplus-of-bvif-arg2
  (equal (bvplus size (if test x1 x2) y)
         (bvplus size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvplus-of-if-becomes-bvplus-of-bvif-arg3
  (equal (bvplus size x (if test y1 y2))
         (bvplus size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvminus-of-if-becomes-bvminus-of-bvif-arg2
  (equal (bvminus size (if test x1 x2) y)
         (bvminus size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvminus-of-if-becomes-bvminus-of-bvif-arg3
  (equal (bvminus size x (if test y1 y2))
         (bvminus size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvmult-of-if-becomes-bvmult-of-bvif-arg2
  (equal (bvmult size (if test x1 x2) y)
         (bvmult size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvmult-of-if-becomes-bvmult-of-bvif-arg3
  (equal (bvmult size x (if test y1 y2))
         (bvmult size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvdiv-of-if-becomes-bvdiv-of-bvif-arg2
  (equal (bvdiv size (if test x1 x2) y)
         (bvdiv size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvdiv-of-if-becomes-bvdiv-of-bvif-arg3
  (equal (bvdiv size x (if test y1 y2))
         (bvdiv size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvmod-of-if-becomes-bvmod-of-bvif-arg2
  (equal (bvmod size (if test x1 x2) y)
         (bvmod size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvmod-of-if-becomes-bvmod-of-bvif-arg3
  (equal (bvmod size x (if test y1 y2))
         (bvmod size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvdiv-of-if-becomes-sbvdiv-of-bvif-arg2
  (implies (posp size)
           (equal (sbvdiv size (if test x1 x2) y)
                  (sbvdiv size (bvif size test x1 x2) y)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvdiv-of-if-becomes-sbvdiv-of-bvif-arg3
  (implies (posp size)
           (equal (sbvdiv size x (if test y1 y2))
                  (sbvdiv size x (bvif size test y1 y2))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvrem-of-if-becomes-sbvrem-of-bvif-arg2
  (implies (posp size)
           (equal (sbvrem size (if test x1 x2) y)
                  (sbvrem size (bvif size test x1 x2) y)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvrem-of-if-becomes-sbvrem-of-bvif-arg3
  (implies (posp size)
           (equal (sbvrem size x (if test y1 y2))
                  (sbvrem size x (bvif size test y1 y2))))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvlt-of-if-becomes-bvlt-of-bvif-arg2
  (equal (bvlt size (if test x1 x2) y)
         (bvlt size (bvif size test x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvlt-of-if-becomes-bvlt-of-bvif-arg3
  (equal (bvlt size x (if test y1 y2))
         (bvlt size x (bvif size test y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvlt-of-if-becomes-sbvlt-of-bvif-arg2
  (implies (posp size) ; gen?
           (equal (sbvlt size (if test x1 x2) y)
                  (sbvlt size (bvif size test x1 x2) y)))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd sbvlt-of-if-becomes-sbvlt-of-bvif-arg3
  (implies (posp size) ; gen?
           (equal (sbvlt size x (if test y1 y2))
                  (sbvlt size x (bvif size test y1 y2))))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvif-of-if-becomes-bvif-of-bvif-arg3
  (equal (bvif size test (if test2 x1 x2) y)
         (bvif size test (bvif size test2 x1 x2) y))
  :hints (("Goal" :in-theory (enable bvif))))

(defthmd bvif-of-if-becomes-bvif-of-bvif-arg4
  (equal (bvif size test x (if test2 y1 y2))
         (bvif size test x (bvif size test2 y1 y2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd bvsx-of-if-becomes-bvsx-of-bvif-arg3
  (implies (and (posp old-size) ; gen?
                (natp new-size))
           (equal (bvsx new-size old-size (if test val1 val2))
                  (bvsx new-size old-size (bvif old-size test val1 val2))))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd repeatbit-of-if-becomes-repeatbit-of-bvif-arg2
  (equal (repeatbit n (if test bit1 bit2))
         (repeatbit n (bvif 1 test bit1 bit2)))
  :hints (("Goal" :in-theory (enable bvif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
