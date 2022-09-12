; Rules about trim
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "trim")
(include-book "bvsx")
(include-book "leftrotate32")
(include-book "bvnot")
(include-book "bvplus")
(include-book "bvmult")
(include-book "bvminus")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvif")
(local (include-book "bvcat-rules"))
(local (include-book "repeatbit2"))
(local (include-book "getbit"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defthm trim-of-bvchop
  (equal (trim size1 (bvchop size i))
         (if (< (ifix size1) (ifix size))
             (bvchop size1 i)
           (bvchop size i)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-slice
  (implies (and (natp n)
                (natp high)
                (natp low))
           (equal (trim n (slice high low x))
                  (if (<= n (+ 1 (- high low)))
                      (slice (+ -1 n low) low x)
                    (slice high low x))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvcat
  (implies (and (natp n)
                (natp lowsize)
                (natp highsize))
           (equal (trim n (bvcat highsize highval lowsize lowval))
                  (if (<= n lowsize)
                      (bvchop n lowval) ;don't want to leave a trim (e.g. around a variable)
                    (bvcat (min (binary-+ n (unary-- lowsize))
                                highsize)
                           highval lowsize lowval))))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvnot
  (implies (and (<= n size)
                (natp n)
                (natp size))
           (equal (trim n (bvnot size val))
                  (bvnot n val)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvand
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvand size2 y z))
                  (bvand size1 y z)))
  :hints (("Goal" :in-theory (e/d ( trim) nil))))

(defthm trim-of-bvor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvor size2 y z))
                  (bvor size1 y z)))
  :hints (("Goal" :in-theory (enable trim)))) ;bozo

(defthm trim-of-bvxor
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvxor size2 y z))
                  (bvxor size1 y z)))
  :hints (("Goal" :in-theory (enable trim))))

(defthm trim-of-bvplus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvplus size2 x y))
                  (bvplus size1 x y)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))

(defthm trim-of-bvminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvminus size2 y z))
                  (bvminus size1 y z)))
  :hints (("Goal" :in-theory (e/d (bvuminus trim) (BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

(defthm trim-of-bvuminus
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvuminus size2 x))
                  (bvuminus size1 x)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))

(defthm trim-of-bvmult
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvmult size2 y z))
                  (bvmult size1 y z)))
  :hints (("Goal" :in-theory (e/d ( trim) nil))))

(defthm trim-of-bvsx
  (implies (and (<= n new-size)
                (natp n)
                (natp new-size)
                (posp old-size))
           (equal (trim n (bvsx new-size old-size val))
                  (if (<= old-size n)
                      (bvsx n old-size val)
                    (bvchop N VAL))))
  :hints (("Goal" :in-theory (enable trim bvsx))))

;; only do this if amount and size are constants?
(defthmd trim-of-leftrotate32
  (implies (and (<= size 32)
                (<= amount 32)
                (natp size)
                (natp amount))
           (equal (trim size (leftrotate32 amount val))
                  (if (< amount size)
                      (bvcat (- size amount)
                             val
                             amount
                             (SLICE (+ -1 32)
                                    (+ (- AMOUNT) 32)
                                    VAL) )
                    (slice (+ -1 (- AMOUNT) SIZE 32)
                           (+ (- AMOUNT) 32)
                           val))))
  :hints (("Goal" :in-theory (enable trim bvchop-of-leftrotate32-both))))

;todo: add full trim support for rotate ops
;todo: only do this if the amt is a constant?
(defthmd trim-of-1-and-leftrotate
  (implies (and (< amt width) ; avoids mod in rhs
                (natp amt)
                (natp width))
           (equal (trim 1 (leftrotate width amt x))
                  (if (< 0 width)
                      (if (< 0 amt) ; this case
                          (getbit (+ width (- amt)) x)
                        (getbit amt x))
                    0)))
  :hints (("Goal" :in-theory (enable trim leftrotate))))

(defthm trim-of-repeatbit
  (equal (trim size1 (repeatbit size i))
         (if (< (ifix size1) (ifix size))
             (repeatbit size1 i)
             (repeatbit size i)))
  :hints (("Goal" :in-theory (e/d (trim repeatbit)
                                  (bvplus-recollapse)))))

;; ;not true?
;; (defthm bvchop-of-bvdiv2
;;   (implies (and (<= size1 size2)
;;                 (natp size2)
;;                 (natp size1))
;;            (equal (bvchop size1 (bvdiv size2 x y))
;;                   (bvdiv size1 x y)))
;;   :hints (("Goal" :in-theory (enable bvdiv))))

;; ;not true?
;; (defthm trim-of-bvdiv
;;   (implies (and (<= size1 size2)
;;                 (natp size2)
;;                 (natp size1))
;;            (equal (trim size1 (bvdiv size2 x y))
;;                   (bvdiv size1 x y)))
;;   :hints (("Goal" :in-theory (enable))))

(defthm trim-of-bvif
  (implies (and (<= size1 size2)
                (natp size1)
                (natp size2))
           (equal (trim size1 (bvif size2 test x y))
                  (bvif size1 test x y)))
  :hints (("Goal" :in-theory (e/d (trim) nil))))
