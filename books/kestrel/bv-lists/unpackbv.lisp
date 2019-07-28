; BV Lists Library: unpackbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility for unpacking (i.e., diassembling) larger bit
;; vectors into smaller bit vectors.  The smaller bit vectors can of course be
;; single bits.

(include-book "all-unsigned-byte-p")
(include-book "../bv/bvcat")
(local (include-book "../../ihs/ihs-lemmas")) ;why?
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/cons"))

;num is the number of chunks, size is the number of bits per chunk.
;The higher bits of BV come first in the result.
(defund unpackbv (num size bv)
  (declare (type (integer 0 *) size) ;todo: disallow 0?
           (type (integer 0 *) num)
           (type integer bv))
  (if (zp num)
      nil
    (cons (slice (+ -1 (* num size))
                 (* (+ -1 num) size)
                 bv)
          (unpackbv (+ -1 num) size bv))))

(defthm true-listp-of-unpackbv
  (true-listp (unpackbv num size bv)))

(defthm all-integerp-of-unpackbv
  (all-integerp (unpackbv num size bv))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm consp-of-unpackbv
  (equal (consp (unpackbv num size bv))
         (posp num))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthmd unpackbv-opener
  (implies (not (zp num))
           (equal (unpackbv num size bv)
                  (cons (slice (+ -1 (* num size))
                               (* (+ -1 num) size)
                               bv)
                        (unpackbv (+ -1 num) size bv))))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm unpackbv-when-zp
  (implies (zp num)
           (equal (unpackbv num size bv)
                  nil))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm unpackbv-when-not-integerp
  (implies (and (syntaxp (not (and (quotep bv)
                                   (eql 0 (unquote bv)))))
                (not (integerp bv)))
           (equal (unpackbv num size bv)
                  (unpackbv num size 0)))
 :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm all-unsigned-byte-p-of-unpackbv
  (implies (natp size)
           (all-unsigned-byte-p size (unpackbv num size bv)))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm len-of-unpackbv
  (implies (natp num)
           (equal (len (unpackbv num size bv))
                  num))
  :hints (("Goal" :in-theory (enable unpackbv))))

;fixme use trim?
(defthm unpackbv-of-bvcat-irrel
  (implies (and (<= (* size num) size2)
                (posp size)
                (natp num)
                (natp size2)
                (natp size1))
           (equal (unpackbv num size (bvcat size1 item size2 item2))
                  (unpackbv num size item2)))
  :hints (("Goal" :in-theory (enable unpackbv))))

(local
 (defun induct-for-nth-of-unpackbv (n count)
  (if (zp count)
      (list n count)
    (induct-for-nth-of-unpackbv (+ -1 n) (+ -1 count)))))

(defthm nth-of-unpackbv
  (implies (and (< n count)
                (natp n)
                (posp size)
                (natp count))
           (equal (nth n (unpackbv count size bv))
                  (slice (+ -1 (* size (+ count (- n))))
                         (+ (- size) (* size (+ count (- n))))
                         bv)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (induct-for-nth-of-unpackbv n count)
           :in-theory (enable unpackbv nth))))
(local
 (defun double-sub1-induct (m n)
  (if (or (zp m)
          (zp n))
      (list m n)
    (double-sub1-induct (+ -1 m) (+ -1 n)))))

;todo: gen
(defthm take-of-unpackbv-of-8
  (implies (and (<= m n)
                (natp n)
                (natp m))
           (equal (take m (unpackbv n 8 val))
                  (unpackbv m 8 (logtail (* 8 (- n m)) val))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (unpackbv n 8 val)
           :induct (double-sub1-induct m n)
           :in-theory (enable unpackbv))))

(defthm take-of-unpackbv-of-1
  (implies (and (natp n)
                (<= n num)
                (natp num))
           (equal (take n (unpackbv num 1 bv))
                  (unpackbv n 1 (logtail (- num n) bv))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (double-sub1-induct n num)
           :in-theory (enable unpackbv take))))

(defthm nthcdr-of-unpackbv
  (implies (and (<= n num)
                (natp n))
           (equal (nthcdr n (unpackbv num 1 x))
                  (unpackbv (- num n) 1 x)))
  :hints (("Goal" :induct (unpackbv num 1 x)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable unpackbv
                              zp
                              cdr-of-nthcdr))))

(defthm cdr-of-unpackbv
  (implies (posp num)
           (equal (cdr (unpackbv num 1 x))
                  (unpackbv (+ -1 num) 1 x)))
  :hints (("Goal" :induct (unpackbv num 1 x)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable unpackbv))))

(defthm unpackbv-of-1
  (implies (integerp size)
           (equal (unpackbv 1 size x)
                  (list (bvchop size x))))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm car-of-unpackbv
  (implies (and (posp num)
                (posp size))
           (equal (car (unpackbv num size bv))
                  (slice (+ -1 (* size num))
                         (+ (- size) (* size num))
                         bv)))
  :hints (("Goal" :expand ((unpackbv num size bv)))))

(defthm unpackbv-non-nil
  (implies (posp num)
           (unpackbv num size bv))
  :hints (("Goal" :in-theory (enable unpackbv))))

(defthm unpackbv-of-bvchop
  (implies (and (<= (* num size) n)
                (natp n)
                (posp size)
                (natp num))
           (equal (unpackbv num size (bvchop n val))
                  (unpackbv num size val)))
  :hints (("Goal" :in-theory (enable unpackbv))))
