; A function to read from an array of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system)) ;for UNSIGNED-BYTE-P-INTEGER-LENGTH-ONE-LESS

;; Readd the element at position INDEX of the array DATA, which should be a
;; bv-array of length LEN and have elements that are bit-vectors of size
;; ELEMENT-SIZE.  The INDEX should be less than LEN.  This function chops the
;; index, to follow the convention that BV functions chop their arguments. This
;; function now returns 0 if the trimmed index is too long.  Don't change that
;; behavior without also changing how calls to bv-array-read are translated to
;; STP.
(defund bv-array-read (element-size len index data)
  (declare (xargs :guard (and (natp element-size)
                              (natp len)
                              (integerp index) ;todo: consider natp
                              (true-listp data))))
  (let* ((len (nfix len))
         (numbits (ceiling-of-lg len)) ;number of index bits needed
         ;; Chop the index down to the needed number of bits:
         (index (bvchop numbits (ifix index))))
    (if (< index len) ;; always true when LEN is a power of 2
        (bvchop element-size (ifix ; drop if we change the guard on bvchop
                              (nth index data)))
      0)))

(defthm bv-array-read-of-true-list-fix
  (equal (bv-array-read element-size len index (true-list-fix data))
         (bv-array-read element-size len index data))
  :hints (("Goal" :in-theory (enable bv-array-read))))

(defthmd bv-array-read-opener
  (implies (and (natp index)
                (< index len)
                (natp len))
           (equal (bv-array-read element-size len index data)
                  (bvchop element-size (nth index data))))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))

(defthm unsigned-byte-p-of-bv-array-read-gen
  (implies (and (<= element-size n)
                (natp n)
                (natp element-size))
           (unsigned-byte-p n (bv-array-read element-size len index data)))
  :hints (("Goal" :in-theory (enable bv-array-read))))

(defthm equal-of-bvchop-of-car-and-bv-array-read
  (implies (equal len (len x))
           (equal (equal (bvchop 8 (car x)) (bv-array-read 8 len 0 x))
                  t))
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))
