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
(local (include-book "kestrel/lists-light/take" :dir :system))

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
                              (true-listp data))
                  :type-prescription (natp (bv-array-read element-size len index data))))
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

(defthm bv-array-read-of-bvchop-helper
  (implies (and (<= m n)
                (natp n)
                (natp m))
           (equal (BV-ARRAY-READ size (expt 2 m) (BVCHOP n INDEX) VALS)
                  (BV-ARRAY-READ size (expt 2 m) INDEX VALS)))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))

(defthm bv-array-read-of-bvchop
  (implies (and (equal len (expt 2 (+ -1 (integer-length len)))) ;len is a power of 2
                (<= (+ -1 (integer-length len)) n)
                (natp len)
                (natp n))
           (equal (bv-array-read size len (bvchop n index) vals)
                  (bv-array-read size len index vals)))
  :hints (("Goal" :in-theory (disable bv-array-read-of-bvchop-helper
                                      ;collect-constants-times-equal ;fixme
                                      )
           :use (:instance bv-array-read-of-bvchop-helper (m (+ -1 (integer-length len)))))))

;or do we want to go to nth?
(defthm bv-array-read-of-take
  (implies (posp len)
           (equal (bv-array-read elem-size len index (take len array))
                  (bv-array-read elem-size len index array)))
  :hints (("Goal" :cases ((posp len))
           :in-theory (enable bv-array-read))))

;kind of gross to mix theories like this?
(defthm bv-array-read-of-cons
  (implies (and (natp len)
                (< 0 index)
                (< index len)
                (natp index))
           (equal (BV-ARRAY-READ element-size len index (cons a b))
                  (BV-ARRAY-READ element-size (+ -1 len) (+ -1 index) b)))
  :hints (("Goal"
           :cases ((equal index (+ -1 len)))
           :in-theory (enable ;LIST::NTH-OF-CONS
                       bv-array-read unsigned-byte-p-of-integer-length-gen ceiling-of-lg))))

(defthm bv-array-read-of-cons-base
  (implies (and (natp len)
                (< 0 len) ;new!
                )
           (equal (BV-ARRAY-READ element-size len 0 (cons a b))
                  (bvchop element-size a)))
  :hints (("Goal" :in-theory (enable ;LIST::NTH-OF-CONS
                              BVCHOP-WHEN-I-IS-NOT-AN-INTEGER bv-array-read))))

(defthm bv-array-read-of-cons-both
  (implies (and (syntaxp (not (and (quotep a)  ;prevent application to a constant array
                                   (quotep b))))
                (natp len)
                ;(< 0 index)
                (< index len)
                (natp index))
           (equal (bv-array-read element-size len index (cons a b))
                  (if (equal 0 index)
                      (bvchop element-size a)
                    (bv-array-read element-size (+ -1 len) (+ -1 index) b)))))

;; Reading from an array of length 1 always gives the 0th element (and is in
;; fact independent from the index).
;drop this one?
(defthmd bv-array-read-of-1-arg2
  (equal (bv-array-read element-size 1 index data)
         (bvchop element-size (nth 0 data)))
  :hints (("Goal" :in-theory (enable bv-array-read))))

;; the index gets chopped down to 0 bits
;todo: maybe enable
(defthmd bv-array-read-of-1-arg2-better
  (implies (< 0 index) ;prevents loops (could also do a syntactic check against '0 but not for axe?)
           (equal (bv-array-read element-size 1 index data)
                  (bv-array-read element-size 1 0 data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

(defthm bv-array-read-of-nil
  (equal (bv-array-read width len index nil)
         0)
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

(defthm bv-array-read-of-0-arg2
  (equal (bv-array-read size 0 index data)
         0)
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))
