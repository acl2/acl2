; A function to write to an array of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/update-nth2" :dir :system)
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "bvchop-list")
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system)) ;for UNSIGNED-BYTE-P-INTEGER-LENGTH-ONE-LESS

;; Writes VAL, which should be a BV of size ELEMENT-SIZE, at position INDEX of
;; DATA, which should be a bv-array of length LEN whose elements are BVs of
;; size ELEMENT-SIZE.  The INDEX should be less than LEN.  This function chops
;; the index, to follow the convention that BV functions chop their
;; arguments. If the trimmed index is out-of-bounds, this has no effect
;; (because of the call to update-nth2).  Don't change this behavior unless you
;; also change how bv-array-write calls are translated to STP.
(defund bv-array-write (element-size len index val data)
  (declare (xargs :guard (and (natp len)
                              (natp index)
                              ;(all-integerp data)
                              ;(<= len (len data)) ;would like to drop..
                              ;(< index (len data))
                              ;(integerp val)
                              (natp element-size)
                              (true-listp data))
                  :guard-hints (("Goal" :in-theory (enable update-nth2)))))
  (let* ((len (nfix len))
         (numbits (ceiling-of-lg len))
         (index (bvchop numbits (ifix index))))
        (bvchop-list element-size ;; the bvchop-list is often wasted work
                ;this calls take, but in many cases that is wasted work:
                (update-nth2 len index val data))))

;for axe?
(defthm true-listp-of-bv-array-write
  (true-listp (bv-array-write element-size len key val lst)))

(defthm all-integerp-of-bv-array-write
  (all-integerp (bv-array-write element-size len key val lst))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthmd bv-array-write-normal-case
  (implies (and (natp index)
                (< index len)
                (equal len (len data)))
           (equal (bv-array-write element-size len index val data)
                  (bvchop-list element-size (update-nth index val data))))
  :hints (("Goal" :in-theory (enable bv-array-write ceiling-of-lg update-nth2))))

(defthm len-of-bv-array-write
  (equal (len (bv-array-write element-size len key val lst))
         (nfix len))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) ()))))

(defthm consp-of-bv-array-write
  (implies (natp len)
           (equal (consp (bv-array-write element-size len key val lst))
                  (< 0 (nfix len))))
  :hints (("Goal" :in-theory (enable UPDATE-NTH2 bv-array-write))))

(defthm all-unsigned-byte-p-of-bv-array-write-same
    (implies (natp size)
             (all-unsigned-byte-p size (bv-array-write size len key val lst)))
 :hints (("Goal" :cases ((natp size))
          :in-theory (enable bv-array-write))))

(defthm all-unsigned-byte-p-of-bv-array-write
  (implies (and (<= element-size size)
                (integerp size)
                (natp element-size))
           (all-unsigned-byte-p size (bv-array-write element-size len key val lst)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthm bv-array-write-iff
  (iff (bv-array-write element-size len index val data)
       (posp len))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;For Axe
(defthmd equal-of-nil-and-bv-array-write
  (equal (equal nil (bv-array-write element-size len index val data))
         (not (posp len)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;; Probably only needed for Axe since ACL2 will use equal-of-nil-and-bv-array-write.
(defthmd equal-of-bv-array-write-and-nil
  (equal (equal (bv-array-write element-size len index val data) nil)
         (not (posp len)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthm bv-array-write-of-0
  (equal (bv-array-write width 0 index val x)
         nil)
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthmd bv-array-write-opener
  (implies (and (natp index)
                (< index len)
                (natp len))
           (equal (bv-array-write element-size len index val data)
                  (bvchop-list element-size
                ;this calls take, but in many cases that is wasted work:
                (update-nth2 len index val data))))
  :hints (("Goal" :in-theory (enable bv-array-write ceiling-of-lg))))

(defthm bv-array-write-when-index-not-integer-cheap
  (implies (not (integerp index))
           (equal (bv-array-write element-size len index val data)
                  (bv-array-write element-size len 0 val data)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) ()))))

;;Do not remove.  This helps justify te correctness of the translation to STP.
;a write out of bounds has essentially no effect
;note that the index is chopped down before the comparison
(defthmd bv-array-write-when-index-is-too-large
  (implies (and (<= len (bvchop (ceiling-of-lg len) index))
                (natp len))
           (equal (bv-array-write width len index value data)
                  (bvchop-list width (take len data))))
  :hints (("Goal" :in-theory (e/d (bv-array-write) ()))))

;; A bv-array-write to an array of length 1 always acts as if the index is 0,
;; The result does not depend on the original contents of the array,
;; because the single element gets overwritten.
(defthm bv-array-write-of-1-arg2
  (implies (syntaxp (not (equal index ''0))) ;prevents loops
           (equal (bv-array-write size 1 index val data)
                  (bv-array-write size 1 0 val '(0))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                                  ( ;update-nth-becomes-update-nth2-extend-gen
                                   ;LIST::UPDATE-NTH-EQUAL-REWRITE
                                   ;LIST::UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE
                                   )))))

(defthm bv-array-write-when-len-is-not-natp
  (implies (not (natp len))
           (equal (bv-array-write element-size len index val data)
                  nil))
  :hints (("Goal" :in-theory (enable bv-array-write))))
