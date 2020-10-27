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
                (natp len)
                (equal len (len data))
                )
           (equal (bv-array-write element-size len index val data)
                  (bvchop-list element-size (update-nth index val data))))
  :hints (("Goal" :in-theory (enable bv-array-write ceiling-of-lg update-nth2))))
