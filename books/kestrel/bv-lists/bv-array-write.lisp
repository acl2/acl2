; A function to write to an array of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/update-nth2" :dir :system)
(include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system)
(include-book "bvchop-list")
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
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
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

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

(defthm unsigned-byte-listp-of-bv-array-write
  (implies (and (<= size2 size1)
                (integerp size1)
                (natp size2))
           (unsigned-byte-listp size1 (bv-array-write size2 len index val data)))
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
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

;;Do not remove.  This helps justify te correctness of the translation to STP.
;a write out of bounds has essentially no effect
;note that the index is chopped down before the comparison
(defthmd bv-array-write-when-index-is-too-large
  (implies (and (<= len (bvchop (ceiling-of-lg len) index))
                (natp len))
           (equal (bv-array-write width len index value data)
                  (bvchop-list width (take len data))))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;; A bv-array-write to an array of length 1 always acts as if the index is 0,
;; The result does not depend on the original contents of the array,
;; because the single element gets overwritten.
(defthm bv-array-write-of-1-arg2
  (implies (syntaxp (not (equal index ''0))) ;prevents loops
           (equal (bv-array-write size 1 index val data)
                  (bv-array-write size 1 0 val '(0))))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                                  (;update-nth-becomes-update-nth2-extend-gen
                                   )))))

(defthm bv-array-write-when-len-is-not-natp
  (implies (not (natp len))
           (equal (bv-array-write element-size len index val data)
                  nil))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;move
(defthmd equal-of-bv-array-write-of-1
  (equal (equal k (bv-array-write size 1 index val data))
         (and (true-listp k)
              (equal 1 (len k))
              (equal (car k) (bvchop size val))))
  :hints (("Goal"
           :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                           (;update-nth-becomes-update-nth2-extend-gen
                            )))))

;move
(defthm equal-of-bv-array-write-of-1-constant-version
  (implies (syntaxp (quotep k))
           (equal (equal k (bv-array-write size 1 index val data))
                  (and (true-listp k)
                       (equal 1 (len k))
                       (equal (car k) (bvchop size val)))))
  :hints (("Goal"
           :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                           (;update-nth-becomes-update-nth2-extend-gen
                            )))))

;; width is a free var
(defthmd update-nth2-becomes-bv-array-write
  (implies (and (all-unsigned-byte-p width lst)
                (unsigned-byte-p width val)
                ;;new:
                (< key len)
                (natp key)
                (true-listp lst)
                (equal len (len lst))
                )
           (equal (update-nth2 len key val lst)
                  (bv-array-write width len key val lst)))
  :hints (("Goal" :in-theory (enable bv-array-write-opener update-nth2))))

;; width is a free var
(defthmd update-nth-becomes-bv-array-write
  (implies (and (all-unsigned-byte-p width lst)
                (unsigned-byte-p width val)
                (< key (len lst))
                (natp key)
                (true-listp lst))
           (equal (update-nth key val lst)
                  (bv-array-write width (len lst) key val lst)))
  :hints (("Goal" :in-theory (enable bv-array-write-opener update-nth2))))

(defthm bv-array-write-of-true-list-fix
  (equal (bv-array-write elem-size len index val (true-list-fix lst))
         (bv-array-write elem-size len index val lst))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

(defthm bv-array-write-of-bvchop-arg3
  (implies (and (<= (ceiling-of-lg len) size)
                (integerp size))
           (equal (bv-array-write element-size len (bvchop size index) val data)
                  (bv-array-write element-size len index val data)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthm bv-array-write-of-bvchop-arg4
  (implies (and (<= element-size size)
                (integerp size))
           (equal (bv-array-write element-size len index (bvchop size val) data)
                  (bv-array-write element-size len index val data)))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                                                 )))))

(defthm nthcdr-of-bv-array-write-is-nil
  (implies (and (<= len n)
                (integerp len)
                (integerp n))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  nil)))

(defthm bv-array-write-of-bvchop-list
  (equal (bv-array-write elemement-width len index val (bvchop-list elemement-width array))
         (bv-array-write elemement-width len index val array))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2 bvchop-list-of-take-of-bvchop-list))))

(defthm bv-array-write-of-take
  (implies (and (<= len n)
                (natp n))
           (equal (bv-array-write elemement-width len index val (take n array))
                  (bv-array-write elemement-width len index val array)))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2 bvchop-list-of-take-of-bvchop-list take))))

(defthm bv-array-write-of-take-same
  (equal (bv-array-write elemement-width len index val (take len array))
         (bv-array-write elemement-width len index val array))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2 bvchop-list-of-take-of-bvchop-list take))))

;fixme can loop?
(defthmd bv-array-write-of-bv-array-write-diff-helper
  (implies (and ;this is implied by them being unequal nats both of which are in bounds:
             (not (equal (bvchop (integer-length (+ -1 len)) index1)
                         (bvchop (integer-length (+ -1 len)) index2)))
             (natp index1)
             (natp index2))
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))
                  ))
  :hints (("Goal"
           :cases ((equal (bvchop (integer-length (+ -1 len))
                                  index2)
                          (bvchop (integer-length (+ -1 len))
                                  index1)))
           :in-theory (enable update-nth2 ceiling-of-lg bv-array-write))))

;; might loop?
(defthmd bv-array-write-of-bv-array-write-diff
  (implies (and (not (equal index1 index2))
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2))
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))))
  :hints (("Goal" :use bv-array-write-of-bv-array-write-diff-helper
           :cases ((not (natp len)))
           :in-theory (disable bv-array-write-of-bv-array-write-diff-helper))))

;would like this not to mention len, but we have to know that the indices (after trimming down to the number of bits indicated by len) are in fact different.
;; TODO: Maybe we prefer the other order since lower indices are usually done first.
(defthmd bv-array-write-of-bv-array-write-diff-constant-indices
  (implies (and (syntaxp (and (quotep index1)
                              (quotep index2)))
                (< index2 index1) ; prevents loops
                (< index1 len)
                ;; (< index2 len)
                (natp index1)
                (natp index2)
                ;; (natp len) ;drop?
                )
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))
                  ))
  :hints (("Goal" :use bv-array-write-of-bv-array-write-diff
           :cases ((not (natp len)))
           :in-theory (disable bv-array-write-of-bv-array-write-diff))))

;fixme think about how this interacts with the tightening rules...
(defthm bv-array-write-of-bv-array-write-diff-constant-indices-gen
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1) ;only do it when the indices are out of order
                (<= element-size2 element-size1) ;the outer size is bigger
                (< index1 len)
                ;; (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2)
                )
           (equal (bv-array-write element-size1 len index1 val1 (bv-array-write element-size2 len index2 val2 lst))
                  (bv-array-write element-size1 len index2 (bvchop element-size2 val2)
;the bvchop-list should have no affect when lst is a bv-array-write nest with element-size2
                                  (bv-array-write element-size1 len index1 val1 (bvchop-list element-size2 lst)))))
  :hints
  (("Goal" :cases ((<= len (len lst)))
    :in-theory (e/d (update-nth2 bv-array-write-opener
                                 bvchop-list-of-take-of-bvchop-list-gen
                                 )
                    (BVCHOP-LIST-OF-TAKE)))))

(DEFTHMd BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-tighten
  (IMPLIES (AND (< element-size1 element-size2)
                (< INDEX1 LEN)
                (< INDEX2 LEN)
                (equal len (len lst))
                (NATP INDEX1)
                (NATP INDEX2)
                (NATP LEN)
                (NATP ELEMENT-SIZE1)
                (NATP ELEMENT-SIZE2))
           (EQUAL (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX1 VAL1 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX2 VAL2 LST))
                  (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX1 VAL1 (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX2 VAL2 LST))))
  :hints (("Goal" :in-theory (enable update-nth2 LEN-UPDATE-NTH bv-array-write))))

(defthm bvchop-list-of-bv-array-write
  (implies (and (<= size1 size2)
                (natp size1)
                (integerp size2))
           (equal (bvchop-list size1 (bv-array-write size2 len index val lst))
                  (bv-array-write size1 len index val lst)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(defthm bv-array-write-of-bvchop-list-tighten
  (implies (and (unsigned-byte-p width2 val) ;what if this isn't true?
                (< 0 len)
                (integerp len)
                (natp index)
                (< index len)
                (<= width2 width1) ;handle the other case?
                (natp width2)
                (integerp width1)
                (equal len (len lst)) ;gross!
                )
           (equal (bv-array-write width1 len index val (bvchop-list width2 lst))
                  (bv-array-write width2 len index val lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write BVCHOP-WHEN-I-IS-NOT-AN-INTEGER update-nth2)
                                  (;JVM::INT-LEMMA0
                                   )))))

(defthm bv-array-write-of-bv-array-write-same-index
  (implies (and (< index len)
                (natp index)
                (natp len)
                (natp element-size)
                )
           (equal (bv-array-write element-size len index val1 (bv-array-write element-size len index val2 lst))
                  (bv-array-write element-size len index val1 lst)))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

(defthm bv-array-write-of-0-and-bv-array-write-tighter
  (implies (and (< element-size2 element-size1) ;true for = but would loop
                (natp element-size2)
                (natp index2)
                (natp element-size1))
           (equal (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX2 0 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX1 0 LST))
                  (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX2 0 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX1 0 LST))
                  ))
  :hints (("Goal" :cases ((< len (len lst)))
           :in-theory (enable bv-array-write update-nth2))))

; do we need this one?
(defthm bv-array-write-of-0-and-bvchop-list
  (implies (and (<= element-size2 element-size1)
                (natp element-size2)
                (natp index2)
                (natp element-size1))
           (equal (bv-array-write element-size1 len index2 0 (bvchop-list element-size2 lst))
                  (bv-array-write element-size2 len index2 0 lst)))
  :hints (("Goal" :cases ((< len (len lst)))
           :in-theory (enable bv-array-write update-nth2 BVCHOP-LIST-OF-TAKE-OF-BVCHOP-LIST-GEN))))

(defthm bv-array-write-of-bv-array-write-diff-same-val
  (implies (and (syntaxp (smaller-termp index2 index1))
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size))
           (equal (bv-array-write element-size len index1 val (bv-array-write element-size len index2 val lst))
                  (bv-array-write element-size len index2 val (bv-array-write element-size len index1 val lst))))
  :hints
  (("Goal"
    :in-theory (e/d (update-nth2 ;list::update-nth-update-nth-diff
                     bv-array-write)
                    (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     ;BV-ARRAY-WRITE-EQUAL-REWRITE-ALT
                     ;BV-ARRAY-WRITE-EQUAL-REWRITE
                     )))))

(defthmd bv-array-write-tighten-to-1-bit
  (implies (and (< 1 esize)
                (all-unsigned-byte-p 1 data)
                (unsigned-byte-p 1 val)
                (NATP ESIZE)
                (equal len (len data))
                (natp index)
                (true-listp data)
                (< INDEX LEN))
           (equal (bv-array-write esize len index val data)
                  (bv-array-write 1 len index val data)))
  :hints (("Goal" :in-theory (enable UPDATE-NTH2 BV-ARRAY-WRITE))))

(defthm nthcdr-of-bv-array-write
  (implies (and (<= n (len lst))
                (equal (len lst) len) ;bozo
                (< key len)           ;Mon Jul 19 20:28:02 2010
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bvchop-list element-size (nthcdr n (true-list-fix lst)))
                    (bv-array-write element-size (- len n) (- key n) val (nthcdr n lst)))))
  :hints (("Goal" :in-theory (enable UPDATE-NTH2 bv-array-write ceiling-of-lg NTHCDR-of-true-list-fix))))

(defthm nthcdr-of-bv-array-write-better
  (implies (and (<= n len)
                (integerp len)
                ;;(natp len)
                (< key len)
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bvchop-list element-size (nthcdr n (take len (true-list-fix lst))))
                    (bv-array-write element-size (- len n) (- key n) val (nthcdr n lst)))))
  :hints (("Goal"
           :cases ((< key n))
           :in-theory (enable update-nth2 bv-array-write-opener))))

(defthmd bv-array-write-of-bv-array-write-when-length-is-1
  (equal (bv-array-write size 1 index1 val1 (bv-array-write size 1 index2 val2 data))
         (bv-array-write size 1 0 val1 '(0))))

;; breaks the abstraction
(defthm car-of-bv-array-write
  (implies (and ;; (<= 1 len)
                (integerp len)
                (< key len)
                ;(natp len)
                (natp key))
           (equal (car (bv-array-write element-size len key val lst))
                  (if (< key 1)
                      (bvchop element-size val)
                    (bvchop element-size (car lst)))))
  :hints (("Goal" :in-theory (enable bv-array-write-opener update-nth2))))

(defthm car-of-bv-array-write-gen
  (implies (posp len)
           (equal (car (bv-array-write element-size len key val lst))
                  (if (equal 0 (bvchop (ceiling-of-lg len) key))
                      (bvchop element-size val)
                    (bvchop element-size (car lst)))))
  :hints (("Goal" :expand (bv-array-write element-size len key val lst)
           :in-theory (enable update-nth2))))

(defthm cdr-of-bv-array-write-better
  (implies (and (integerp len)
                (< key len)
                (natp key))
           (equal (cdr (bv-array-write element-size len key val lst))
                  (if (zp len)
                      nil
                    (if (< key 1)
                        (bvchop-list element-size (cdr (take len (true-list-fix lst))))
                      (bv-array-write element-size (- len 1) (- key 1) val (nthcdr 1 lst))))))
  :hints (("Goal"
           :cases ((and (< len 0)
                        (< key n))
                   (and (not (< len 0))
                        (< key n))
                   (and (< len 0)
                        (not (< key n)))
                   (and (not (< len 0))
                        (not (< key n))))
           :in-theory (e/d (update-nth2 bv-array-write-opener
                            ;bv-array-write
                            ) (ceiling-of-lg
                               update-nth-becomes-update-nth2-extend-gen)))))

(defthmd bv-array-write-redef-special
  (implies (and (equal len (len data)) ; this case
                (< index len)
                (natp len)
                (natp index))
           (equal (bv-array-write element-size len index val data)
                  (append (bvchop-list element-size (take index data))
                          (list (bvchop element-size val))
                          (bvchop-list element-size (nthcdr (+ 1 index) data)))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2
                                     equal-of-append
                                     cdr-of-nthcdr))))

(defthmd bv-array-write-redef
  (implies (and (< index len)
                (natp len)
                (natp index))
           (equal (bv-array-write element-size len index val data)
                  (append (bvchop-list element-size (take index data))
                          (list (bvchop element-size val))
                          (bvchop-list element-size (take (+ -1 (- index) len) (nthcdr (+ 1 index) data))))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2
                                     equal-of-append
                                     cdr-of-nthcdr))))
