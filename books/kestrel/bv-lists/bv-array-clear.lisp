; Clearing values in bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "bv-array-write")
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
(local (include-book "all-unsigned-byte-p2"))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/all-equal-dollar2" :dir :system)) ;for ALL-EQUAL$-WHEN-TRUE-LISTP

(defund bv-array-clear (element-size len index data)
  (declare (xargs :guard (and (natp len)
                              (natp index)
                              (ALL-INTEGERP data)
                              (<= len (len data))
                              (< index (len data))
                              (natp element-size)
                              (true-listp data))))
  (bv-array-write element-size len index 0 data))

(defthm true-listp-of-bv-array-clear
  (true-listp (bv-array-clear element-size len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

;analogues of the bv-array-write theorems?

(defthm len-of-bv-array-clear
  (equal (len (bv-array-clear element-size len key lst))
         (nfix len))
  :hints (("Goal" :in-theory (e/d (bv-array-clear) ()))))

(defthm all-integerp-of-bv-array-clear
  (all-integerp (bv-array-clear element-size len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-clear-1-0
  (equal (bv-array-clear width 1 0 data)
         '(0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear update-nth2 ;list::clear-nth
                                                  )
                                  (;LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
                                   ;;LIST::UPDATE-NTH-EQUAL-REWRITE
                                   )))))

(defun bv-array-clear-range (esize len lowindex highindex data)
  (declare (xargs :measure (+ 1 (nfix (+ 1 (- highindex lowindex))))
                  :guard (and (true-listp data)
                              (all-integerp data)
                              (natp len)
                              (<= LEN (LEN DATA))
                              (natp esize)
                              (rationalp highindex)
                              (rationalp lowindex)
                              (< highindex len))
                  :verify-guards nil ;done below
                  ))
  (if (or (not (natp highindex))
          (not (natp lowindex))
          (> lowindex highindex))
      (bvchop-list esize (take len data)) ;was data
    (bv-array-clear esize len lowindex (bv-array-clear-range esize len (+ 1 lowindex) highindex data))))

(defthm len-of-bv-array-clear-range
  (equal (len (bv-array-clear-range esize len lowindex highindex data))
         (nfix len)))

(defthm all-integerp-of-bv-array-clear-range
  (all-integerp (bv-array-clear-range esize len lowindex highindex data)))

(verify-guards bv-array-clear-range :hints (("Goal" :do-not-induct t)))

(defthm bv-array-clear-of-repeat-same
  (equal (bv-array-clear 8 len start (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :in-theory (e/d (;update-nth-when-equal-of-nth
                                   bv-array-clear
                                   bv-array-write ;fixme
                                   update-nth2
                                   )
                                  ()))))

(defthm bv-array-clear-range-of-repeat-same
  (equal (bv-array-clear-range '8 len start end (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

;restrict to constants?
(defthm bv-array-clear-range-of-zeros
  (implies (and (all-equal$ 0 data)
                (true-listp data)
                (equal len (len data)))
           (equal (bv-array-clear-range '8 len start end data)
                  data))
  :hints (("Goal" :use (:instance bv-array-clear-range-of-repeat-same)
           :in-theory (e/d (ALL-EQUAL$-WHEN-TRUE-LISTP)
                           (bv-array-clear-range-of-repeat-same)))))
