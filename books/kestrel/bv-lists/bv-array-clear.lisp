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
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/take2" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
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

(defthm nth-of-bv-array-clear
  (implies (and (< n len)
                (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg) ()))))

(defthm nth-of-bv-array-clear-better
  (implies (and (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  (if (< n len)
                      0
                    nil)))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write ceiling-of-lg update-nth2)
         ()))))

(defthm nth-of-bv-array-clear-diff
  (implies (and (natp len)
                (natp n)
                (natp index)
;                (natp elem-size)
                (< n len)
                (< index len) ;Mon Jul 19 20:50:11 2010
                (not (equal n index))
                )
           (equal (nth n (bv-array-clear elem-size len index lst))
                  (bvchop elem-size (nth n lst))))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write-opener update-nth2)
         ()))))

(defthm nth-of-bv-array-clear-both
  (implies (and (natp len)
                (natp n)
                (natp index)
                (< index len) ;Mon Jul 19 20:50:11 2010
                (< n len)
                )
           (equal (nth n (bv-array-clear elem-size len index lst))
                  (if (equal n index)
                      0
                  (bvchop elem-size (nth n lst)))))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write-opener update-nth2)
         ()))))

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

(defthm BV-ARRAY-CLEAR-RANGE-of-true-list-fix
  (implies (and (<= lowindex highindex)
                (natp lowindex)
                (natp highindex))
           (equal (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len lowindex highindex (TRUE-LIST-FIX LST))
                  (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len lowindex highindex LST)))
  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR-RANGE))))

(defthmd take-when-most-known
  (implies (and (equal (take (+ -1 n) x) free)
                (posp n))
           (equal (take n x)
                  (append free
                          (list (nth (+ -1 n) x)))))
  :hints (("Goal" :in-theory (enable equal-of-append
;                                     subrange ;todo
                                     CAR-BECOMES-NTH-OF-0
                                     ))))

(defthm nth-of-bv-array-clear-range
  (implies (and (natp len)
                (natp n)
                (natp lowindex)
                (natp highindex)
                (<= lowindex n)
                (<= n highindex)
                (<= lowindex highindex)
                (< highindex len)
                )
           (equal (nth n (bv-array-clear-range elem-size len lowindex highindex lst))
                  0))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear-range bv-array-write update-nth2)
         ()))))

;; (thm
;;  (equal (BV-ARRAY-CLEAR ELEM-SIZE len len LST)
;;         (BVCHOP-LIST ELEM-SIZE (TAKE LEN LST)))
;;  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR bv-array-write update-nth2))))

;; (thm
;;  (equal (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len len HIGHINDEX LST)
;;         (BVCHOP-LIST ELEM-SIZE (TAKE LEN LST)))
;;  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR-RANGE))))

(defthm nth-of-bv-array-clear-range-low
  (implies (and (< n lowindex)
                (< lowindex len)
                (natp len)
                (natp n)
                (natp lowindex)
        ;        (equal len (len lst))
                (natp highindex)
                (<= lowindex highindex)
                (< highindex len))
           (equal (nth n (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bvchop elem-size (nth n lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear-range bv-array-write update-nth2)
                                  ()))))

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
  :hints (("Goal" :cases ((natp len))
           :in-theory (enable bv-array-clear-range))))

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

(defthm bv-array-clear-of-true-list-fix
  (equal (bv-array-clear elem-size len index (true-list-fix lst))
         (bv-array-clear elem-size len index lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))
