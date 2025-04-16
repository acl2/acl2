; Clearing values in bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/subrange-def" :dir :system)
(include-book "bv-array-write")
(local (include-book "all-unsigned-byte-p2"))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

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
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm nth-of-bv-array-clear
  (implies (and (< n len)
                (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  0))
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write update-nth2 ceiling-of-lg))))

(defthm nth-of-bv-array-clear-better
  (implies (and (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  (if (< n len)
                      0
                    nil)))
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write ceiling-of-lg update-nth2))))

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
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write-opener update-nth2))))

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
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write-opener update-nth2))))

(defthm all-integerp-of-bv-array-clear
  (all-integerp (bv-array-clear element-size len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

;; only 1 element and we set it to 0
(defthm bv-array-clear-1-0
  (equal (bv-array-clear width 1 0 data)
         '(0))
  :hints (("Goal" :in-theory (enable bv-array-clear update-nth2))))

(defthm bv-array-clear-of-repeat-same
  (equal (bv-array-clear 8 len start (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :in-theory (enable ;update-nth-when-equal-of-nth
                              bv-array-clear
                              bv-array-write ;fixme
                              update-nth2
                              ))))

(defthm bv-array-clear-of-true-list-fix
  (equal (bv-array-clear elem-size len index (true-list-fix lst))
         (bv-array-clear elem-size len index lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm all-unsigned-byte-p-of-bv-array-clear-gen
  (implies (and (<= element-size size)
                (natp size)
                (natp element-size))
           (all-unsigned-byte-p size (bv-array-clear element-size len key lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-clear-of-take
  (equal (bv-array-clear esize len key (take len lst))
         (bv-array-clear esize len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-clear-of-bv-array-write
  (implies (and (not (equal key1 key2))
                (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))
  :hints (("Goal" :cases ((< KEY1 KEY2)
                          (< KEY2 KEY1)
                          )
           :in-theory (e/d (BV-ARRAY-CLEAR ;bv-array-write
                            BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF ;could this ever loop?  make a syntaxp version for non constants?
                            )
                           ()))))

(defthm bv-array-clear-of-bv-array-write-same
  (implies (and (natp esize)
                (< key len)
                (natp key)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key (bv-array-write esize len key val lst))
                  (bv-array-clear esize len key lst)))
  :hints (("Goal" :cases ((< KEY1 KEY2)
                          (< KEY2 KEY1))
           :in-theory (e/d (BV-ARRAY-CLEAR) ()))))

(defthm bv-array-clear-of-bvchop-list
  (equal (bv-array-clear elemement-width len index (bvchop-list elemement-width array))
         (bv-array-clear elemement-width len index array))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-clear-of-bv-array-clear-diff
  (implies (and (syntaxp (smaller-termp index2 index1))
                (<= element-size2 element-size1) ;other case?
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2))
           (equal (bv-array-clear element-size1 len index1 (bv-array-clear element-size2 len index2 lst))
                  (bv-array-clear element-size2 len index2 (bv-array-clear element-size2 len index1 lst))))
  :hints (("Goal"
           :use (:instance bv-array-write-of-bv-array-write-diff-constant-indices-gen (val1 0) (val2 0))
           :cases ((equal element-size1 element-size2))
           :in-theory (e/d (bv-array-clear)
                           (bv-array-write-of-bv-array-write-diff-constant-indices-gen
                            )))))

(defthm bv-array-clear-of-bv-array-clear-diff-constant-indices
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1)
                (<= element-size2 element-size1) ;other case?
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2))
           (equal (bv-array-clear element-size1 len index1 (bv-array-clear element-size2 len index2 lst))
                  (bv-array-clear element-size2 len index2 (bv-array-clear element-size2 len index1 lst))))

  :hints (("Goal" :use (:instance bv-array-clear-of-bv-array-clear-diff)
           :in-theory (disable bv-array-clear-of-bv-array-clear-diff))))


(defthm bv-array-clear-of-cons
  (implies (and (< i len)
                (equal (+ -1 len) (len x))
                (natp i)
                (true-listp x) ;move to conclusion
                (natp len)
                (natp size)
                )
           (equal (bv-array-clear size len i (cons a x))
                  (if (zp i)
                      (cons 0 (bvchop-list size x))
                    (cons (bvchop size a) (bv-array-clear size (+ -1 len) (+ -1 i) x)))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg)
                                  (;UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT
                                   ;UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   ;;update-nth-becomes-update-nth2-extend-gen
                                   )))))

;;todo clear-nth becomes bv-array-clear?

(defthm bv-array-clear-of-0-arg2
  (equal (bv-array-clear size 0 index data)
         nil)
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-clear-of-0-and-cons
  (implies (syntaxp (not (quotep a)))
           (equal (bv-array-clear size len 0 (cons a b))
                  (bv-array-clear size len 0 (cons 0 b))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2)
                                  (
                                   ;;update-nth-becomes-update-nth2-extend-gen
                                   )))))

(defthmd bv-array-write-of-0-becomes-bv-array-clear
  (equal (bv-array-write elem-size len index1 0 lst)
         (bv-array-clear elem-size len index1 lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))
(defthm bv-array-clear-of-bv-array-write-both
  (implies (and (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (if (equal key1 key2)
                      (bv-array-clear esize len key1 lst)
                    (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))))

(defthm bv-array-clear-of-bv-array-write-better
  (implies (and (not (equal key1 key2))
                (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (<= len (len lst)) ;drop?
                )
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))
  :hints (("Goal" :use (:instance bv-array-clear-of-bv-array-write (lst (firstn len lst)))
           :in-theory (disable bv-array-clear-of-bv-array-write
                               ))))

(defthm bv-array-clear-of-bv-array-clear-same
  (implies (and (natp index)
                (natp len)
                (natp element-size))
           (equal (bv-array-clear element-size len index (bv-array-clear element-size len index lst))
                  (bv-array-clear element-size len index lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write bv-array-clear update-nth2) ()))))

;could drop hyps if we change what bv-array-clear-range does in the base case
(defthm take-of-bv-array-clear-irrel
  (implies (and (<= index index2)
                (natp len)
                (< index2 len)
;                (<= len (len lst))
                (natp index)
                (natp index2))
           (equal (take index (bv-array-clear elem-size len index2 lst))
                  (bvchop-list elem-size (take index lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg) ()))))

(defthm nthcdr-of-bv-array-clear
  (implies (and (<= n len)
                (< key len)
                (integerp len)
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-clear element-size len key lst))
                  (if (< key n)
                      (bvchop-list element-size
                                    (nthcdr n (take len (true-list-fix lst))))
                    (bv-array-clear element-size (- len n)
                                    (- key n) (nthcdr n lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm car-of-BV-ARRAY-CLEAR-of-0
  (implies (posp len)
           (equal (CAR (BV-ARRAY-CLEAR ELEM-SIZE LEN 0 lst))
                  0))
  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR))))

(defthm car-of-bv-array-clear
  (equal (car (bv-array-clear width len index data))
         (if (posp len)
             (if (zp (bvchop (ceiling-of-lg (nfix len)) index))
                 0
               (bvchop width (car data)))
           nil))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-length-1-of-list-zero
  (equal (bv-array-clear width 1 index '(0))
         '(0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm cdr-of-bv-array-clear
  (implies (and (posp len)
                (< index len) ;Mon Jul 19 21:20:04 2010
                (natp index))
           (equal (cdr (bv-array-clear width len index data))
                  (if (zp index)
                      (bvchop-list width (SUBRANGE 1 (+ -1 LEN) DATA)) ; todo: avoid subrange here?
                    (bv-array-clear width (+ -1 len) (+ -1 index) (cdr data)))))
  :hints (("Goal"
           :cases ((< len 2))
           :in-theory (e/d (bv-array-clear bv-array-write-opener update-nth2 subrange)
                           (;GETBIT-OF-BV-ARRAY-READ-HELPER ;yuck
                            update-nth-becomes-update-nth2-extend-gen)))))

(defthm cdr-of-bv-array-clear-of-0
  (implies (posp len)
           (equal (cdr (bv-array-clear elem-size len 0 lst))
                  (bvchop-list elem-size (take (+ -1 len) (cdr lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm cdr-of-bv-array-clear-2
  (implies (and (<= n len)
                (< key len)
                (integerp len)
                (natp key))
           (equal (cdr (bv-array-clear element-size len key lst))
                  (if (< key 1)
                      (bvchop-list element-size
                                   (cdr (take len (true-list-fix lst))))
                    (bv-array-clear element-size (- len 1)
                                    (- key 1) (cdr lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthmd bv-array-clear-redef-special
  (implies (and (< index len)
                (equal len (len data)) ; this case
                (natp index))
           (equal (bv-array-clear element-size len index data)
                  (append (bvchop-list element-size (take index data))
                          (list 0)
                          (bvchop-list element-size (nthcdr (+ 1 index) data)))))
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write-redef-special))))

(defthmd bv-array-clear-redef
  (implies (and (< index len)
                (natp len)
                (natp index))
           (equal (bv-array-clear element-size len index data)
                  (append (bvchop-list element-size (take index data))
                          (list 0)
                          (bvchop-list element-size (take (+ -1 (- index) len) (nthcdr (+ 1 index) data))))))
  :hints (("Goal" :in-theory (enable bv-array-clear bv-array-write-redef))))
