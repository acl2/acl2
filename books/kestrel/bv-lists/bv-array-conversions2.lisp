; Conversions between lists and bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-arrays")
(local (include-book "kestrel/bv/getbit" :dir :system)) ;drop?
(local (include-book "kestrel/bv/logext" :dir :system)) ;drop?
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;this version is tail recursive
(defun list-to-bv-array-aux2 (element-size len i array lst)
  (declare (xargs :measure (nfix (- len i))
                  :guard (and (natp element-size)
                              (natp len)
                              (natp i)
                              (bv-arrayp element-size len array)
                              (true-listp lst))))
  (if (or (not (natp i))
          (not (natp len))
          (>= i len))
      array
    (list-to-bv-array-aux2 element-size len (+ 1 i)
                           (bv-array-write element-size len i (first lst) array)
                           (rest lst))))

(defthm len-of-list-to-bv-array-aux2
  (implies (equal len (len array))
           (equal (len (list-to-bv-array-aux2 element-size len i array lst))
                  len))
  :hints (("Goal" :induct t)))

;; (defthm list-to-bv-array-aux2-of-bvchop-list
;;   (implies (natp i)
;;            (equal (list-to-bv-array-aux2 element-size len i (bvchop-list element-size array) lst)
;;                   (list-to-bv-array-aux2 element-size len i array lst))))
;;   :hints (("Goal" :induct t)))

(defthm bv-array-aux2-iff
  (implies (equal len (len array))
           (iff (list-to-bv-array-aux2 element-size len i array lst)
                array))
  :hints (("Goal" :induct t)))

(defthm consp-of-bv-array-aux2
  (implies (equal len (len array))
           (equal (consp (list-to-bv-array-aux2 element-size len i array lst))
                  (posp len)))
  :hints (("Goal" :induct t)))

(defthm car-of-bv-array-aux2
  (implies (and (equal len (len array))
                (< i (len array))
                (natp i)
                (natp element-size))
           (equal (car (list-to-bv-array-aux2 element-size len i array lst))
                  (if (zp i)
                      (bvchop element-size (car lst))
                    (bvchop element-size (car array)))))
  :hints (("Goal" :induct t
           :expand ((LIST-TO-BV-ARRAY-AUX2 ELEMENT-SIZE (LEN ARRAY)
                                            0 ARRAY LST)))))


(defun list-to-bv-array2 (element-size lst)
  (declare (xargs :guard (and (natp element-size)
                              (true-listp lst))))
  (list-to-bv-array-aux2 element-size (len lst) 0 (array-of-zeros element-size (len lst)) lst))

(defthm len-of-list-to-bv-array2
  (equal (len (list-to-bv-array2 element-size lst))
         (len lst)))

(defthm nthcdr-of-list-to-bv-array-aux2
  (implies (and (<= n i) ;this case
                (natp n)
                (natp len)
                (<= i len)
                (natp i)
                )
           (equal (nthcdr n (list-to-bv-array-aux2 element-size len i array lst))
                  (list-to-bv-array-aux2 element-size (- len n) (- i n) (nthcdr n array) lst)))
  :hints (("Goal" :expand ((LIST-TO-BV-ARRAY-AUX2 ELEMENT-SIZE (+ I (- N))
                                       (+ I (- N))
                                       (NTHCDR N ARRAY)
                                       LST))
           :in-theory (enable natp))))

(defthm plus-of-minus-when-constant
  (implies (and (EQUAL x (+ k I))
                (syntaxp (quotep k))
                (acl2-numberp k))
           (equal (+ (- I) x)
                  k))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))

(defthm nthcdr-of-list-to-bv-array-aux2-case2
  (implies (and (<= i n) ;this case
                (<= n len)
                (< i len)
                (equal len (len array))
                (all-unsigned-byte-p element-size array)
                (natp element-size)
                (TRUE-LISTP ARRAY)
                (natp n)
                (natp i))
           (equal (nthcdr n (list-to-bv-array-aux2 element-size len i array lst))
                  (list-to-bv-array-aux2 element-size (- len n) 0 (nthcdr n array) (nthcdr (- n i) lst))))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (natp nthcdr) (;NTHCDR-OF-TAKE-BECOMES-SUBRANGE TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                                                       ;NTHCDR-OF-LIST-TO-BV-ARRAY-AUX2
                                                                       )))))

(defthm nthcdr-of-list-to-bv-array2
  (equal (nthcdr n (list-to-bv-array2 8 lst))
         (list-to-bv-array2 8 (nthcdr n lst)))
  :hints (("Goal" :cases ((zp (len lst)))
           :in-theory (enable list-to-bv-array2))))

(in-theory (disable list-to-bv-array2))

(defthmd list-to-bv-array-aux2-of-cons
  (implies (and (natp i)
                (natp len)
                (< i len))
           (equal (list-to-bv-array-aux2 element-size len i array (cons x y))
                  (list-to-bv-array-aux2 element-size
                                         len
                                         (+ 1 i)
                                         (bv-array-write element-size
                                                         len
                                                         i
                                                         x
                                                         array) y)))
  :hints (("Goal" :in-theory (enable LIST-TO-BV-ARRAY-AUX2))))
