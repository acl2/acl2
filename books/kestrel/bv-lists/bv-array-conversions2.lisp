; Conversions between lists and bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-arrays") ; for bv-arrayp-of-bv-array-write
(include-book "bv-array-write")
(include-book "array-of-zeros")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;; See also bv-array-conversions2.lisp and bv-array-conversions-gen.lisp.

(local
 (defthm plus-of-minus-when-constant
   (implies (and (equal x (+ k i))
                 (syntaxp (quotep k))
                 (acl2-numberp k))
            (equal (+ (- i) x)
                   k))
   :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes values from LST into ARRAY, at positions I through LEN-1.
;; This version is tail recursive, but note that it won't often run because list-to-bv-array2 has an MBE.
(defund list-to-bv-array-aux2 (element-size len i lst array)
  (declare (xargs :guard (and (natp element-size)
                              (natp len)
                              (natp i)
                              (<= i len)
                              (bv-arrayp element-size len array)
                              (unsigned-byte-listp element-size lst)
                              (equal (len lst) (- len i)) ; lst has exactly enough elements remaining
                              )
                  :measure (nfix (- len i))))
  (if (or (not (mbt (and (natp i)
                         (natp len))))
          (>= i len))
      array
    (list-to-bv-array-aux2 element-size len
                           (+ 1 i) (rest lst)
                           (bv-array-write element-size len i (first lst) array))))

(defthm len-of-list-to-bv-array-aux2
  (implies (equal len (len array))
           (equal (len (list-to-bv-array-aux2 element-size len i lst array))
                  len))
  :hints (("Goal" :induct t
           :in-theory (enable list-to-bv-array-aux2))))

(defthm bv-array-aux2-iff
  (implies (equal len (len array))
           (iff (list-to-bv-array-aux2 element-size len i lst array)
                array))
  :hints (("Goal" :induct t
           :in-theory (enable list-to-bv-array-aux2))))

(defthm consp-of-bv-array-aux2
  (implies (equal len (len array))
           (equal (consp (list-to-bv-array-aux2 element-size len i lst array))
                  (posp len)))
  :hints (("Goal" :induct t
           :in-theory (enable list-to-bv-array-aux2))))

(defthm car-of-bv-array-aux2
  (implies (and (equal len (len array))
                (< i (len array))
                (natp i)
                (natp element-size))
           (equal (car (list-to-bv-array-aux2 element-size len i lst array))
                  (if (zp i)
                      (bvchop element-size (car lst))
                    (bvchop element-size (car array)))))
  :hints (("Goal" :induct t
           :in-theory (enable list-to-bv-array-aux2)
           :expand ((LIST-TO-BV-ARRAY-AUX2 ELEMENT-SIZE (LEN ARRAY) 0 LST ARRAY)))))

(defthm nthcdr-of-list-to-bv-array-aux2
  (implies (and (<= n i) ;this case
                (natp n)
                (natp len)
                (<= i len)
                (natp i)
                )
           (equal (nthcdr n (list-to-bv-array-aux2 element-size len i lst array))
                  (list-to-bv-array-aux2 element-size (- len n) (- i n) lst (nthcdr n array))))
  :hints (("Goal" :expand ((list-to-bv-array-aux2 element-size (+ i (- n))
                                       (+ i (- n))
                                       lst
                                       (nthcdr n array)))
           :in-theory (enable natp equal-of-bv-array-write-of-1 list-to-bv-array-aux2))))

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
           (equal (nthcdr n (list-to-bv-array-aux2 element-size len i lst array))
                  (list-to-bv-array-aux2 element-size (- len n) 0 (nthcdr (- n i) lst) (nthcdr n array))))
  :hints (("Goal" :induct t
           :in-theory (e/d (natp nthcdr equal-of-bv-array-write-of-1 list-to-bv-array-aux2)
                           (;;NTHCDR-OF-LIST-TO-BV-ARRAY-AUX2
                            )))))

(defthm nthcdr-of-list-to-bv-array-aux2-case3
  (implies (and (<= len n) ; this case
                (equal len (len array))
                (natp n)
                (true-listp array))
           (equal (nthcdr n (list-to-bv-array-aux2 element-size len i lst array))
                  nil)))

(defthmd list-to-bv-array-aux2-of-cons
  (implies (and (natp i)
                (natp len)
                (< i len))
           (equal (list-to-bv-array-aux2 element-size len i (cons x y) array)
                  (list-to-bv-array-aux2 element-size
                                         len
                                         (+ 1 i)
                                         y
                                         (bv-array-write element-size
                                                         len
                                                         i
                                                         x
                                                         array))))
  :hints (("Goal" :in-theory (enable list-to-bv-array-aux2))))

;; (defund list-to-bv-array-aux2-alt (element-size len i lst array)
;;   (declare (xargs :guard (and (natp element-size)
;;                               (natp len)
;;                               (natp i)
;;                               (bv-arrayp element-size len array)
;;                               (true-listp lst))
;;                   :measure (nfix (- len i))
;;                   :verify-guards nil ; todo
;;                   ))
;;   (if (or (not (mbt (and (natp i)
;;                          (natp len))))
;;           (>= i len))
;;       array
;;     (bv-array-write element-size len i (first lst)
;;                     (list-to-bv-array-aux2-alt element-size len (+ 1 i)
;;                                                (rest lst)
;;                                                array
;;                                                ))))

;; (thm
;;   (equal (list-to-bv-array-aux2-alt element-size len i lst array)
;;          (list-to-bv-array-aux2 element-size len i lst array))
;;   :hints (("Goal" :expand (list-to-bv-array-aux2 element-size len i lst array)
;;            :in-theory (enable list-to-bv-array-aux2-alt
;;                               list-to-bv-array-aux2))))

(defthm list-to-bv-array-aux2-of-bv-array-write
  (implies (and (< g i) ; so the write is to an element not affected by the list-to-bv-array-aux2
                (natp g))
           (equal (list-to-bv-array-aux2 element-size len i lst (bv-array-write element-size len g val array))
                  (bv-array-write element-size len g val (list-to-bv-array-aux2 element-size len i lst array))))
  :hints (("Goal"
           :induct (list-to-bv-array-aux2 element-size len i lst array) ; why is this needed?
           :in-theory (enable list-to-bv-array-aux2
                              bv-array-write-of-bv-array-write-diff))))

(defthm take-of-list-to-bv-array-aux2
  (implies (and (<= n i) ; none of the elements copied in are taken
                (natp n)
                (< i len)
                (natp i)
                (equal len (len array)))
           (equal (take n (list-to-bv-array-aux2 element-size len i lst array))
                  (take n (bvchop-list element-size array))))
  :hints (("Goal" :in-theory (enable list-to-bv-array-aux2))))

(defthm nthcdr-of-list-to-bv-array-aux2-case2-better
  (implies (and (<= i len)
                (equal len (len array))
                (natp element-size)
                (equal (len lst) (- len i))
                (true-listp array)
                (natp i))
           (equal (nthcdr i (list-to-bv-array-aux2 element-size len i lst array))
                  (bvchop-list element-size lst)))
  :hints (("Goal" :induct t
           :expand ((bvchop-list element-size lst)
                    (bv-array-write element-size (len lst)
                                    0 (car lst)
                                    (nthcdr (+ -1 i)
                                            (cdr (list-to-bv-array-aux2 element-size (len array)
                                                                        (+ 1 i)
                                                                        (cdr lst)
                                                                        array))))
                    (bv-array-write element-size (len array)
                                    0 (car lst)
                                    (list-to-bv-array-aux2 element-size (len array)
                                                           1 (cdr lst)
                                                           array))
                    (bv-array-write element-size (len lst)
                                    0 (car lst)
                                    (nthcdr i
                                            (list-to-bv-array-aux2 element-size (len array)
                                                                   (+ 1 i)
                                                                   (cdr lst)
                                                                   array)))
                    )
           :in-theory (e/d (natp nthcdr equal-of-bv-array-write-of-1 list-to-bv-array-aux2 zp
                                 ;bv-array-write
                                 update-nth2
                                 cdr-of-nthcdr
                                 )
                           (;;NTHCDR-OF-LIST-TO-BV-ARRAY-AUX2
                            nthcdr-of-list-to-bv-array-aux2
                            )))))

(defthm array-aux2-case2-of-0-redef
  (implies (and (equal len (len array))
                (natp element-size)
                (equal (len lst) len)
                (true-listp array)
                (natp i))
           (equal (list-to-bv-array-aux2 element-size len 0 lst array)
                  (bvchop-list element-size lst)))
  :hints (("Goal" :use (:instance nthcdr-of-list-to-bv-array-aux2-case2-better
                                  (i 0))
           :in-theory (disable nthcdr-of-list-to-bv-array-aux2-case2-better))))


;; (thm
;;   (implies (and (< i (len array)) ;; add to guard? ; allow = ?
;;                 (equal (len lst) (+ len (- i))) ; add to guard?
;;                 (natp element-size)
;;                 (natp len)
;;                 (natp i)
;;                 (bv-arrayp element-size len array)
;;                 (true-listp lst))
;;            (equal (list-to-bv-array-aux2 element-size len i lst array)
;;                   (append (take i array)
;;                           lst)))
;;   :hints (("Goal" :expand (list-to-bv-array-aux2 element-size 1 0 lst (nthcdr i array))
;; ;           :induct (list-to-bv-array-aux2 element-size len i lst array)
;;            :in-theory (enable list-to-bv-array-aux2
;;                               bv-arrayp
;;                               bv-array-write-redef-special
;;                               equal-of-append
;;                               ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version should be instantaneous to run, due to the MBE
(defund list-to-bv-array2 (element-size lst)
  (declare (xargs :guard (and (natp element-size)
                              (unsigned-byte-listp element-size lst))))
  (mbe :logic (let* ((len (len lst))
                     (array (array-of-zeros element-size len)))
                (list-to-bv-array-aux2 element-size len 0 lst array))
       :exec lst))

(defthm len-of-list-to-bv-array2
  (equal (len (list-to-bv-array2 element-size lst))
         (len lst))
  :hints (("Goal" :in-theory (enable list-to-bv-array2))))

(defthm nthcdr-of-list-to-bv-array2
  (equal (nthcdr n (list-to-bv-array2 8 lst))
         (list-to-bv-array2 8 (nthcdr n lst)))
  :hints (("Goal" :cases ((zp (len lst)))
           :in-theory (enable list-to-bv-array2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund list-to-byte-array2 (lst)
  (declare (xargs :guard (unsigned-byte-listp 8 lst)))
  (list-to-bv-array2 8 lst))
