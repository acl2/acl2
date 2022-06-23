; Conversions between lists and bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-arrays")
(include-book "array-of-zeros")
(local (include-book "all-unsigned-byte-p2"))
;(local (include-book "all-unsigned-byte-p"))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; See also bv-array-conversions.lisp and bv-array-conversions2.lisp.

;; Reads the segment of values from index i through index j.  Returns a list.
(defund bv-array-read-segment (element-width array-len i j array)
  (declare (xargs :guard (and (natp element-width)
                              (natp i)
                              (integerp j)
                              (<= -1 j)
                              (bv-arrayp element-width array-len array)
                              (<= i (+ 1 j))
                              (< j array-len))
                  :measure (+ 1 (nfix (+ 1 (- j i))))))
  (if (or (not (mbt (and (natp i)
                         (integerp j))))
          (< j i))
      nil
    (cons (bv-array-read element-width array-len i array)
          (bv-array-read-segment element-width array-len (+ 1 i) j array))))

(defthm unsigned-byte-listp-of-bv-array-read-segment
  (implies (natp element-width)
           (unsigned-byte-listp element-width (bv-array-read-segment element-width array-len i j array)))
  :hints (("Goal" :in-theory (enable bv-array-read-segment))))

(defthm len-of-bv-array-read-segment
  (implies (and (<= i (+ 1 j))
                (natp i)
                (integerp j))
           (equal (len (bv-array-read-segment element-width array-len i j array))
                  (+ 1 (- j i))))
  :hints (("Goal" :in-theory (enable bv-array-read-segment))))

(defthm consp-of-bv-array-read-segment
  (implies (and (<= i (+ 1 j))
                (natp i)
                (integerp j))
           (equal (consp (bv-array-read-segment element-width array-len i j array))
                  (< 0 (+ 1 (- j i)))))
  :hints (("Goal" :in-theory (enable bv-array-read-segment))))

(local
 (defun sub1-plus1-induct (n i)
   (if (zp n)
       (list n i)
     (sub1-plus1-induct (+ -1 n) (+ 1 i)))))

(defthm car-of-bv-array-read-segment
  (implies (and (<= i (+ 1 j))
                (natp i)
                (integerp j))
           (equal (car (bv-array-read-segment element-width array-len i j array))
                  (if (<= i j)
                      (bv-array-read element-width array-len i array)
                    nil)))
  :hints (("Goal" :expand (bv-array-read-segment element-width array-len i i array)
           :in-theory (enable bv-array-read-segment))))

(defthm take-of-bv-array-read-segment
  (implies (and (<= n (+ 1 (- j i)))
                (natp n)
                (natp i)
                (integerp j))
           (equal (take n (bv-array-read-segment element-width array-len i j array))
                  (bv-array-read-segment element-width array-len i (+ -1 i n) array)))
  :hints (("Goal"  :induct (sub1-plus1-induct n i)
           :in-theory (enable bv-array-read-segment))))

(defthm cdr-of-bv-array-read-segment
  (implies (and (<= i (+ 1 j))
                (natp i)
                (integerp j))
           (equal (cdr (bv-array-read-segment element-width array-len i j array))
                  (if (<= j i)
                      nil
                    (bv-array-read-segment element-width array-len (+ 1 i) j array))))
  :hints (("Goal"
           :in-theory (enable bv-array-read-segment nthcdr))))

(defthm nthcdr-of-bv-array-read-segment
  (implies (and (<= i (+ 1 j))
                (natp n)
                (natp i)
                (integerp j))
           (equal (nthcdr n (bv-array-read-segment element-width array-len i j array))
                  (if (<= (+ 1 (- j i)) n)
                      nil
                    (bv-array-read-segment element-width array-len (+ n i) j array))))
  :hints (("Goal" :induct (sub1-plus1-induct n i)
           :in-theory (enable bv-array-read-segment nthcdr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; better name?
;should we pass in the length too (can't really ask an array for its length)?
(defund bv-array-to-list-gen (element-width array)
  (declare (xargs :guard (and (natp element-width)
                              (bv-arrayp element-width (len array) array))))
  (bv-array-read-segment element-width (len array) 0 (+ -1 (len array)) array))

(defthm unsigned-byte-listp-of-bv-array-to-list-gen
  (implies (and (natp element-width)
                (bv-arrayp element-width (len array) array))
           (unsigned-byte-listp element-width (bv-array-to-list-gen element-width array)))
  :hints (("Goal" :in-theory (enable bv-array-to-list-gen))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Write the VALS to the array segment from index i through index j.  Returns an updated array.
(defund bv-array-write-segment (element-width array-len i j vals array)
  (declare (xargs :guard (and (natp element-width)
                              (natp i)
                              (integerp j)
                              (<= -1 j)
                              (bv-arrayp element-width array-len array)
                              (<= i (+ 1 j))
                              (< j array-len)
                              (<= (+ 1 (- j i)) (len vals)))
                  :measure (+ 1 (nfix (+ 1 (- j i))))))
  (if (or (not (mbt (and (natp i)
                         (integerp j))))
          (< j i))
      array
    (bv-array-write-segment element-width
                            array-len
                            (+ 1 i)
                            j
                            (cdr vals)
                            (bv-array-write element-width array-len i (first vals) array))))

(defthm bv-array-write-segment-out-of-order
  (implies (< j i)
           (equal (bv-array-write-segment element-width array-len i j vals array)
                  array))
  :hints (("Goal" :in-theory (enable bv-array-write-segment))))

(defthm bv-array-write-segment-of-cons
  (implies (and (natp i)
                (integerp j)
                (< j array-len))
           (equal (bv-array-write-segment element-width array-len i j (cons val vals) array)
                  (if (<= i j) ; at least one val being written
                      (bv-array-write-segment element-width array-len (+ 1 i) j vals
                                              (bv-array-write element-width array-len i val array))
                    array)))
  :hints (("Goal" :in-theory (enable bv-array-write-segment))))

(defthm bv-array-write-segment-of-append
  (implies (and (equal (+ 1 (- j i)) (+ (len vals1) (len vals2))) ; gen?
                (<= i (+ 1 j))
                (< j array-len)
                (natp i)
                (integerp j))
           (equal (bv-array-write-segment element-width array-len i j (append vals1 vals2) array)
                  (bv-array-write-segment element-width array-len (+ i (len vals1)) j vals2
                                          (bv-array-write-segment element-width array-len i (+ -1 i (len vals1)) vals1 array))))
  :hints (("Goal" :induct (bv-array-write-segment element-width array-len i j vals1 array)
           :in-theory (enable bv-array-write-segment append))))

(defthm len-of-bv-array-write-segment
  (implies (and (natp i)
                (integerp j)
                (equal array-len (len array))
                (< j array-len))
           (equal (len (bv-array-write-segment element-width array-len i j vals array))
                  (len array)))
  :hints (("Goal" :in-theory (enable bv-array-write-segment))))

(defthm bv-arrayp-of-bv-array-write-segment
  (implies (and (natp element-width)
                (natp i)
                (integerp j)
                (<= -1 j)
                (bv-arrayp element-width array-len array)
                (<= i (+ 1 j))
                (< j array-len)
                ;(<= (+ 1 (- j i)) (len vals))
                )
           (bv-arrayp element-width array-len (bv-array-write-segment element-width array-len i j vals array)))
  :hints (("Goal" :in-theory (enable bv-array-write-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; better name?
(defund list-to-bv-array-gen (element-width vals)
  (declare (xargs :guard (and (natp element-width)
                              (unsigned-byte-listp element-width vals))))
  (let ((array (array-of-zeros element-width (len vals))))
    (bv-array-write-segment element-width (len vals) 0 (+ -1 (len vals)) vals array)))

(defthm len-of-list-to-bv-array-gen
  (equal (len (list-to-bv-array-gen element-width vals))
         (len vals))
  :hints (("Goal" :in-theory (enable list-to-bv-array-gen))))

(defthm bv-arrayp-of-list-to-bv-array-gen
  (implies (and (natp element-width)
                (unsigned-byte-listp element-width vals))
           (bv-arrayp element-width (len vals) (list-to-bv-array-gen element-width vals)))
  :hints (("Goal" :in-theory (enable list-to-bv-array-gen))))
