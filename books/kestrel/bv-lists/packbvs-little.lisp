; Packing a list of BVs to create a shorter list of larger BVs (little endian)
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-little") ; or just the def
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

;; "Pack bit-vectors little"
;; Packs the ITEMS into larger bit-vectors.  Take ITEMS-PER-CHUNK elements of
;; ITEMS at a time, packing each such group into a larger bit-vector.  Returns
;; a list of these larger bit-vectors.  The packing of each item is little-endian
;; (see packbv-little).
(defund packbvs-little (items-per-chunk itemsize items)
  (declare (xargs :guard (and (posp items-per-chunk)
                              (natp itemsize)
                              (true-listp items)
                              (all-unsigned-byte-p itemsize items)
                              (equal (mod (len items) items-per-chunk)
                                     0))))
  (if (not (mbt (posp items-per-chunk))) ; ensure termination
      nil
    (if (endp items)
        nil
      (cons (packbv-little items-per-chunk itemsize (take items-per-chunk items))
            (packbvs-little items-per-chunk itemsize (nthcdr items-per-chunk items))))))

(defthm all-unsigned-byte-p-of-packbvs-little
  (implies (and (<= (* items-per-chunk itemsize) size)
                (natp size)
                (natp itemsize))
           (all-unsigned-byte-p size (packbvs-little items-per-chunk itemsize items)))
  :hints (("Goal" :in-theory (enable packbvs-little))))

;gen?
(defthm len-of-packbvs-little
  (implies (and (posp items-per-chunk)
                (equal (mod (len items) items-per-chunk)
                       0))
           (equal (len (packbvs-little items-per-chunk itemsize items))
                  (/ (len items) items-per-chunk)))
  :hints (("Goal" :in-theory (enable packbvs-little))))

(defthm consp-of-packbvs-little
  (implies (posp items-per-chunk)
           (equal (consp (packbvs-little items-per-chunk itemsize items))
                  (consp items)))
  :hints (("Goal" :in-theory (enable packbvs-little))))

;; (thm
;;  (equal (packbvs-little 4 8 '(0 0 0 1  1 0 0 1  0 0 0 0))
;;         '(16777216 16777217 0)))

(defthm car-of-packbvs-little
  (implies (posp items-per-chunk)
           (equal (car (packbvs-little items-per-chunk itemsize items))
                  (if (endp items)
                      nil
                    (packbv-little items-per-chunk itemsize (take items-per-chunk items)))))
  :hints (("Goal" :in-theory (enable packbvs-little))))

(local (include-book "kestrel/lists-light/nth" :dir :system))

(local
  (defun ind (items-per-chunk itemsize items n)
    (if (not (mbt (posp items-per-chunk))) ; ensure termination
        (list items-per-chunk itemsize items n)
      (if (endp items)
          nil
        (ind items-per-chunk itemsize (nthcdr items-per-chunk items) (+ -1 n))))))

;; or could phrase the RHS using subrange
(defthm nth-of-packbvs-little
  (implies (and (posp items-per-chunk)
                ;; (equal (mod (len items) items-per-chunk) 0)
                (natp n)
                (< n (/ (len items) items-per-chunk)) ; gen?
                )
           (equal (nth n (packbvs-little items-per-chunk itemsize items))
                  (packbv-little items-per-chunk itemsize (take items-per-chunk (nthcdr (* n items-per-chunk) items)))))
  :hints (("Goal" :induct (ind items-per-chunk itemsize items n)
           :in-theory (enable packbvs-little (:i nthcdr)))))

(defthm nth-of-packbvs-little-alt
  (implies (and (posp items-per-chunk)
                (equal (mod (len items) items-per-chunk) 0)
                (natp n))
           (equal (nth n (packbvs-little items-per-chunk itemsize items))
                  (if (< n (/ (len items) items-per-chunk))
                      (packbv-little items-per-chunk itemsize (take items-per-chunk (nthcdr (* n items-per-chunk) items)))
                    nil)))
  :hints (("Goal" :induct (ind items-per-chunk itemsize items n)
           :in-theory (enable packbvs-little (:i nthcdr)))))
