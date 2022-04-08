; Packing a list of BVs to create a shorter list of larger BVs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-def")
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(local (include-book "packbv"))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;; TODO: Prove this is the same as map-packbv of group.

;; "Pack bit-vectors"
;; Packs the ITEMS into larger bit-vectors.  Take ITEMS-PER-CHUNK elements of
;; ITEMS at a time, packing each such group into a larger bit-vector.  Returns
;; a list of these larger bit-vectors.  The packing of each item is big-endian
;; (see packbv).
(defund packbvs (items-per-chunk itemsize items)
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
      (cons (packbv items-per-chunk itemsize (take items-per-chunk items))
            (packbvs items-per-chunk itemsize (nthcdr items-per-chunk items))))))

(defthm all-unsigned-byte-p-of-packbvs
  (implies (and (<= (* items-per-chunk itemsize) size)
                (natp size)
                (natp itemsize))
           (all-unsigned-byte-p size (packbvs items-per-chunk itemsize items)))
  :hints (("Goal" :in-theory (enable packbvs))))

;gen?
(defthm len-of-packbvs
  (implies (and (posp items-per-chunk)
                (equal (mod (len items) items-per-chunk)
                       0))
           (equal (len (packbvs items-per-chunk itemsize items))
                  (/ (len items) items-per-chunk)))
  :hints (("Goal" :in-theory (enable packbvs))))

; (equal (packbvs 4 8 '(0 0 0 1  1 0 0 1  0 0 0 0)) '(1 16777217 0))
