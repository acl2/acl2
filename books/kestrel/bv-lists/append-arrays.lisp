; Appending bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-arrayp")
(include-book "bv-array-read")
(include-book "bvchop-list")
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))

;todo: add "bv" to the name

(defund append-arrays (width len1 array1 len2 array2)
  (declare (xargs :guard (and (natp len1)
                              (natp len2)
                              (natp width)
                              (true-listp array1)
                              (true-listp array2))))
  (bvchop-list width (append (take len1 array1)
                              (take len2 array2))))

(defthm len-of-append-arrays
  (equal (len (append-arrays width len1 array1 len2 array2))
         (+ (nfix len1) (nfix len2)))
  :hints (("Goal" :in-theory (enable append-arrays))))

(defthm all-unsigned-byte-p-of-append-arrays
  (implies (natp size) ;move to cons?
           (all-unsigned-byte-p size (append-arrays size a b c d)))
  :hints (("Goal" :in-theory (enable append-arrays))))

(defthm bv-arrayp-of-append-arrays
  (implies (and (natp element-size)
                (natp len1)
                (natp len2)
                )
           (equal (bv-arrayp element-size len (append-arrays element-size len1 array1 len2 array2))
                  (equal len (+ len1 len2))))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

;gross because it mixes theories?
;fixme could make an append operator with length params for two arrays..
(defthm bv-array-read-of-append-arrays
  (implies (and (equal len (+ len1 len2))
                (< index len)
                (natp len1)
                (natp len2)
                (natp index))
           (equal (bv-array-read width len index (append-arrays width len1 x len2 y))
                  (if (< index len1)
                      (bv-array-read width len1 index x)
                    (bv-array-read width len2 (- index len1) y))))
  :hints (("Goal" :in-theory (enable bv-array-read-opener append-arrays))))
