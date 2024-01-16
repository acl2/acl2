; Reading a chunk of bytes from a bv-array
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "bv-array-read")
(include-book "unsigned-byte-listp")
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;; From the ARRAY (described by ELEMENT-SIZE and ARRAY-LEN), read ELEMENT-COUNT
;; elements starting at INDEX and combine then into a single BV in a
;; little-endian way.
(defund bv-array-read-chunk-little (element-count element-size array-len index array)
  (declare (xargs :guard (and (natp element-size)
                              (unsigned-byte-listp element-size array)
                              (natp index)
                              (natp element-count)
                              (equal array-len (len array))
                              (< (+ -1 index element-count) array-len))))
  (if (zp element-count)
      0
    (bvcat (* element-size (+ -1 element-count))
           (bv-array-read-chunk-little (+ -1 element-count) element-size array-len (+ 1 index) array)
           element-size
           (bv-array-read element-size array-len index array))))

;; Discards irrelevant elements from the start of the array.
(defthm bv-array-read-chunk-little-of-+-arg4-when-constants
  (implies (and (syntaxp (and (quotep k)
                              (quotep array)))
                (natp index)
                (natp k)
                (natp element-count)
                (equal array-len (len array))
                (< (+ -1 k index element-count) array-len))
           (equal (bv-array-read-chunk-little element-count element-size array-len (+ k index) array)
                  (bv-array-read-chunk-little element-count element-size (- array-len k) index (nthcdr k array))))
  :hints (("Goal" :in-theory (enable bv-array-read-chunk-little bv-array-read-opener))))

(defthm bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg
 (implies (and (natp len)
               (natp index))
          (equal (acl2::bv-array-read-chunk-little num element-width len (+ index (expt 2 (ceiling-of-lg len))) data)
                 (acl2::bv-array-read-chunk-little num element-width len index data)))
 :hints (("Goal" :in-theory (enable acl2::bv-array-read-chunk-little))))

(defthm bv-array-read-chunk-little-of-expt-of-ceiling-of-lg
 (implies (and (natp len)
               (natp index))
          (equal (acl2::bv-array-read-chunk-little num element-width len (expt 2 (ceiling-of-lg len)) data)
                 (acl2::bv-array-read-chunk-little num element-width len 0 data)))
 :hints (("Goal" :use (:instance bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg (index 0))
          :in-theory (disable bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg))))
