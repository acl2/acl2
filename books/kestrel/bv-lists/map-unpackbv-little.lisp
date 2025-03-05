; Mapping unpackbv-little over a list.
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unpackbv-little")
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-all-integerp" :dir :system)

;; Splits each of the BVS into list of NUM items, each with SIZE bits.
;; The result is a list of lists, one list for each of the original BVS.
;; Unpacking is done in little-endian fashion, so the least significant chunk of
;; each BV comes first in the corresponding list.
(defun map-unpackbv-little (num size bvs)
  (declare (xargs :guard (and (natp size)
                              (natp num)
                              (all-integerp bvs))))
  (if (atom bvs)
      nil
    (cons (unpackbv-little num size (first bvs))
          (map-unpackbv-little num size (rest bvs)))))

(defthm len-of-map-unpackbv-little
  (equal (len (map-unpackbv-little num size bvs))
         (len bvs)))

(defthm items-have-len-of-map-unpackbv-little
  (implies (natp num)
           (items-have-len num (map-unpackbv-little num size bvs))))

(defthm true-list-listp-of-map-unpackbv-little
  (true-list-listp (map-unpackbv-little num size bvs)))

(defthm all-all-integerp-of-map-unpackbv-little
  (all-all-integerp (map-unpackbv-little num size bvs))
  :hints (("Goal" :in-theory (enable map-unpackbv-little))))
