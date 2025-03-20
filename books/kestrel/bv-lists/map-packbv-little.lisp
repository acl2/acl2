; Mapping packbv-little over a list.
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-little")
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/typed-lists-light/all-all-integerp" :dir :system)
(include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system)

;; Packs each of the LISTS in a BV and returns a list of those BVS.
;; Each of the LISTS should have length NUM and contain BVs of SIZE bits.
;; Packing is done in little-endian fashion, so earlier elements of each
;; LIST become less significant parts of the resulting BV.
(defun map-packbv-little (num size lists)
  (declare (xargs :guard (and (natp size)
                              (natp num)
                              (all-true-listp lists)
                              (all-all-integerp lists))))
  (if (atom lists)
      nil
    (cons (packbv-little num size (car lists))
          (map-packbv-little num size (cdr lists)))))

(defthm len-of-map-packbv-little
  (equal (len (map-packbv-little num size lists))
         (len lists)))

(defthm unsigned-byte-listp-of-map-packbv-little
  (implies (and (<= (* num size) size2)
                (integerp size2)
                (natp num)
                (natp size))
           (unsigned-byte-listp size2 (map-packbv-little num size lists)))
  :hints (("Goal" :in-theory (enable map-packbv-little))))
