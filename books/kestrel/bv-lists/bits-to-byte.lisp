; BV Lists Library: bits-to-byte
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../bv/bvcat2")
(include-book "all-unsigned-byte-p")
(local (include-book "../bv/bvcat"))

;; Convert BITS (a list of 8 bits) into a byte in a big-endian fashion where
;; the first element of BITS becomes the most significant bit of the result,
;; and so on.
(defund bits-to-byte (bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 bits)
                              (true-listp bits)
                              (= 8 (len bits)))))
  (bvcat2 1 (nth 0 bits)
          1 (nth 1 bits)
          1 (nth 2 bits)
          1 (nth 3 bits)
          1 (nth 4 bits)
          1 (nth 5 bits)
          1 (nth 6 bits)
          1 (nth 7 bits)))

(defthm unsigned-byte-p-8-of-bits-to-byte
  (unsigned-byte-p 8 (bits-to-byte bits))
  :hints (("Goal" :in-theory (enable bits-to-byte))))
