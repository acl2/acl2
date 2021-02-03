; Inversion proofs of little-endian conversions between bit lists and byte lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bytes-to-bits-little")
(include-book "bits-to-bytes-little")
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(defthm bits-to-byte-little-of-byte-to-bits-little
  (equal (bits-to-byte-little (byte-to-bits-little byte))
         (bvchop 8 byte))
  :hints (("Goal" :in-theory (enable byte-to-bits-little
                                     bits-to-byte-little
                                     nth))))

(defthm byte-to-bits-little-of-bits-to-byte-little
  (implies (and (<= 8 (len bits))
                (all-unsigned-byte-p 1 bits))
           (equal (byte-to-bits-little (bits-to-byte-little bits))
                  (take 8 bits)))
  :hints (("Goal" :in-theory (enable byte-to-bits-little
                                     bits-to-byte-little
                                     nth))))

(defthm bytes-to-bits-little-of-bits-to-bytes-little
  (implies (and (true-listp x)
                (all-unsigned-byte-p 1 x)
                (len-mult-of-8p x))
           (equal (bytes-to-bits-little (bits-to-bytes-little x))
                  x))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little bits-to-bytes-little))))

(defthm bits-to-bytes-little-of-bytes-to-bits-little
  (implies (and (all-unsigned-byte-p 8 x)
                (true-listp x))
           (equal (bits-to-bytes-little (bytes-to-bits-little x))
                  x))
  :hints (("Goal" :in-theory (enable bytes-to-bits-little bits-to-bytes-little))))

;; Somewhat unusal because the inner function operates on a single byte but the
;; outer function returns a list of bytes.
(defthm bits-to-bytes-little-of-byte-to-bits-little
  (implies (unsigned-byte-p 8 byte)
           (equal (bits-to-bytes-little (byte-to-bits-little byte))
                  (list byte)))
  :hints (("Goal" :expand (bits-to-bytes-little (byte-to-bits-little byte)))))
