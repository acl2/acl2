; Inversion theorems about converting between bytes and bit lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bytes-to-bits")
(include-book "bits-to-bytes")
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(defthm byte-to-bits-of-bits-to-byte
  (implies (and (equal 8 (len bits))
                (all-unsigned-byte-p 1 bits)
                (true-listp bits))
           (equal (byte-to-bits (bits-to-byte bits))
                  bits))
  :hints (("Goal" :in-theory (enable byte-to-bits bits-to-byte))))

(defthm bits-to-byte-of-byte-to-bits
  (implies (unsigned-byte-p 8 byte)
           (equal (bits-to-byte (byte-to-bits byte))
                  byte))
  :hints (("Goal" :in-theory (enable byte-to-bits bits-to-byte))))

(defthm bytes-to-bits-of-bits-to-bytes
  (implies (and (len-mult-of-8p bits)
                (all-unsigned-byte-p 1 bits)
                (true-listp bits))
           (equal (bytes-to-bits (bits-to-bytes bits))
                  bits))
  :hints (("Goal" :in-theory (enable))))

(defthm bits-to-bytes-of-bytes-to-bits
  (implies (and (all-unsigned-byte-p 8 bytes)
                (true-listp bytes))
           (equal (bits-to-bytes (bytes-to-bits bytes))
                  bytes))
  :hints (("Goal" :in-theory (enable bytes-to-bits
                                     bits-to-bytes
                                     len-mult-of-8p)
           :expand (bits-to-bytes (byte-to-bits (car bytes))))))

;; Somewhat unusal because the inner function operates on a single byte but the
;; outer function returns a list of bytes.
(defthm bits-to-bytes-of-byte-to-bits
  (implies (unsigned-byte-p 8 byte)
           (equal (bits-to-bytes (byte-to-bits byte))
                  (list byte)))
  :hints (("Goal" :expand (bits-to-bytes (byte-to-bits byte)))))
