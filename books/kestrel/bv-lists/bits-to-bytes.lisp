; BV Lists library: bits-to-bytes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Convert a list of bits to a list of bytes (big endian)

(include-book "bits-to-byte")
(include-book "len-mult-of-8p")
(local (include-book "../lists-light/len"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/take"))
(local (include-book "../lists-light/append"))
(local (include-book "../arithmetic-light/ceiling"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/floor"))

;; Convert each group of 8 bits from BITS into a byte in a big-endian fashion,
;; returning a list of the resulting bytes.  The first element of BITS becomes
;; the most significant bit of the first byte in the result, and so on.
(defun bits-to-bytes (bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 bits)
                              (true-listp bits)
                              (len-mult-of-8p bits))))
  (if (endp bits)
      nil
    (cons (bits-to-byte (take 8 bits))
          (bits-to-bytes (nthcdr 8 bits)))))

(defthm consp-of-bits-to-bytes
  (equal (consp (bits-to-bytes bits))
         (consp bits)))

(defthm len-of-bits-to-bytes
  (equal (len (bits-to-bytes bits))
         (ceiling (len bits) 8)))

(defthm all-unsigned-byte-p-8-of-bits-to-bytes
  (all-unsigned-byte-p 8 (bits-to-bytes bits)))

(defthm bits-to-bytes-of-append
  (implies (len-mult-of-8p bits1)
           (equal (bits-to-bytes (append bits1 bits2))
                  (append (bits-to-bytes bits1)
                          (bits-to-bytes bits2))))
  :hints (("Goal" :in-theory (enable bits-to-bytes)
           :expand (bits-to-bytes (append bits1 bits2)))))
