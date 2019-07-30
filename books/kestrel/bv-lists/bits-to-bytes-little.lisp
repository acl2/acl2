; BV Lists library: bits-to-bytes-little
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

;; Convert a list of bits to a list of bytes (little endian)

(include-book "bits-to-byte-little")
(include-book "len-mult-of-8p")
(local (include-book "../lists-light/len"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../lists-light/take"))
(local (include-book "../arithmetic-light/ceiling"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/floor"))

;; Convert a list of bits to a list of bytes.  Earlier bits in the input are
;; used to form earlier bytes in the result. But the first bit in each group of
;; 8 bits becomes the least significant bit of corresponding byte in the
;; result, so this is "little endian".
(defun bits-to-bytes-little (bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 bits)
                              (true-listp bits)
                              (len-mult-of-8p bits))))
  (if (endp bits)
      nil
    (cons (bits-to-byte-little (take 8 bits))
          (bits-to-bytes-little (nthcdr 8 bits)))))

(defthm consp-of-bits-to-bytes-little
  (equal (consp (bits-to-bytes-little bits))
         (consp bits)))

(defthm len-of-bits-to-bytes-little
  (equal (len (bits-to-bytes-little bits))
         (ceiling (len bits) 8)))

(defthm all-unsigned-byte-p-8-of-bits-to-bytes-little
  (all-unsigned-byte-p 8 (bits-to-bytes-little bits)))
