; BV Lists Library: Converting a string to a list of bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "byte-to-bits-little")
(include-book "all-unsigned-byte-p")
(include-book "kestrel/typed-lists-light/map-char-code" :dir :system)

(defun char-codes-to-bit-list-aux (char-codes acc)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 char-codes)
                              (true-listp char-codes)
                              (true-listp acc))))
  (if (endp char-codes)
      (reverse acc)
    (char-codes-to-bit-list-aux (rest char-codes)
                                ;; We use byte-to-bits-little because the acc will be reversed
                                (append (byte-to-bits-little (first char-codes))
                                        acc))))

;; Convert each element of CHAR-CODES to a list of bits (big-endian) and append
;; the results.
(defun char-codes-to-bit-list (char-codes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 char-codes)
                              (true-listp char-codes))))
  (char-codes-to-bit-list-aux char-codes nil))

;; Convert STRING to a list of bytes.
(defun string-to-bytes (string)
  (declare (xargs :guard (stringp string)))
  (map-char-code (coerce string 'list)))

;; Convert STRING to a list of bits, where each character is represented with
;; its most significant bit first (big-endian).
(defun string-to-bits (string)
  (declare (xargs :guard (stringp string)))
  (char-codes-to-bit-list (string-to-bytes string)))
