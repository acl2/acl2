; Turning bytes into printable chars and strings
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system) ; todo: use byte-listp instead?

(defun printable-char-code-p (code)
  (declare (xargs :guard (unsigned-byte-p 8 code)))
  (and (<= 32 code)
       (<= code 126)))

;; Turn a code into a char, but turn unprintable things into dots.
(defun code-char-printable (code)
  (declare (xargs :guard (unsigned-byte-p 8 code)))
  (if (printable-char-code-p code)
      (code-char code)
    #\.))

(defun map-code-char-printable (codes)
  (declare (xargs :guard (acl2::all-unsigned-byte-p 8 codes)))
  (if (atom codes)
      nil
    (cons (code-char-printable (first codes))
          (map-code-char-printable (rest codes)))))

(defun bytes-to-printable-string (bytes)
  (acl2::coerce (map-code-char-printable bytes) 'string))
