; Turning bytes into printable chars and strings
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

(defun printable-char-code-p (code)
  (declare (xargs :guard (bytep code)))
  (and (<= 32 code)
       (<= code 126)))

;; Like CODE-CHAR, except turns non-printable chars int dots.
;; Turn a code into a char, but turn unprintable things into dots.
(defun code-char-printable (code)
  (declare (xargs :guard (bytep code)))
  (if (printable-char-code-p code)
      (code-char code)
    #\.))

;; Maps CODE-CHAR over the bytes, except turns non-printable chars int dots.
(defun map-code-char-printable (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (atom bytes)
      nil
    (cons (code-char-printable (first bytes))
          (map-code-char-printable (rest bytes)))))

(defund bytes-to-printable-string (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (coerce (map-code-char-printable bytes) 'string))
