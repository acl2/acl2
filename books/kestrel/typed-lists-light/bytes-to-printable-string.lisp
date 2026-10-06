; Turning bytes into printable chars and strings
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

(defund printable-char-code-p (code)
  (declare (xargs :guard (bytep code)))
  (and (<= 32 code)
       (<= code 126)))

;; Like CODE-CHAR, except turns non-printable chars int dots.
;; Turn a code into a char, but turn unprintable things into dots.
(defund code-char-printable (code)
  (declare (xargs :guard (bytep code)))
  (if (printable-char-code-p code)
      (code-char code)
    #\.))

;; Maps CODE-CHAR over the bytes, except turns non-printable chars int dots.
(defund map-code-char-printable (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (atom bytes)
      nil
    (cons (code-char-printable (first bytes))
          (map-code-char-printable (rest bytes)))))

(defthm character-listp-of-map-code-char-printable
  (character-listp (map-code-char-printable bytes))
  :hints (("Goal" :in-theory (enable map-code-char-printable))))

(defund bytes-to-printable-string (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (coerce (map-code-char-printable bytes) 'string))
