; Utilities to upcase characters and strings
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that the function STRING-UPCASE is built-in but requires all chars to
;; be "standard characters".  The utilities in this book are more general.

;; Note that STD provides a function, UPCASE-STRING, but it is much more
;; heavyweight than this book.

;; Convert CHAR from upper to lower case, if it is an upper-case letter.
;; Otherwise, return CHAR unchanged.
(defund char-upcase-gen (char)
  (declare (xargs :guard (characterp char)))
  (if (standard-char-p char)
      (char-upcase char)
    char))

;; Convert the CHARS from upper to lower case, leaving non-upper-case-letters
;; unchanged.
(defund chars-upcase-gen (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))))
  (if (endp chars)
      (reverse acc)
    (chars-upcase-gen (rest chars) (cons (char-upcase-gen (first chars))
                                         acc))))

(defthm character-listp-of-chars-upcase-gen
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (chars-upcase-gen chars acc)))
  :hints (("Goal" :in-theory (enable chars-upcase-gen))))

;; Convert the characters in STR from upper to lower case, leaving
;; non-upper-case-letters unchanged.
(defund string-upcase-gen (str)
  (declare (xargs :guard (stringp str)))
  (coerce (chars-upcase-gen (coerce str 'list) nil) 'string))

(defthm stringp-of-string-upcase-gen
  (implies (stringp str)
           (stringp (string-upcase-gen str))))
