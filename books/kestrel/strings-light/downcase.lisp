; Utilities to downcase characters and strings
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that the function STRING-DOWNCASE is built-in but requires all chars to
;; be "standard characters".  The utilities in this book are more general.

;; Note that STD provides a function, DOWNCASE-STRING, but it is much more
;; heavyweight than this book.

;; Convert CHAR from upper to lower case, if it is an upper-case letter.
;; Otherwise, return CHAR unchanged.
(defund char-downcase-gen (char)
  (declare (xargs :guard (characterp char)))
  (if (standard-char-p char)
      (char-downcase char)
    char))

;; Convert the CHARS from upper to lower case, leaving non-upper-case-letters
;; unchanged.
(defund chars-downcase-gen (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))))
  (if (endp chars)
      (reverse acc)
    (chars-downcase-gen (rest chars) (cons (char-downcase-gen (first chars))
                                           acc))))

(defthm character-listp-of-chars-downcase-gen
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (chars-downcase-gen chars acc)))
  :hints (("Goal" :in-theory (enable chars-downcase-gen))))

;; Convert the characters in STR from upper to lower case, leaving
;; non-upper-case-letters unchanged.
(defund string-downcase-gen (str)
  (declare (xargs :guard (stringp str)))
  (coerce (chars-downcase-gen (coerce str 'list) nil) 'string))

(defthm stringp-of-string-downcase-gen
  (stringp (string-downcase-gen str)))
