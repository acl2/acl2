; A utility to split a string at all occurrences of a given char
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-chars-repeatedly")

;; Coerces each of the CHAR-LISTS to a string, returning a list of strings.
(defund coerce-all-to-string (char-lists)
  (declare (xargs :guard (character-list-listp char-lists)))
  (if (endp char-lists)
      nil
    (cons (coerce (first char-lists) 'string)
          (coerce-all-to-string (rest char-lists)))))

(defthm string-listp-of-coerce-all-to-string
  (implies (character-list-listp char-lists)
           (string-listp (coerce-all-to-string char-lists)))
  :hints (("Goal" :in-theory (enable coerce-all-to-string))))

;; Repeatedly split the string STR at occurrences of CHAR.  Returns a list of
;; strings.  If STR starts with CHAR, the result has an empty string at the
;; front.  If STR end with CHAR, the result has an empty string at the end.
(defund split-string-repeatedly (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (coerce-all-to-string (split-chars-repeatedly (coerce str 'list) char)))

;Example: (split-string-repeatedly "192.168.1.1" #\.)
;Example: (split-string-repeatedly ".192.168.1.1." #\.)
;Example: (split-string-repeatedly "192.168.1.1" #\X)

(defthm string-listp-of-split-string-repeatedly
  (implies (stringp str)
           (string-listp (split-string-repeatedly str char)))
  :hints (("Goal" :in-theory (enable split-string-repeatedly))))
