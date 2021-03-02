; A utility to split a list of characters at all occurrences of a given char
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/character-list-listp" :dir :system)
(include-book "split-chars")

;; Repeatedly split CHARS at occurrences of CHAR.  Returns a list of lists of
;; chars.  If CHARS starts with CHAR, the result has an empty list at the
;; front.  If CHARS end with CHAR, the result has an empty list at the
;; end.
(defund split-chars-repeatedly (chars char)
  (declare (xargs :guard (and (character-listp chars)
                              (characterp char))
                  :measure (len chars)))
  (if (endp chars)
    (list nil)
    (mv-let (foundp chars-before chars-after)
      (split-chars chars char)
      (if (not foundp)
          (list chars)
      (cons chars-before
            (split-chars-repeatedly chars-after char))))))

;Example (split-chars-repeatedly '(#\a #\b #\0 #\d #\e #\0 #\f #\g) #\0)
;Example (split-chars-repeatedly '(#\0 #\a #\b #\0 #\d #\e #\0 #\f #\g #\0) #\0)

(defthm character-list-listp-split-chars-repeatedly
  (implies (character-listp chars)
           (character-list-listp (split-chars-repeatedly chars char)))
  :hints (("Goal" :in-theory (enable split-chars-repeatedly))))
