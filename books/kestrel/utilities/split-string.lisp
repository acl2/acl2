; A utility to split a string at a given char
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-chars")

;; Splits the string STR into two parts, the substring before the first
;; occurence of CHAR and the substring after the first occurrence of CHAR.
;; Returns (mv foundp string-before string-after).  If CHAR does not occur in
;; STR, FOUNDP will be nil, STRING-BEFORE will be STR and STRING-AFTER will be
;; the empty string "".
(defund split-string (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (mv-let (foundp chars-before chars-after)
    (split-chars (coerce str 'list) char)
    (mv foundp
        (coerce chars-before 'string)
        (coerce chars-after 'string))))

;; Example: (split-string "ABCDE" #\D)
;; Example: (split-string "ABCDE" #\Z)
