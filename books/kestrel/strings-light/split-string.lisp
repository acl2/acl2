; A utility to split a string at the first occurrence of a given char
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in split-string-tests.lisp.

(include-book "split-chars")

(local (in-theory (disable mv-nth)))

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

(defthm booleanp-of-mv-nth-0-of-split-string
  (booleanp (mv-nth 0 (split-string str char)))
  :hints (("Goal" :in-theory (enable split-string))))

(defthm stringp-of-mv-nth-1-of-split-string
  (stringp (mv-nth 1 (split-string str char)))
  :hints (("Goal" :in-theory (enable split-string))))

(defthm stringp-of-mv-nth-2-of-split-string
  (stringp (mv-nth 2 (split-string str char)))
  :hints (("Goal" :in-theory (enable split-string))))

(defthm <-of-length-of-mv-nth-1-of-split-string
  (implies (mv-nth 0 (split-string str char))
           (< (length (mv-nth 1 (split-string str char)))
              (length str)))
  :hints (("Goal" :in-theory (enable split-string))))

(defthm <-of-length-of-mv-nth-2-of-split-string
  (implies (mv-nth 0 (split-string str char))
           (< (length (mv-nth 2 (split-string str char)))
              (length str)))
  :hints (("Goal" :in-theory (enable split-string))))
