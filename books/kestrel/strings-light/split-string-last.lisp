; A utility to split a string at the last occurrence of a given char
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in split-string-last-tests.lisp.

(include-book "split-chars")
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (e/d (true-listp-when-character-listp2)
                       (mv-nth))))

;; Splits the string STR into two parts, the substring before the last
;; occurence of CHAR and the substring after the last occurrence of CHAR.
;; Returns (mv foundp string-before string-after).  If CHAR does not occur in
;; STR, FOUNDP will be nil, STRING-BEFORE will be STR and STRING-AFTER will be
;; the empty string "".
(defund split-string-last (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (let* ((chars (coerce str 'list))
         (rev-chars (reverse chars)))
    ;; note that "before" and "after" are switched here, compared to what is
    ;; typical:
    (mv-let (foundp rev-chars-after rev-chars-before)
      (split-chars rev-chars char)
      (if foundp
          (mv t
              (coerce (reverse rev-chars-before) 'string)
              (coerce (reverse rev-chars-after) 'string))
        (mv nil
            ;; Ensures it's always a string:
            (mbe :logic (if (stringp str) str "")
                 :exec str)
            "")))))

(defthm booleanp-of-mv-nth-0-of-split-string-last
  (booleanp (mv-nth 0 (split-string-last str char)))
  :hints (("Goal" :in-theory (enable split-string-last))))

(defthm stringp-of-mv-nth-1-of-split-string-last
  (stringp (mv-nth 1 (split-string-last str char)))
  :hints (("Goal" :in-theory (enable split-string-last))))

(defthm stringp-of-mv-nth-2-of-split-string-last
  (stringp (mv-nth 2 (split-string-last str char)))
  :hints (("Goal" :in-theory (enable split-string-last))))
