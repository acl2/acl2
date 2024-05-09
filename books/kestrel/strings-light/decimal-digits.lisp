; Converting decimal digits to chars and strings
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defconst *decimal-digit-chars* '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

(defund decimal-digit-charp (char)
  (declare (xargs :guard t))
  (member char *decimal-digit-chars*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun decimal-digitp (digit)
  (declare (xargs :guard t))
  (and (natp digit)
       (< digit 10)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See also digit-to-char, but that one also handles hex digits.
(defund decimal-digit-to-char (digit)
  (declare (xargs :guard (decimal-digitp digit)))
  (case digit
    (0 #\0)
    (1 #\1)
    (2 #\2)
    (3 #\3)
    (4 #\4)
    (5 #\5)
    (6 #\6)
    (7 #\7)
    (8 #\8)
    (9 #\9)))

;; Sanity check:
(thm
 (implies (decimal-digitp digit)
          (equal (decimal-digit-to-char digit)
                 (digit-to-char digit))))

(defthm characterp-of-decimal-digit-to-char
  (implies (decimal-digitp digit)
           (characterp (decimal-digit-to-char digit)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable decimal-digit-to-char))))

(defund decimal-digit-to-string (digit)
  (declare (xargs :guard (decimal-digitp digit)))
  (coerce (list (decimal-digit-to-char digit)) 'string))
