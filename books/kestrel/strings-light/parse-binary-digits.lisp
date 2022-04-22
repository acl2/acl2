; Lightweight utilities for parsing binary digits from strings
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (disable natp mv-nth)))

;; Convert a binary digit char to a numeric value
(defund binary-digit-char-value (char)
  (declare (xargs :guard (and (characterp char)
                              (digit-char-p char 2))))
  (if (equal char #\1)
      1
    0))

(defthm natp-of-binary-digit-char-value
  (implies (and (characterp char)
                (digit-char-p char s))
           (natp (binary-digit-char-value char)))
  :hints (("Goal" :in-theory (enable binary-digit-char-value))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv res chars) where res is either nil (no binary digit to parse)
;; or the numeric value of the binary digit.  And chars is either the original
;; chars (if there is no binary digit to parse) or the cdr of the original
;; chars.
(defund parse-binary-digit-from-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (mv nil chars)
    (let ((char (first chars)))
      (if (digit-char-p char 2)
          (mv (binary-digit-char-value char)
              (rest chars))
        (mv nil chars)))))

(defthm len-of-mv-nth-1-of-parse-binary-digit-from-chars-strong-linear
  (implies (mv-nth 0 (parse-binary-digit-from-chars chars))
           (< (len (mv-nth 1 (parse-binary-digit-from-chars chars)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

(defthm len-of-mv-nth-1-of-parse-binary-digit-from-chars-weak-linear
  (<= (len (mv-nth 1 (parse-binary-digit-from-chars chars)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-digit-from-chars
  (implies (mv-nth 0 (parse-binary-digit-from-chars chars))
           (natp (mv-nth 0 (parse-binary-digit-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-digit-from-chars-type
  (or (null (mv-nth 0 (parse-binary-digit-from-chars chars)))
      (natp (mv-nth 0 (parse-binary-digit-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-binary-digit-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-binary-digit-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

(defthm true-listp-of-mv-nth-1-of-parse-binary-digit-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-binary-digit-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-digit-from-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv val chars).
(defund parse-binary-digits-from-chars (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (natp acc))
                  :measure (len chars)
                  ))
  (mv-let (maybe-val chars)
    (parse-binary-digit-from-chars chars)
    (if maybe-val
        (parse-binary-digits-from-chars chars (+ maybe-val (* 2 acc)))
      ;; No more digits:
      (mv acc chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-digits-from-chars
  (implies (and (mv-nth 0 (parse-binary-digits-from-chars chars acc))
                (natp acc))
           (natp (mv-nth 0 (parse-binary-digits-from-chars chars acc))))
  :hints (("Goal" :in-theory (enable parse-binary-digits-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-digits-from-chars-type
  (implies (natp acc)
           (or (null (mv-nth 0 (parse-binary-digits-from-chars chars acc)))
               (natp (mv-nth 0 (parse-binary-digits-from-chars chars acc)))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-digits-from-chars))))

(defthm len-of-mv-nth-1-of-parse-binary-digits-from-chars-weak-linear
  (<= (len (mv-nth 1 (parse-binary-digits-from-chars chars acc)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-binary-digits-from-chars))))

(defthm true-listp-of-mv-nth-1-of-parse-binary-digits-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-binary-digits-from-chars chars acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-digits-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-binary-digits-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-binary-digits-from-chars chars acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-digits-from-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv maybe-val chars).
(defund parse-binary-number-from-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (res chars)
    (parse-binary-digit-from-chars chars)
    (if res
        ;; At least one binary digit is present:
        (parse-binary-digits-from-chars chars res)
      ;; No binary digts preseent:
      (mv nil chars))))

(defthm parse-binary-number-from-chars-len-bound
  (<= (len (mv-nth 1 (parse-binary-number-from-chars chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (parse-binary-number-from-chars)
                                  ()))))

(defthm true-listp-of-mv-nth-1-of-parse-binary-number-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-binary-number-from-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-binary-number-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-binary-number-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-binary-number-from-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-binary-number-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-number-from-chars-type
  (or (natp (mv-nth 0 (parse-binary-number-from-chars chars)))
      (null (mv-nth 0 (parse-binary-number-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-binary-number-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-binary-number-from-chars
  (implies (mv-nth 0 (parse-binary-number-from-chars chars))
           (natp (mv-nth 0 (parse-binary-number-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-binary-number-from-chars))))

;; (parse-binary-number-from-chars '(#\1 #\0 #\0 #\1 #\0 #\1 #\Z))
;; (parse-binary-number-from-chars '(#\1 #\0 #\0 #\1 #\0 #\1))
;; (parse-binary-number-from-chars '(#\1))
;; (parse-binary-number-from-chars '(#\0))
;; (parse-binary-number-from-chars '(#\Z))
