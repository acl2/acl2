; Lightweight utilities for parsing decimal digits from strings
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

;; Convert a decimal digit char to a numeric value
(defund decimal-digit-char-value (char)
  (declare (xargs :guard (and (characterp char)
                              (digit-char-p char))))
  (- (char-code char)
     (mbe :logic (char-code #\0)
          :exec 48)))

(defthm natp-of-decimal-digit-char-value
  (implies (and (characterp char)
                (digit-char-p char))
           (natp (decimal-digit-char-value char)))
  :hints (("Goal" :in-theory (enable decimal-digit-char-value))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv res chars) where res is either nil (no decimal digit to parse)
;; or the numeric value of the decimal digit.  And chars is either the original
;; chars (if there is no decimal digit to parse) or the cdr of the original
;; chars.
(defund parse-decimal-digit-from-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (mv nil chars)
    (let ((char (first chars)))
      (if (digit-char-p char)
          (mv (decimal-digit-char-value char)
              (rest chars))
        (mv nil chars)))))

(defthm len-of-mv-nth-1-of-parse-decimal-digit-from-chars-strong-linear
  (implies (mv-nth 0 (parse-decimal-digit-from-chars chars))
           (< (len (mv-nth 1 (parse-decimal-digit-from-chars chars)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

(defthm len-of-mv-nth-1-of-parse-decimal-digit-from-chars-weak-linear
  (<= (len (mv-nth 1 (parse-decimal-digit-from-chars chars)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-digit-from-chars
  (implies (mv-nth 0 (parse-decimal-digit-from-chars chars))
           (natp (mv-nth 0 (parse-decimal-digit-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-digit-from-chars-type
  (or (null (mv-nth 0 (parse-decimal-digit-from-chars chars)))
      (natp (mv-nth 0 (parse-decimal-digit-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-decimal-digit-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-decimal-digit-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

(defthm true-listp-of-mv-nth-1-of-parse-decimal-digit-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-decimal-digit-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-digit-from-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv val chars).
(defund parse-decimal-digits-from-chars (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (natp acc))
                  :measure (len chars)
                  ))
  (mv-let (maybe-val chars)
    (parse-decimal-digit-from-chars chars)
    (if maybe-val
        (parse-decimal-digits-from-chars chars (+ maybe-val (* 10 acc)))
      ;; No more digits:
      (mv acc chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-digits-from-chars
  (implies (and (mv-nth 0 (parse-decimal-digits-from-chars chars acc))
                (natp acc))
           (natp (mv-nth 0 (parse-decimal-digits-from-chars chars acc))))
  :hints (("Goal" :in-theory (enable parse-decimal-digits-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-digits-from-chars-type
  (implies (natp acc)
           (or (null (mv-nth 0 (parse-decimal-digits-from-chars chars acc)))
               (natp (mv-nth 0 (parse-decimal-digits-from-chars chars acc)))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-digits-from-chars))))

(defthm len-of-mv-nth-1-of-parse-decimal-digits-from-chars-weak-linear
  (<= (len (mv-nth 1 (parse-decimal-digits-from-chars chars acc)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-decimal-digits-from-chars))))

(defthm true-listp-of-mv-nth-1-of-parse-decimal-digits-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-decimal-digits-from-chars chars acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-digits-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-decimal-digits-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-decimal-digits-from-chars chars acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-digits-from-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv maybe-val chars).
(defund parse-decimal-number-from-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (res chars)
    (parse-decimal-digit-from-chars chars)
    (if res
        ;; At least one decimal digit is present:
        (parse-decimal-digits-from-chars chars res)
      ;; No decimal digts preseent:
      (mv nil chars))))

(defthm parse-decimal-number-from-chars-len-bound
  (<= (len (mv-nth 1 (parse-decimal-number-from-chars chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (parse-decimal-number-from-chars)
                                  ()))))

(defthm true-listp-of-mv-nth-1-of-parse-decimal-number-from-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-decimal-number-from-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-decimal-number-from-chars))))

(defthm character-listp-of-mv-nth-1-of-parse-decimal-number-from-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-decimal-number-from-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-decimal-number-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-number-from-chars-type
  (or (natp (mv-nth 0 (parse-decimal-number-from-chars chars)))
      (null (mv-nth 0 (parse-decimal-number-from-chars chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-decimal-number-from-chars))))

(defthm natp-of-mv-nth-0-of-parse-decimal-number-from-chars
  (implies (mv-nth 0 (parse-decimal-number-from-chars chars))
           (natp (mv-nth 0 (parse-decimal-number-from-chars chars))))
  :hints (("Goal" :in-theory (enable parse-decimal-number-from-chars))))

;; (parse-decimal-number-from-chars '(#\1 #\2 #\3 #\4 #\5 #\6 #\Z))
;; (parse-decimal-number-from-chars '(#\1 #\2 #\3 #\4 #\5 #\6))
;; (parse-decimal-number-from-chars '(#\7))
;; (parse-decimal-number-from-chars '(#\0))
;; (parse-decimal-number-from-chars '(#\Z))
