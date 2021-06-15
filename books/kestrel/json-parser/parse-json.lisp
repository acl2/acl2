; A simple JSON parser
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also parse-json-file.lisp, for a wrapper of this tool that reads the
;; JSON from a file.

;; Written from http://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf.

;; This parser works best if its input is encoded in UTF-8 (regular ASCII text
;; is compatible with UTF-8).  The names and strings in the output of this
;; parser are also encoded in UTF-8.

;; This parser does handle Unicode escapes (character sequences starting with
;; \u).

;; For maximum clarity, we could restructure the parser implementation to first
;; decode the entire input to create a sequence of Unicode code points, then
;; process those code points as JSON, re-encoding any strings/names encountered
;; as UTF-8.  However, it seems that UTF-8 encodings would then simply pass
;; through our implementation unchanged, so we don't so that.

;; This parser does not check that its input is valid UTF-8.  So characters,
;; and sequences of characters, that are not allowed in UTF-8 (such as any
;; occurence of the character whose code is 255) are just passed through.

;; TODO: If whitespace is optional, what if it occurs between digits?

;; TODO: Handle commas in lists and objects more elegantly.

;; TODO: Return more helpful information in the case of errors.

(include-book "tools/flag" :dir :system)
(include-book "kestrel/unicode-light/hex-digit-chars-to-code-point" :dir :system)
(include-book "kestrel/unicode-light/code-point-to-utf-8-chars" :dir :system)
(include-book "kestrel/unicode-light/surrogates" :dir :system)
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable mv-nth)))

;dup
(defund prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(local (in-theory (enable prefixp ;todo
                          true-listp-when-character-listp2)))

;; Returns a suffix of chars.
(defund skip-json-whitespace (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (if (member (first chars) '(#\Tab #\Newline #\Return #\Space))
        (skip-json-whitespace (rest chars))
      chars)))

(defthm len-of-skip-json-whitespace-bound
  (<= (len (skip-json-whitespace chars))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-json-whitespace))))

(defthm character-listp-of-skip-json-whitespace
  (implies (character-listp chars)
           (character-listp (skip-json-whitespace chars)))
  :hints (("Goal" :in-theory (enable skip-json-whitespace))))

;; Returns (mv erp parsed-token remaining-chars).  We parse the true literal
;; true as the symbol :TRUE.
(defund parse-json-true-literal (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (prefixp '(#\t #\r #\u #\e) chars)
      (mv nil :true (nthcdr 4 chars))
    (mv :bad-true-literal nil chars)))

(defthm len-of-mv-nth-2-of-parse-json-true-literal
  (implies (not (mv-nth 0 (parse-json-true-literal chars)))
           (equal (len (mv-nth 2 (parse-json-true-literal chars)))
                  (+ -4 (len chars))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-true-literal))))

(defthm character-listp-of-mv-nth-2-of-parse-json-true-literal
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-true-literal chars))))
  :hints (("Goal" :in-theory (enable parse-json-true-literal))))

;; Returns (mv erp parsed-token remaining-chars).  We parse the false literal
;; true as the symbol :FALSE.
(defund parse-json-false-literal (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (prefixp '(#\f #\a #\l #\s #\e) chars)
      (mv nil :false (nthcdr 5 chars))
    (mv :bad-false-literal nil chars)))

(defthm len-of-mv-nth-2-of-parse-json-false-literal
  (implies (not (mv-nth 0 (parse-json-false-literal chars)))
           (equal (len (mv-nth 2 (parse-json-false-literal chars)))
                  (+ -5 (len chars))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-false-literal))))

(defthm character-listp-of-mv-nth-2-of-parse-json-false-literal
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-false-literal chars))))
  :hints (("Goal" :in-theory (enable parse-json-false-literal))))

;; Returns (mv erp parsed-token remaining-chars).  We parse the null literal
;; true as the symbol :NULL.
(defund parse-json-null-literal (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (prefixp '(#\n #\u #\l #\l) chars)
      (mv nil :null (nthcdr 4 chars))
    (mv (cons :bad-null-literal chars) nil chars)))

(defthm len-of-mv-nth-2-of-parse-json-null-literal
  (implies (not (mv-nth 0 (parse-json-null-literal chars)))
           (equal (len (mv-nth 2 (parse-json-null-literal chars)))
                  (+ -4 (len chars))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-null-literal))))

(defthm character-listp-of-mv-nth-2-of-parse-json-null-literal
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-null-literal chars))))
  :hints (("Goal" :in-theory (enable parse-json-null-literal))))

;; Returns (mv erp code-point remaining-chars)
(defund parse-4-hex-chars-as-code-point (chars)
  (declare (xargs :guard (character-listp chars)
                  :guard-hints (("Goal" :in-theory (enable <-16-of-mv-nth-1-of-hex-char-to-val-forward)))))
  (if (not (consp (rest (rest (rest chars)))))
      (mv :too-few-unicode-digits 0 chars)
    (let ((digit1 (first chars))
          (digit2 (second chars))
          (digit3 (third chars))
          (digit4 (fourth chars)))
      (mv-let (erp code-point)
        (hex-digit-chars-to-code-point digit1 digit2 digit3 digit4)
        (if erp ; happens if there are bad hex digits
            (mv erp 0 chars)
          (mv nil ; no error
              code-point
              (rest (rest (rest (rest chars))))))))))

(defthm natp-of-mv-nth-1-of-parse-4-hex-chars-as-code-point
  (natp (mv-nth 1 (parse-4-hex-chars-as-code-point chars)))
  :hints (("Goal" :in-theory (enable parse-4-hex-chars-as-code-point))))

(defthm <-of-mv-nth-1-of-parse-4-hex-chars-as-code-point
  (<= (mv-nth 1 (parse-4-hex-chars-as-code-point chars))
      #x10FFFF)
  :hints (("Goal" :in-theory (enable parse-4-hex-chars-as-code-point))))

(defthm character-listp-of-mv-nth-2-of-parse-4-hex-chars-as-code-point
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-4-hex-chars-as-code-point chars))))
  :hints (("Goal" :in-theory (enable parse-4-hex-chars-as-code-point))))

(defthm true-listp-of-mv-nth-2-of-parse-4-hex-chars-as-code-point
  (implies (true-listp chars)
           (true-listp (mv-nth 2 (parse-4-hex-chars-as-code-point chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-4-hex-chars-as-code-point))))

(defthm len-of-mv-nth-2-of-parse-4-hex-chars-as-code-point-bound
  (implies (not (mv-nth 0 (parse-4-hex-chars-as-code-point chars)))
           (< (len (mv-nth 2 (parse-4-hex-chars-as-code-point chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-4-hex-chars-as-code-point))))

;; Parse the 4 hex digits of a Unicode escape, possibly followed by another
;; entire Unicode escape (the \u and the 4 hex digits). We have already
;; consumed the leading \u sequence of the first escape.
;; Returns (mv erp result-chars remaining-chars).
(defund parse-unicode-escape (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (erp code-point chars)
    (parse-4-hex-chars-as-code-point chars)
    (if erp
        (mv erp nil chars)
      (if (low-surrogatep code-point)
          (mv :unexpected-low-surrogate nil chars)
        (if (high-surrogatep code-point)
            ;; Need to parse the upcoming low surrogate and combine:
            (if (not (consp (cdr chars)))
                (mv :not-enough-bytes-for-low-surrogate nil chars)
              (if (not (and (equal #\\ (first chars))
                            (equal #\u (second chars))))
                  (mv :ill-formed-low-surrogate-escape nil chars)
                (let ((chars (rest (rest chars)))) ; skip the \u
                  (mv-let (erp second-code-point chars)
                    (parse-4-hex-chars-as-code-point chars)
                    (if erp
                        (mv erp nil chars)
                      (if (not (low-surrogatep second-code-point))
                          (mv :code-point-not-a-low-surrogate nil chars)
                        ;; Combine the bits from the high and low surrogate and convert the resulting code-point to UTF-8:
                        (mv nil ; no error
                            (code-point-to-utf-8-chars (combine-utf-16-surrogates code-point second-code-point))
                            chars)))))))
          ;; Not a surrogate, so we have the entire code-point:
          ;; Convert the code-point to UTF-8:
          (mv nil ; no error
              (code-point-to-utf-8-chars code-point)
              chars))))))

(defthm character-listp-of-mv-nth-1-of-parse-unicode-escape
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-unicode-escape chars))))
  :hints (("Goal" :in-theory (enable parse-unicode-escape))))

(defthm character-listp-of-mv-nth-2-of-parse-unicode-escape
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-unicode-escape chars))))
  :hints (("Goal" :in-theory (enable parse-unicode-escape))))

(defthm len-of-mv-nth-2-of-parse-unicode-escape-bound
  (implies (not (mv-nth 0 (parse-unicode-escape chars)))
           (< (len (mv-nth 2 (parse-unicode-escape chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-unicode-escape))))

(defconst *json-control-chars*
  (list (code-char #x0)
        (code-char #x1)
        (code-char #x2)
        (code-char #x3)
        (code-char #x4)
        (code-char #x5)
        (code-char #x6)
        (code-char #x7)
        (code-char #x8)
        (code-char #x9)
        (code-char #xA)
        (code-char #xB)
        (code-char #xC)
        (code-char #xD)
        (code-char #xE)
        (code-char #xF)
        (code-char #x10)
        (code-char #x11)
        (code-char #x12)
        (code-char #x13)
        (code-char #x14)
        (code-char #x15)
        (code-char #x16)
        (code-char #x17)
        (code-char #x18)
        (code-char #x19)
        (code-char #x1A)
        (code-char #x1B)
        (code-char #x1C)
        (code-char #x1D)
        (code-char #x1E)
        (code-char #x1F)))

;; Returns (mv erp result-chars remaining-chars).
(defund parse-json-string-char (chars)
  (declare (xargs :guard (and (character-listp chars)
                              (consp chars)
                              (not (equal (first chars) #\")))))
  (let ((first-char (first chars))
        (rest-chars (rest chars)))
    (if (eql first-char #\\)
        (if (endp rest-chars)
            (mv :empty-escape-sequence-in-string
                nil
                chars)
          (let ((char-after-backslash (first rest-chars)))
            (cond ((equal char-after-backslash #\") ;quotation mark
                   (mv nil (list #\") (rest rest-chars)))
                  ((equal char-after-backslash #\\) ;reverse solidus
                   (mv nil (list #\\) (rest rest-chars)))
                  ((equal char-after-backslash #\/) ;solidus
                   (mv nil (list #\/) (rest rest-chars)))
                  ((equal char-after-backslash #\b) ;backspace
                   (mv nil (list (code-char #x8)) (rest rest-chars)))
                  ((equal char-after-backslash #\f) ;form feed
                   (mv nil (list (code-char #xC)) (rest rest-chars)))
                  ((equal char-after-backslash #\n) ;line feed
                   (mv nil (list (code-char #xA)) (rest rest-chars)))
                  ((equal char-after-backslash #\r) ;carriage return
                   (mv nil (list (code-char #xD)) (rest rest-chars)))
                  ((equal char-after-backslash #\t) ;character tabulation
                   (mv nil (list (code-char #x9)) (rest rest-chars)))
                  ((equal char-after-backslash #\u) ;a unicode char
                   ;; May consume up to 12 characters:
                   (parse-unicode-escape (rest rest-chars)))
                  (t
                   (mv :ill-formed-escape-sequence-in-string nil chars)))))
      (if (member first-char *json-control-chars*)
          (mv :unescaped-control-character nil chars)
        ;; Normal case:
        (mv nil (list first-char) rest-chars)))))

(defthm mv-nth-2-of-parse-json-string-char-bound
  (implies (and (not (mv-nth 0 (parse-json-string-char chars)))
                (consp chars))
           (< (len (mv-nth 2 (parse-json-string-char chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-string-char))))

(defthm character-listp-of-mv-nth-2-of-parse-json-string-char
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-string-char chars))))
  :hints (("Goal" :in-theory (enable parse-json-string-char))))

(defthm character-listp-of-mv-nth-1-of-parse-json-string-char
  (implies (and (character-listp chars)
                (consp chars))
           (character-listp (mv-nth 1 (parse-json-string-char chars))))
  :hints (("Goal" :in-theory (enable parse-json-string-char))))

(defthm len-of-mv-nth-2-of-parse-json-string-char-bound
  (implies (and (not (mv-nth 0 (parse-json-string-char chars)))
                (consp chars))
           (< (len (mv-nth 2 (parse-json-string-char chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-string-char))))

;; Returns (mv erp parsed-chars remaining-chars).
(defund parse-json-string-chars-and-final-quote (chars)
  (declare (xargs :guard (character-listp chars)
                  :measure (len chars)))
  (if (endp chars)
      (mv :no-closing-quote nil chars)
    (let ((first-char (first chars)))
      (if (eql first-char #\") ;found the end of the string
          (mv nil nil (rest chars))
        (mv-let (erp parsed-char chars)
          (parse-json-string-char chars)
          (if erp
              (mv erp nil chars)
            (mv-let (erp parsed-chars chars)
              (parse-json-string-chars-and-final-quote chars)
              (if erp
                  (mv erp nil chars)
                (mv nil
                    (append parsed-char parsed-chars)
                    chars)))))))))

(defthm len-of-mv-nth-2-of-parse-json-string-chars-and-final-quote-bound
  (implies (not (mv-nth 0 (parse-json-string-chars-and-final-quote chars)))
           (< (len (mv-nth 2 (parse-json-string-chars-and-final-quote chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-string-chars-and-final-quote))))

(defthm character-listp-of-mv-nth-2-of-parse-json-string-chars-and-final-quote
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-string-chars-and-final-quote chars))))
  :hints (("Goal" :in-theory (enable parse-json-string-chars-and-final-quote))))

(defthm character-listp-of-mv-nth-1-of-parse-json-string-chars-and-final-quote
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-json-string-chars-and-final-quote chars))))
  :hints (("Goal" :in-theory (enable parse-json-string-chars-and-final-quote))))

;; Parse a string, including the closing quote.  Returns (mv erp parsed-string
;; remaining-chars).
(defund parse-json-string (chars)
  (declare (xargs :guard (and (character-listp chars)
                              (eql #\" (first chars)))))
  (let ((chars (cdr chars))) ;Skip the opening double quote
    (mv-let (erp parsed-chars chars)
      (parse-json-string-chars-and-final-quote chars)
      (if erp
          (mv erp "" chars)
        (mv nil (coerce parsed-chars 'string) chars)))))

(defthm len-of-mv-nth-2-of-parse-json-string-bound
  (implies (not (mv-nth 0 (parse-json-string chars)))
           (< (len (mv-nth 2 (parse-json-string chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-string))))

(defthm character-listp-of-mv-nth-2-of-parse-json-string
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-string chars))))
  :hints (("Goal" :in-theory (enable parse-json-string))))

(defthm stringp-of-mv-nth-1-of-parse-json-string
  (implies (character-listp chars)
           (stringp (mv-nth 1 (parse-json-string chars))))
  :hints (("Goal" :in-theory (enable parse-json-string))))

(defund char-value (char)
  (declare (xargs :guard (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
  (- (char-code char)
     (char-code #\0)))

;; Parse 0 or more JSON digits.  Returns (mv parsed-digits num-digits-parsed
;; remaining-chars) where parsed-digits is the numeric value of the digits.
;; Cannot throw an error.
;; TODO: Optimize this to not call expt.
(defund parse-json-digits (chars)
  (declare (xargs :guard (character-listp chars)
                  :verify-guards nil ;done below
                  ))
  (if (endp chars)
      (mv 0 0 chars) ;we can say that a lack of digits represents a value of 0
    (let ((char (first chars)))
      (if (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
          (mv-let (parsed-rest-digits num-rest-digits chars)
            (parse-json-digits (rest chars))
            (mv (+ (* (expt 10 num-rest-digits) (char-value char)) parsed-rest-digits)
                (+ 1 num-rest-digits)
                chars))
        (mv 0 0 chars) ;we can say that a lack of digits represents a value of 0
        ))))

(local
 (defthm natp-of-expt
   (implies (and (natp r)
                 (natp i))
            (natp (expt r i)))
   :rule-classes :type-prescription))

(defthm natp-of-mv-nth-1-of-parse-json-digits
  (natp (mv-nth 1 (parse-json-digits chars)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable parse-json-digits))))

(defthm natp-of-mv-nth-0-of-parse-json-digits
  (natp (mv-nth 0 (parse-json-digits chars)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable parse-json-digits))))

(verify-guards parse-json-digits)

(defthm character-listp-of-mv-nth-2-of-parse-json-digits
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-digits chars))))
  :hints (("Goal" :in-theory (enable parse-json-digits))))

(defthm len-of-mv-nth-2-of-parse-json-digits-bound-when-digit-bound
  (implies (and (consp chars)
                (member (first chars) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))
           (< (len (mv-nth 2 (parse-json-digits chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-digits))))

(defthm len-of-mv-nth-2-of-parse-json-digits-bound-bound
  (<= (len (mv-nth 2 (parse-json-digits chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-digits))))

;; Parse the integer part (the part before any decimal point or exponent) of a
;; number without a leading minus sign.  At least one such digit must
;; exist. Returns (mv erp parsed-integer-part remaining-chars).
(defund parse-integer-part-of-json-number (chars)
  (declare (xargs :guard (and (character-listp chars)
                              ;;(consp chars)
                              ;;(member (first chars) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
                              )))
  (if (not (consp chars))
      (mv :empty-number 0 chars)
    (let ((char (first chars)))
      (if (eql char #\0)
          ;; If the integer part starts with 0, it must be just a single 0 (no
          ;; leading zeros are allowed)
          (mv nil 0 (rest chars))
        (if (member char '(#\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
            (mv-let (parsed-rest-digits num-rest-digits chars)
              (parse-json-digits (rest chars))
              (mv nil
                  (+ (* (expt 10 num-rest-digits) (char-value char)) parsed-rest-digits)
                  chars))
          (mv :invalid-number 0 chars))))))

;todo: this sort of thing could be automated
(defthm natp-of-mv-nth-1-of-parse-integer-part-of-json-number
  (natp (mv-nth 1 (parse-integer-part-of-json-number chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-integer-part-of-json-number))))

;todo: this sort of thing could be automated
(defthm character-listp-of-mv-nth-2-of-parse-integer-part-of-json-number
  (implies (and; (consp chars)
                (character-listp chars))
           (character-listp (mv-nth 2 (parse-integer-part-of-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-integer-part-of-json-number))))

(defthm len-of-mv-nth-2-of-parse-integer-part-of-json-number-bound
  (implies (not (mv-nth 0 (parse-integer-part-of-json-number chars)))
           (< (len (mv-nth 2 (parse-integer-part-of-json-number chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-integer-part-of-json-number))))

;; Returns (mv erp parsed-digits num-digits remaining-chars).
(defund parse-one-or-more-json-digits (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (not (consp chars))
      (mv :no-digit-found 0 0 chars)
    (let ((char (first chars)))
      (if (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
          (mv-let (parsed-digits num-digits chars)
            (parse-json-digits chars)
            (mv nil parsed-digits num-digits chars))
        (mv :non-digit-found 0 0 chars)))))

(defthm natp-of-mv-nth-1-of-parse-one-or-more-json-digits
  (natp (mv-nth 1 (parse-one-or-more-json-digits chars)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-one-or-more-json-digits))))

(defthm natp-of-mv-nth-2-of-parse-one-or-more-json-digits
  (implies (character-listp chars)
           (natp (mv-nth 2 (parse-one-or-more-json-digits chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-one-or-more-json-digits))))

(defthm character-listp-of-mv-nth-3-of-parse-one-or-more-json-digits
  (implies (character-listp chars)
           (character-listp (mv-nth 3 (parse-one-or-more-json-digits chars))))
  :hints (("Goal" :in-theory (enable parse-one-or-more-json-digits))))

(defthm len-of-mv-nth-3-of-parse-one-or-more-json-digits-bound
  (<= (len (mv-nth 3 (parse-one-or-more-json-digits chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-one-or-more-json-digits))))


;; Parse a decimal point followed by one or more digits, if present. Returns
;; (mv erp parsed-number remaining-chars).  A decimal point not followed by at
;; least one digit is an error.
(defund parse-fractional-part-of-json-number (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (mv nil 0 chars) ;no fractional part present
    (let ((char (first chars)))
      (if (eql char #\.)
          (let ((chars (rest chars))) ;skip the decimal point
            (if (endp chars)
                (mv :empty-fractional-part 0 chars)
              (mv-let (erp parsed-digits num-digits chars)
                (parse-one-or-more-json-digits chars)
                (if erp
                    (mv erp 0 nil)
                  (mv nil
                      (/ parsed-digits (expt 10 num-digits))
                      chars)))))
        ;; no fractional part present:
        (mv nil 0 chars)))))

(defthm rationalp-of-mv-nth-1-of-parse-fractional-part-of-json-number
  (implies (and; (consp chars)
                (character-listp chars))
           (rationalp (mv-nth 1 (parse-fractional-part-of-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-fractional-part-of-json-number))))

(defthm character-listp-of-mv-nth-2-of-parse-fractional-part-of-json-number
  (implies (and; (consp chars)
                (character-listp chars))
           (character-listp (mv-nth 2 (parse-fractional-part-of-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-fractional-part-of-json-number))))

(defthm len-of-mv-nth-2-of-parse-fractional-part-of-json-number-bound
  (<= (len (mv-nth 2 (parse-fractional-part-of-json-number chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-fractional-part-of-json-number))))

;; Parse an e or E followed by an optional sign and one of more digits, if
;; present. Returns (mv erp parsed-exponent-part remaining-chars).  An e or E
;; not followed by at least one digit (possibly after a sign) is an error.
(defund parse-exponent-part-of-json-number (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (mv nil 0 chars) ;no exponent part present
    (let ((first-char (first chars)))
      (if (not (member first-char '(#\e #\E)))
          (mv nil 0 chars)        ;no exponent part present
        (let ((chars (rest chars))) ;skip the e or E
          (let ((possible-sign (first chars)))
            (if (member possible-sign '(#\+ #\-))
                (mv-let (erp parsed-digits num-digits chars)
                  (parse-one-or-more-json-digits (rest chars))
                  (declare (ignore num-digits))
                  (if erp
                      (mv erp 0 chars)
                    (mv nil
                        (* (if (eql possible-sign #\-) -1 1)
                           parsed-digits)
                        chars)))
              (mv-let (erp parsed-digits num-digits chars)
                (parse-one-or-more-json-digits chars)
                (declare (ignore num-digits))
                (if erp
                    (mv erp 0 chars)
                  (mv nil
                      parsed-digits
                      chars))))))))))

(defthm integerp-of-mv-nth-1-of-parse-exponent-part-of-json-number
  (integerp (mv-nth 1 (parse-exponent-part-of-json-number chars)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-exponent-part-of-json-number))))

(defthm character-listp-of-mv-nth-2-of-parse-exponent-part-of-json-number
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-exponent-part-of-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-exponent-part-of-json-number))))

(defthm len-of-mv-nth-2-of-parse-exponent-part-of-json-number-bound
  (<= (len (mv-nth 2 (parse-exponent-part-of-json-number chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-exponent-part-of-json-number))))

;; Parse a number without a leading minus sign.  Returns (mv erp parsed-number
;; remaining-chars).
(defund parse-non-negative-json-number (chars)
  (declare (xargs :guard (and (character-listp chars)
;                              (consp chars)
;(member (first chars) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
                              )))
  (mv-let (erp parsed-integer-part chars)
    (parse-integer-part-of-json-number chars)
    (if erp
        (mv erp 0 chars)
      (mv-let (erp parsed-fractional-part chars)
        (parse-fractional-part-of-json-number chars)
        (if erp
            (mv erp 0 chars)
      (mv-let (erp parsed-exponent-part chars)
        (parse-exponent-part-of-json-number chars)
        (if erp
            (mv erp 0 chars)
          (mv nil
              (* (+ parsed-integer-part parsed-fractional-part)
                 (expt 10 parsed-exponent-part))
              chars))))))))

(defthm rationalp-of-mv-nth-1-of-parse-non-negative-json-number
  (implies (character-listp chars)
           (rationalp (mv-nth 1 (parse-non-negative-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-non-negative-json-number))))

(defthm character-listp-of-mv-nth-2-of-parse-non-negative-json-number
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-non-negative-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-non-negative-json-number))))

(defthm len-of-mv-nth-2-of-parse-non-negative-json-number-bound
  (implies (not (mv-nth 0 (parse-non-negative-json-number chars)))
           (< (len (mv-nth 2 (parse-non-negative-json-number chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-non-negative-json-number))))

;; Parse a number.  Returns (mv erp parsed-number remaining-chars).
(defund parse-json-number (chars)
  (declare (xargs :guard (and (character-listp chars)
                              (consp chars)
                              (member (first chars) '(#\- #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))))
  (let ((first-char (first chars)))
    (if (eql first-char #\-)
        (mv-let (erp parsed-number chars)
          (parse-non-negative-json-number (rest chars))
          (if erp
              (mv erp 0 chars)
            (mv nil
                (* -1 parsed-number)
                chars)))
      (parse-non-negative-json-number chars))))

(defthm rationalp-of-mv-nth-1-of-parse-json-number
  (implies (character-listp chars)
           (rationalp (mv-nth 1 (parse-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-json-number))))

(defthm len-of-mv-nth-2-of-parse-json-number-bound
  (implies (not (mv-nth 0 (parse-json-number chars)))
           (< (len (mv-nth 2 (parse-json-number chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-json-number))))

(defthm character-listp-of-mv-nth-2-of-parse-json-number
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-json-number chars))))
  :hints (("Goal" :in-theory (enable parse-json-number))))

(defun json-tokenp (tok)
  (declare (xargs :guard t))
  (or (member-eq tok '(:left-bracket :left-brace :right-bracket :right-brace :colon :comma
                                     :true :false :null))
      (stringp tok)
      (rationalp tok)))

(defun json-token-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (json-tokenp (first l))
         (json-token-listp (rest l)))))

(defthm json-token-listp-of-cdr
  (implies (json-token-listp tokens)
           (json-token-listp (cdr tokens)))
  :hints (("Goal" :in-theory (enable json-token-listp))))

(defthm json-token-listp-of-revappend
  (implies (and (json-token-listp x)
                (json-token-listp y))
           (json-token-listp (revappend x y)))
  :hints (("Goal" :in-theory (enable revappend))))

;; Returns (mv erp tokens).
(defund tokenize-json-chars-aux (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (true-listp acc))
                  :measure (len chars)))
  (let ((chars (skip-json-whitespace chars)))
    (if (endp chars)
        (mv nil (reverse acc))
      (let ((char (first chars)))
        (cond
         ((eql char #\{) (tokenize-json-chars-aux (rest chars) (cons :left-brace acc)))
         ((eql char #\}) (tokenize-json-chars-aux (rest chars) (cons :right-brace acc)))
         ((eql char #\[) (tokenize-json-chars-aux (rest chars) (cons :left-bracket acc)))
         ((eql char #\]) (tokenize-json-chars-aux (rest chars) (cons :right-bracket acc)))
         ((eql char #\:) (tokenize-json-chars-aux (rest chars) (cons :colon acc)))
         ((eql char #\,) (tokenize-json-chars-aux (rest chars) (cons :comma acc)))
         ((eql char #\t) ;; is the character is t, the token must be "true"
          (mv-let (erp tok chars)
            (parse-json-true-literal chars)
            (if erp
                (mv erp nil)
              (tokenize-json-chars-aux chars (cons tok acc)))))
         ((eql char #\f) ;; is the character is t, the token must be "false"
          (mv-let (erp tok chars)
            (parse-json-false-literal chars)
            (if erp
                (mv erp nil)
              (tokenize-json-chars-aux chars (cons tok acc)))))
         ((eql char #\n) ;; is the character is n, the token must be "null"
          (mv-let (erp tok chars)
            (parse-json-null-literal chars)
            (if erp
                (mv erp nil)
              (tokenize-json-chars-aux chars (cons tok acc)))))
         ((member char '(#\- #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
          (mv-let (erp parsed-number chars)
            (parse-json-number chars)
            (if erp
                (mv erp nil)
              (tokenize-json-chars-aux chars (cons parsed-number acc)))))
         ((eql char #\")
          (mv-let (erp parsed-string chars)
            (parse-json-string chars)
            (if erp
                (mv erp nil)
              (tokenize-json-chars-aux chars (cons parsed-string acc)))))
         (t (mv ;; print 20 characters starting with the bad char, for debugging
             (list :bad-token-at (coerce (take (min 20 (len chars)) chars) 'string))
             nil)))))))

(defthm true-listp-of-mv-nth-1-of-tokenize-json-chars-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (tokenize-json-chars-aux chars acc))))
  :hints (("Goal" :in-theory (enable tokenize-json-chars-aux))))

(defthm json-token-listp-of-mv-nth-1-of-tokenize-json-chars-aux
  (implies (and (json-token-listp acc)
                (not (mv-nth 0 (tokenize-json-chars-aux chars acc)))
                (character-listp chars))
           (json-token-listp (mv-nth 1 (tokenize-json-chars-aux chars acc))))
  :hints (("Goal" :in-theory (enable tokenize-json-chars-aux
                                     parse-json-true-literal
                                     parse-json-false-literal
                                     parse-json-null-literal))))

(defund tokenize-json-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (tokenize-json-chars-aux chars nil))

(defthm true-listp-of-mv-nth-1-of-tokenize-json-chars
  (true-listp (mv-nth 1 (tokenize-json-chars chars)))
  :hints (("Goal" :in-theory (enable tokenize-json-chars))))

(defthm json-token-listp-of-mv-nth-1-of-tokenize-json-chars
  (implies (and (not (mv-nth 0 (tokenize-json-chars chars)))
                (character-listp chars))
           (json-token-listp (mv-nth 1 (tokenize-json-chars chars))))
  :hints (("Goal" :in-theory (enable tokenize-json-chars))))

;speed up proofs:
(local (in-theory (disable member-equal
                           o< make-ord
                           )))

(local
 (defthm not-o<-self
   (not (o< fco1 fco1))
   :hints (("Goal" :in-theory (enable o<)))))

(local
 (defthm not-<-self
   (not (< fco1 fco1))))

(local
 (defthm o<-of-make-ord-and-make-ord-same-fe-and-rst
   (equal (o< (make-ord fe fco1 rst)
              (make-ord fe fco2 rst))
          (< fco1 fco2))
   :hints (("Goal" :in-theory (enable o< make-ord)))))

(local
 (defthm o<-of-make-ord-and-make-ord-same-fe
  (equal (o< (make-ord fe fco1 rst1)
             (make-ord fe fco2 rst2))
         (if (equal fco1 fco2)
             (o< rst1 rst2)
           (< fco1 fco2)))
  :hints (("Goal" :in-theory (enable o< make-ord)))))

(local
 (defthm o-p-of-make-ord-suff
   (implies (and (posp fco)
                 (posp fe)
                 (natp rst))
            (o-p (make-ord fe fco rst)))
   :hints (("Goal" :in-theory (enable make-ord o-p o<)))))


(mutual-recursion

 ;; Parse the pairs in the object and the closing curly brace.  We have already
 ;; consumed the opening curly brace.  Returns (mv erp parsed-object
 ;; remaining-tokens).
 (defund parse-json-object (tokens acc)
   (declare (xargs :guard (and (true-listp tokens)
                               (true-listp acc))
                   :measure (make-ord 1 (+ 1 (len tokens)) 1)
                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                   :verify-guards nil ;done below
                   ))
   (if (not (consp tokens))
       (mv :no-right-brace nil tokens)
     (let ((first-token (first tokens)))
       (if (eq :right-brace first-token) ;found the end of the object
           (mv nil (list :object (reverse acc)) (rest tokens))
         ;; Must be a string, then a colon, then a value, then perhaps a comma
         (if (not (stringp first-token))
             (mv :bad-pairs nil tokens)
           (if (not (and (consp (rest tokens))
                         (eq :colon (second tokens))))
               (mv :missing-colon nil tokens)
             (mv-let (erp parsed-value tokens2)
               (parse-json-value (rest (rest tokens)))
               (if erp
                   (mv erp nil tokens)
                 (if (not (mbt (< (len tokens2) (len tokens))))
                     (mv t nil tokens)
                   ;; check for the comma (must be present if no :right-brace) and skip it
                   (if (not (consp tokens2))
                       (mv :missing-comma-and-right-brace nil tokens2)
                     (let ((lookahead-token (first tokens2)))
                       (if (eq :right-brace lookahead-token)
                           (parse-json-object tokens2 (cons (cons first-token parsed-value) acc)) ;finish up
                         (if (eq :comma lookahead-token)
                             (if (not (consp (rest tokens2)))
                                 (mv :missing-final-element-and-right-brace nil tokens2)
                               (if (eq :right-brace (second tokens2))
                                   (mv :extra-comma nil tokens2)
                                 (parse-json-object (rest tokens2) ;skip the comma
                                                          (cons (cons first-token parsed-value) acc))))
                           (mv :missing-comma-in-object nil tokens2))))))))))))))

 ;; Parse the comma-separated values in the array and the closing bracket.  We have already consumed the opening bracket.
 ;; Returns (mv erp parsed-array-value remaining-tokens).
 (defund parse-json-array (tokens acc)
   (declare (xargs :guard (and (true-listp tokens)
                               (true-listp acc))
                   :measure (make-ord 1 (+ 1 (len tokens)) 1)
                   :measure-debug t
                   ))
   (if (not (consp tokens))
       (mv :no-right-bracket nil tokens)
     (let ((first-token (first tokens)))
       (if (eq :right-bracket first-token) ;found the end of the array
           (mv nil (list :array (reverse acc)) (rest tokens))
         (mv-let (erp parsed-value tokens2)
           (parse-json-value tokens)
           (if erp
               (mv erp nil tokens)
             (if (not (mbt (< (len tokens2) (len tokens))))
                 (mv t nil tokens)
               ;; check for the comma (must be present if no :right-bracket) and skip it
               (if (not (consp tokens2))
                   (mv :missing-comma-and-right-bracket nil tokens2)
                 (let ((lookahead-token (first tokens2)))
                   (if (eq :right-bracket lookahead-token)
                       (parse-json-array tokens2 (cons parsed-value acc)) ;finish up
                     (if (eq :comma lookahead-token)
                         (if (not (consp (rest tokens2)))
                             (mv :missing-final-element-and-right-bracket nil tokens2)
                           (if (eq :right-bracket (second tokens2))
                               (mv :extra-comma nil tokens2)
                             (parse-json-array (rest tokens2) ;skip the comma
                                                      (cons parsed-value acc))))
                       (mv :missing-comma-in-array nil tokens2))))))))))))

 ;; Returns (mv erp parsed-value remaining-tokens)
 (defund parse-json-value (tokens)
   (declare (xargs :guard (true-listp tokens)
                   :measure (make-ord 1 (+ 1 (len tokens)) 0)))
   (if (endp tokens)
       (mv :no-tokens-for-value nil nil)
     (let ((token (first tokens)))
       (cond ((member-eq token '(:true :false :null)) (mv nil token (rest tokens)))
             ((stringp token) (mv nil token (rest tokens)))
             ((rationalp token) (mv nil token (rest tokens))) ;must be a number
             ((eq token :left-brace) (parse-json-object (rest tokens) nil))
             ((eq token :left-bracket) (parse-json-array (rest tokens) nil))
             ((member-eq token '(:right-brace :right-bracket :colon :comma))
              (mv :bad-token-for-value nil tokens))
             (t
              (mv :unknown-token-for-value nil tokens)))))))

;; TODO: Splits into many cases.
(make-flag parse-json-object)

(defthm-flag-parse-json-object
  (defthm true-list-of-mv-nth-2-of-parse-json-object
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-object tokens acc))))
    :flag parse-json-object)
  (defthm true-list-of-mv-nth-2-of-parse-json-array
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-array tokens acc))))
    :flag parse-json-array)
  (defthm true-list-of-mv-nth-2-of-parse-json-value
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-value tokens))))
    :flag parse-json-value)
  :hints (("Goal" :in-theory (enable parse-json-object
                                     parse-json-array
                                     parse-json-value)
           :expand ((parse-json-object tokens acc)
                    (parse-json-array tokens acc)))))

(defthm-flag-parse-json-object
  (defthm json-token-list-of-mv-nth-2-of-parse-json-object
    (implies (json-token-listp tokens)
             (json-token-listp (mv-nth 2 (parse-json-object tokens acc))))
    :flag parse-json-object)
  (defthm json-token-list-of-mv-nth-2-of-parse-json-array
    (implies (json-token-listp tokens)
             (json-token-listp (mv-nth 2 (parse-json-array tokens acc))))
    :flag parse-json-array)
  (defthm json-token-list-of-mv-nth-2-of-parse-json-value
    (implies (json-token-listp tokens)
             (json-token-listp (mv-nth 2 (parse-json-value tokens))))
    :flag parse-json-value)
  :hints (("Goal" :in-theory (enable parse-json-object
                                     parse-json-array
                                     parse-json-value)
           :expand ((parse-json-object tokens acc)
                    (parse-json-array tokens acc)))))

(defthm-flag-parse-json-object
  (defthm len-of-mv-nth-2-of-parse-json-object-bound
    (<= (len (mv-nth 2 (parse-json-object tokens acc)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-object)
  (defthm len-of-mv-nth-2-of-parse-json-array-bound
    (<= (len (mv-nth 2 (parse-json-array tokens acc)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-array)
  (defthm len-of-mv-nth-2-of-parse-json-value-bound
    (<= (len (mv-nth 2 (parse-json-value tokens)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-value)
  :hints (("Goal" :in-theory (enable parse-json-object
                                     parse-json-array
                                     parse-json-value)
           :expand ((parse-json-object tokens acc)
                    (parse-json-array tokens acc)))))

(defthm len-of-mv-nth-2-of-parse-json-value-bound-strong
  (implies (not (mv-nth 0 (parse-json-value tokens)))
           (< (len (mv-nth 2 (parse-json-value tokens)))
              (len tokens)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :expand ((PARSE-JSON-VALUE TOKENS)))))

(verify-guards parse-json-object)

;;;
;;; Recognizer for parsed JSON objects
;;;

(mutual-recursion
 ;; Recognize the parsed form of a JSON array
 (defund parsed-json-arrayp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (and (true-listp val)
        (= 2 (len val))
        (eq :array (car val))
        (parsed-json-valuesp (cadr val))))

 ;; Recognize a sequence of name/value pairs that appears in the parsed form of
 ;; a JSON object.
 (defund parsed-json-object-pairsp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (if (atom val)
       (null val)
     (let ((entry (first val)))
       (and (consp entry)
            (stringp (car entry))
            (parsed-json-valuep (cdr entry))
            (parsed-json-object-pairsp (rest val))))))

 ;; Recognize a parsed JSON object (in JSON parlance, and "object" is a map
 ;; from keys to values).
 (defund parsed-json-objectp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (and (true-listp val)
        (= 2 (len val))
        (eq :object (car val))
        (parsed-json-object-pairsp (cadr val))))

 ;; Recogize a true-list of parsed JSON values.
 (defund parsed-json-valuesp (vals)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count vals)) 0)))
   (if (atom vals)
       (null vals)
     (and (parsed-json-valuep (first vals))
          (parsed-json-valuesp (rest vals)))))

 ;; Recogize a parsed JSON value (in JSON parlance, a "value" can be a scalar,
 ;; an array, or an object).
 (defund parsed-json-valuep (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 1)))
   (or (member-eq val '(:true :false :null))
       (rationalp val)
       (stringp val)
       (parsed-json-arrayp val)
       (parsed-json-objectp val))))

(defthm parsed-json-object-pairsp-of-cons
  (equal (parsed-json-object-pairsp (cons pair pairs))
         (and (consp pair)
              (stringp (car pair))
              (parsed-json-valuep (cdr pair))
              (parsed-json-object-pairsp pairs)))
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp))))

(defthm parsed-json-object-pairsp-of-revappend
  (implies (and (parsed-json-object-pairsp x)
                (parsed-json-object-pairsp acc))
           (parsed-json-object-pairsp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp revappend))))

(defthm parsed-json-valuesp-of-revappend
  (implies (and (parsed-json-valuesp x)
                (parsed-json-valuesp acc))
           (parsed-json-valuesp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp revappend))))

;; Prove that we always get well-formed structures
(defthm-flag-parse-json-object
  (defthm parsed-json-objectp-of-mv-nth-1-of-parse-json-object
    (implies (and (not (mv-nth 0 (parse-json-object tokens acc)))
                  (parsed-json-object-pairsp acc)
                  (json-token-listp tokens))
             (parsed-json-objectp (mv-nth 1 (parse-json-object tokens acc))))
    :flag parse-json-object)
  (defthm parsed-json-arrayp-of-mv-nth-1-of-parse-json-array
    (implies (and (not (mv-nth 0 (parse-json-array tokens acc)))
                  (parsed-json-valuesp acc)
                  (json-token-listp tokens))
             (parsed-json-arrayp (mv-nth 1 (parse-json-array tokens acc))))
    :flag parse-json-array)
  (defthm parsed-json-valuep-of-mv-nth-1-of-parse-json-value
    (implies (and (not (mv-nth 0 (parse-json-value tokens)))
                  (json-token-listp tokens))
             (parsed-json-valuep (mv-nth 1 (parse-json-value tokens))))
    :flag parse-json-value)
  :hints (("Goal" :in-theory (e/d (parse-json-object
                                   parse-json-array
                                   parse-json-value
                                   parsed-json-valuep
                                   parsed-json-valuesp
                                   parsed-json-object-pairsp
                                   parsed-json-objectp
                                   PARSED-JSON-ARRAYP
                                   member-equal)
                                  (cdr-iff ;looped
                                   ))
           :expand ((parse-json-value tokens)
                    (parse-json-object tokens acc)
                    (parse-json-array tokens acc)))))

;;;
;;; parse-json
;;;

;; Returns (mv erp parsed-value).  where ERP is nil iff no error occured.
;; PARSED-VALUE is a parsed representation of the JSON value, using lists
;; (tagged with :array) for JSON arrays and alists (tagged with :object) for
;; JSON objects.
(defund parse-json (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (erp tokens)
    (tokenize-json-chars chars)
    (if erp
        (mv erp chars)
      (mv-let (erp parsed-value tokens)
        (parse-json-value tokens)
        (if erp
            (mv erp tokens)
          (if (consp tokens)
              (mv :extra-tokens tokens)
            (mv nil parsed-value)))))))

(defthm parsed-json-valuep-of-mv-nth-1-of-parse-json
  (implies (and (not (mv-nth 0 (parse-json chars))) ; no error
                (character-listp chars))
           (parsed-json-valuep (mv-nth 1 (parse-json chars))))
  :hints (("Goal" :in-theory (e/d (parse-json) (cdr-iff)))))
