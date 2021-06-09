; A simple JSON parser
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also parse-json-file.lisp, for a wrapper of this tool that reads the
;; JSON from a file.

;; Written from http://www.ecma-international.org/publications/files/ECMA-ST/ECMA-404.pdf.

;; TODO: Add more complete support for Unicode.  Currently, this uses ACL2 characters, of
;; which there are only 256.  ACL2 characters are used as UTF-8 bytes in JSON strings.

(include-book "unicode/utf8-encode" :dir :system) ; for uchar=>utf8
(include-book "kestrel/bv-lists/string-to-bits" :dir :system)
(include-book "std/basic/defs" :dir :system) ; for (impossible)

;; TODO: If whitespace is optional, what if it occurs between digits?

;; TODO: Define predicates for tokens and lists of tokens.

;; TODO: Handle commas in lists and objects more elegantly.

;; TODO: Return more helpful information in the case of errors.

(include-book "tools/flag" :dir :system)
(local (local (include-book "kestrel/typed-lists-light/character-listp" :dir :system)))

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

(local
 (defthm len-of-cdr
   (implies (consp x)
            (equal (len (cdr x))
                   (+ -1 (len x))))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :in-theory (enable len)))))

(local
 (defthm true-listp-of-cdr
   (implies (true-listp x)
            (true-listp (cdr x)))))

(local
 (defthm len-of-cdr-linear
   (<= (len (cdr x))
       (len x))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :in-theory (enable len)))))

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

;todo: use more
(defconst *digit-chars*
  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

(defconst *hex-digit-chars*
  (append *digit-chars*
          '(#\A #\a
            #\B #\b
            #\C #\c
            #\D #\d
            #\E #\e
            #\F #\f)))

(defund hex-digitp (char)
  (declare (xargs :guard (characterp char)))
  (member char *hex-digit-chars*))

(defund hex-digit-to-nat (d)
  (declare (xargs :guard (and (characterp d) (hex-digitp d))
                  :guard-hints (("Goal" :in-theory (enable hex-digitp)))))
  (let ((code (char-code d)))
    (cond ((and (<= 48 code) (<= code 57))
           (- code 48))
          ((and (<= 65 code) (<= code 70))
           (- code 55))
          ((and (<= 97 code) (<= code 102))
           (- code 87))
          (t (prog2$ (impossible) 0))))) ; should never happen

(defund encode-unicode-bmp (digit1 digit2 digit3 digit4)
  (declare (xargs :guard (and (characterp digit1)
                              (characterp digit2)
                              (characterp digit3)
                              (characterp digit4)
                              (hex-digitp digit1)
                              (hex-digitp digit2)
                              (hex-digitp digit3)
                              (hex-digitp digit4))))
  (let ((unicode-scalar-value
         (+ (* (hex-digit-to-nat digit1) (expt 16 3))
            (* (hex-digit-to-nat digit2) (expt 16 2))
            (* (hex-digit-to-nat digit3) 16)
            (hex-digit-to-nat digit4))))
      (if (uchar? unicode-scalar-value)
          (uchar=>utf8 unicode-scalar-value)
        ;; uchar? will be false for code points
        ;; that are not unicode scalar values,
        ;; such as U+D800 through U+DFFF inclusive.
        ;; Return this error flag for those.
        (list #xC0))))

(defthm unsigned-byte-list-of-encode-unicode-bmp
  (implies (and (hex-digitp digit1)
                (hex-digitp digit2)
                (hex-digitp digit3)
                (hex-digitp digit4))
           (unsigned-byte-listp 8 (encode-unicode-bmp digit1 digit2 digit3 digit4)))
  :hints (("Goal" :in-theory (enable encode-unicode-bmp))))

(defund code-to-char-list (utf-8-byte-list)
  (declare (xargs :guard (and (true-listp utf-8-byte-list)
                              (unsigned-byte-listp 8 utf-8-byte-list))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-listp unsigned-byte-p)))))
  (if (endp utf-8-byte-list)
      nil
    (cons (code-char (car utf-8-byte-list))
          (code-to-char-list (cdr utf-8-byte-list)))))

(defthm character-listp-of-code-to-char-list
  (implies (unsigned-byte-listp 8 x)
           (character-listp (code-to-char-list x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp code-to-char-list))))

;; Returns (mv erp result remaining-chars) where RESULT is a list of
;; characters.
;;   WARNING: this does not handle escapes for characters that are not in the BMP.
;;   RFC 8259 states:
;;     .. for example, a string containing only the G clef character (U+1D11E)
;;     may be represented as "\uD834\uDD1E".
;;   Usually, JSON writers will write those out in UTF-8, which is fine.
;;   But a more complete JSON parser should handle these escapes.
(defund parse-unicode-digits (chars)
  (declare (xargs :guard (and (character-listp chars))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-listp)))))
  (if (not (consp (rest (rest (rest chars)))))
      (mv :too-few-unicode-digits nil chars)
    (let ((digit1 (first chars))
          (digit2 (second chars))
          (digit3 (third chars))
          (digit4 (fourth chars)))
      (if (not (and (hex-digitp digit1)
                    (hex-digitp digit2)
                    (hex-digitp digit3)
                    (hex-digitp digit4)))
          (mv :bad-unicode-digits nil chars)
        (let ((encoded (encode-unicode-bmp digit1 digit2 digit3 digit4)))
          (if (equal encoded (list #xC0)) ; error flag
              (mv :bad-unicode-digits nil chars)
            (mv nil
                ;; Convert the bytes back to common lisp characters
                ;; since that is what the caller expects.
                (code-to-char-list encoded)
                (rest (rest (rest (rest chars)))))))))))

(defthm len-of-mv-nth-2-of-parse-unicode-digits-bound
  (implies (not (mv-nth 0 (parse-unicode-digits chars)))
           (< (len (mv-nth 2 (parse-unicode-digits chars)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-unicode-digits))))

(defthm character-listp-of-mv-nth-2-of-parse-unicode-digits
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-unicode-digits chars))))
  :hints (("Goal" :in-theory (enable parse-unicode-digits))))

(defthm character-listp-of-mv-nth-1-of-parse-unicode-digits
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-unicode-digits chars))))
  :hints (("Goal" :in-theory (enable parse-unicode-digits))))

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

;; Returns (mv erp result remaining-chars) where RESULT is a list of characters.
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
                   (parse-unicode-digits (rest rest-chars)))
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

(defund tokenize-json-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (tokenize-json-chars-aux chars nil))

(defthm true-listp-of-mv-nth-1-of-tokenize-json-chars
  (true-listp (mv-nth 1 (tokenize-json-chars chars)))
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

 ;; Parse the pairs in the object and the closing curly brace.  Returns (mv erp
 ;; parsed-object-pairs remaining-tokens).
 (defund parse-json-object-pairs (tokens acc)
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
                           (parse-json-object-pairs tokens2 (cons (cons first-token parsed-value) acc)) ;finish up
                         (if (eq :comma lookahead-token)
                             (if (not (consp (rest tokens2)))
                                 (mv :missing-final-element-and-right-brace nil tokens2)
                               (if (eq :right-brace (second tokens2))
                                   (mv :extra-comma nil tokens2)
                                 (parse-json-object-pairs (rest tokens2) ;skip the comma
                                                          (cons (cons first-token parsed-value) acc))))
                           (mv :missing-comma-in-object nil tokens2))))))))))))))

 ;; Parse the comma-separated values in the array and the closing bracket.
 ;; Returns (mv erp parsed-array-values remaining-tokens).
 (defund parse-json-array-values (tokens acc)
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
                       (parse-json-array-values tokens2 (cons parsed-value acc)) ;finish up
                     (if (eq :comma lookahead-token)
                         (if (not (consp (rest tokens2)))
                             (mv :missing-final-element-and-right-bracket nil tokens2)
                           (if (eq :right-bracket (second tokens2))
                               (mv :extra-comma nil tokens2)
                             (parse-json-array-values (rest tokens2) ;skip the comma
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
             ((eq token :left-brace) (parse-json-object-pairs (rest tokens) nil))
             ((eq token :left-bracket) (parse-json-array-values (rest tokens) nil))
             ((member-eq token '(:right-brace :right-bracket :colon :comma))
              (mv :bad-token-for-value nil tokens))
             (t
              (mv :unknown-token-for-value nil tokens)))))))

;; TODO: Splits into many cases.
(make-flag parse-json-object-pairs)

(defthm-flag-parse-json-object-pairs
  (defthm true-list-of-mv-nth-2-parse-json-object-pairs
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-object-pairs tokens acc))))
    :flag parse-json-object-pairs)
  (defthm true-list-of-mv-nth-2-parse-json-array-values
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-array-values tokens acc))))
    :flag parse-json-array-values)
  (defthm true-list-of-mv-nth-2-parse-json-value
    (implies (true-listp tokens)
             (true-listp (mv-nth 2 (parse-json-value tokens))))
    :flag parse-json-value)
  :hints (("Goal" :in-theory (enable parse-json-object-pairs
                                     parse-json-array-values
                                     parse-json-value)
           :expand ((parse-json-object-pairs tokens acc)
                    (parse-json-array-values tokens acc)))))

(defthm-flag-parse-json-object-pairs
  (defthm len-of-mv-nth-2-parse-json-object-pairs-bound
    (<= (len (mv-nth 2 (parse-json-object-pairs tokens acc)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-object-pairs)
  (defthm len-of-mv-nth-2-parse-json-array-values-bound
    (<= (len (mv-nth 2 (parse-json-array-values tokens acc)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-array-values)
  (defthm len-of-mv-nth-2-parse-json-value-bound
    (<= (len (mv-nth 2 (parse-json-value tokens)))
        (len tokens))
    :rule-classes (:rewrite :linear)
    :flag parse-json-value)
  :hints (("Goal" :in-theory (enable parse-json-object-pairs
                                     parse-json-array-values
                                     parse-json-value)
           :expand ((parse-json-object-pairs tokens acc)
                    (parse-json-array-values tokens acc)))))

(defthm len-of-mv-nth-2-parse-json-value-bound-strong
  (implies (not (mv-nth 0 (parse-json-value tokens)))
           (< (len (mv-nth 2 (parse-json-value tokens)))
              (len tokens)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :expand ((PARSE-JSON-VALUE TOKENS)))))

(verify-guards parse-json-object-pairs)

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
