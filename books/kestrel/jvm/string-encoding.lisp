; Encoding lists of 16-bit chars as readable strings
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "strings")
(include-book "kestrel/typed-lists-light/map-code-char" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/utilities/chars-and-codes" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

;; JLS says "The first 128 characters of the Unicode UTF-16 encoding are the ASCII characters."
(defund ascii-charp (char)
  (declare (xargs :guard (acl2::java-charp char)))
  (< char 128) ; allows the 128 chars from through 127
  )

;; upper case only
(defund hex-digit-charp (char)
  (declare (xargs :guard (acl2::java-charp char)))
  (mbe :logic
       (and (ascii-charp char) ; so we can call code-char
            (if (member (code-char char) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\A #\B #\C #\D #\E #\F)) t nil))
       :exec
       (or (and (<= 48 char) (<= char 57)) ; digit
           (and (<= 65 char) (<= char 70)) ; A - F
           )))

;; Returns (mv matches rest)
(defund split-leading-matches (char chars)
  (declare (xargs :guard (and (acl2::java-charp char)
                              (java-char-listp chars))
                  :guard-hints (("Goal" :in-theory (enable java-char-listp)))))
  (if (endp chars)
      (mv nil chars)
    (let ((first-char (first chars)))
      (if (eql first-char char)
          (mv-let (rest-matches non-matches)
              (split-leading-matches char (rest chars))
            (mv (cons first-char rest-matches)
                non-matches))
        (mv nil chars)))))

(defthm <=-of-len-of-mv-nth-1-of-split-leading-matches
  (<= (len (mv-nth 1 (split-leading-matches char chars)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable split-leading-matches))))

(defthm java-char-listp-of-mv-nth-1-of-split-leading-matches
  (implies (java-char-listp chars)
           (java-char-listp (mv-nth 1 (split-leading-matches char chars))))
  :hints (("Goal" :in-theory (enable split-leading-matches))))

;; Looks for \u...uXXXX where the number of u's is at least 1 and the XXXX are 4 hex digits.
;; todo: optimize
;; Returns (mv unicode-escape-chars-or-nil rest-chars)
(defund split-unicode-escape (chars)
  (declare (xargs :guard (java-char-listp chars)
                  :guard-hints (("Goal" :in-theory (enable java-char-listp)))))
  (if (not (and (consp chars)
                (eql #\\ (first chars))))
      (mv nil chars)
    (mv-let (us chars-after-us)
        (split-leading-matches #\u (rest chars))
      (if (and (consp us) ; at least 1 u after the backslash
               (acl2::len-at-least 4 chars-after-us)
               (hex-digit-charp (first chars-after-us))
               (hex-digit-charp (second chars-after-us))
               (hex-digit-charp (third chars-after-us))
               (hex-digit-charp (fourth chars-after-us)))
          (mv (cons #\\ (append us (take 4 chars-after-us)))
              (nthcdr 4 chars-after-us))
        (mv nil chars)))))

(defthm <=-of-len-of-mv-nth-1-of-split-unicode-escape
  (<= (len (mv-nth 1 (split-unicode-escape chars)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defthm <=-of-len-of-mv-nth-1-of-split-unicode-escape-strong
  (implies (mv-nth 0 (split-unicode-escape chars))
           (< (len (mv-nth 1 (split-unicode-escape chars)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defthm java-char-listp-of-mv-nth-1-of-split-unicode-escape
  (implies (java-char-listp chars)
           (java-char-listp (mv-nth 1 (split-unicode-escape chars))))
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defthm java-char-listp-of-mv-nth-0-of-split-unicode-escape
  (implies (java-char-listp chars)
           (java-char-listp (mv-nth 0 (split-unicode-escape chars))))
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defthm byte-listp-of-mv-nth-0-of-split-unicode-escape
  (implies (java-char-listp chars)
           (acl2::byte-listp (mv-nth 0 (split-unicode-escape chars))))
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defthm true-listp-of-mv-nth-0-of-split-unicode-escape
  (true-listp (mv-nth 0 (split-unicode-escape chars)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-unicode-escape))))

(defund hex-digit-to-char (d)
  (declare (xargs :guard (and (natp d)
                              (< d 16))))
  (mbe
   :logic (case d
            (0 #\0)
            (1 #\1)
            (2 #\2)
            (3 #\3)
            (4 #\4)
            (5 #\5)
            (6 #\6)
            (7 #\7)
            (8 #\8)
            (9 #\9)
            (10 #\A)
            (11 #\B)
            (12 #\C)
            (13 #\D)
            (14 #\E)
            (otherwise #\F))
   :exec (if (< d 10) ;digit
             (code-char (+ 48 d))
           (code-char (+ 55 d)))))

(defthm characterp-of-hex-digit-to-char
  (characterp (hex-digit-to-char d))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hex-digit-to-char))))

;; See JLS 3.3
;; Returns a list of ACL2 characters
(defund java-chars-to-characters (chars)
  (declare (xargs :guard (java-char-listp chars)
                  :measure (len chars)
                  :guard-hints (("Goal" :in-theory (enable java-char-listp)))))
  (if (endp chars)
      nil
    (mv-let (unicode-escape-chars-or-nil remaining-chars)
        (split-unicode-escape chars)
      (if unicode-escape-chars-or-nil
          (append '(#\\ #\u)
                  (acl2::map-code-char (rest unicode-escape-chars-or-nil)) ; add one u to the unicode escape
                  (java-chars-to-characters remaining-chars))
        (let ((first-char (first chars)))
          (if (ascii-charp first-char)
              (cons (code-char first-char) (java-chars-to-characters (rest chars)))
            ;; non-ascii, so put in a unicode escape:
            (list* #\\
                   #\u
                   (hex-digit-to-char (slice 15 12 first-char))
                   (hex-digit-to-char (slice 11 8 first-char))
                   (hex-digit-to-char (slice 7 4 first-char))
                   (hex-digit-to-char (slice 3 0 first-char))
                   (java-chars-to-characters (rest chars)))))))))

(defthm character-listp-of-java-chars-to-characters
  (implies (java-char-listp chars)
           (character-listp (java-chars-to-characters chars)))
  :hints (("Goal" :in-theory (enable java-chars-to-characters))))

(defund java-chars-to-string (chars)
  (declare (xargs :guard (java-char-listp chars)))
  (coerce (java-chars-to-characters chars) 'string))

;; Makes a readable string.  Uses unicode escapes for non-ASCII characters.
;; (java-chars-to-string (list 65 66)) ; todo: more tests!

;; todo: define decoding and prove inversion
