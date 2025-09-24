; A parser for XML files
;
; Copyright (C) 2014-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "xml")
(include-book "kestrel/typed-lists-light/map-code-char" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))

;An XML parser sufficient for parsing manifests and layouts of Android
;apps.

;This takes an XML file as input and generates an ACL2 book with a
;single defconst corresponding to the XML file.

;This could be of more general use, but:

;; TODO: Thread through and return errors, instead of throwing hard errors
;; TODO: Consider Unicode
;; TODO: Consider character escapes
;; TODO: Prove that the parser always returns an xml-item-listp.

;; See also books/xdoc/parse-xml.lisp (not sure how that compares to this)

(in-theory (disable mv-nth))

(local (in-theory (e/d (true-listp-when-character-listp2)
                       (character-listp
                        member-equal
                        xml-attributep
                        xml-attribute-listp ; todo
                        ))))

(local (defthm consp-when-true-listp-iff (implies (true-listp x) (iff (consp x) x))))

;; Discard leading whitespace characters from the front of CHARS
(defund skip-whitespace (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (if (whitespace-char-p (first chars))
        (skip-whitespace (rest chars))
      chars)))

(defthm len-of-skip-whitespace-linear
  (<= (len (skip-whitespace chars)) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-whitespace))))

(defthm character-listp-of-skip-whitespace
  (implies (character-listp chars)
           (character-listp (skip-whitespace chars)))
  :hints (("Goal" :in-theory (enable skip-whitespace))))

(defthm true-listp-of-skip-whitespace
  (implies (true-listp chars)
           (true-listp (skip-whitespace chars)))
  :hints (("Goal" :in-theory (enable skip-whitespace))))

(defthm true-listp-of-skip-whitespace-type
  (implies (true-listp chars)
           (true-listp (skip-whitespace chars)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable skip-whitespace))))

(defthm skip-whitespace-when-not-consp
  (implies (not (consp chars))
           (equal (skip-whitespace chars)
                  nil))
  :hints (("Goal" :in-theory (enable skip-whitespace))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun next-char-is-whitespace-p (chars)
;;   (declare (xargs :guard (and (character-listp chars)
;;                               (consp chars))))
;;   (if (endp chars)
;;       (hard-error 'next-char-is-whitespace-p "No more chars!" nil)
;;     (whitespace-char-p (first chars))))

(defund non-whitespace-char-existsp (chars)
  (declare (xargs :guard (character-listp chars)))
  (consp (skip-whitespace chars)))

;peeks ahead to the next non-whitespace char (does not change the byte stream).  If no non-whitespace char exists, this returns nil.
(defund next-non-whitespace-char (chars)
  (declare (xargs :guard (character-listp chars)))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        nil ; (hard-error 'next-non-whitespace-char "No more chars!" nil)
      (first chars))))

(defund two-non-whitespace-chars-existp (chars)
  (declare (xargs :guard (character-listp chars)))
  (consp (skip-whitespace (cdr (skip-whitespace chars)))))

;peeks ahead to the second non-whitespace char (does not change the byte stream)
(defund second-non-whitespace-char (chars)
  (declare (xargs :guard (and (character-listp chars)
                              ;(two-non-whitespace-chars-existp chars)
                              )))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        nil ; (hard-error 'second-non-whitespace-char "No more chars!" nil)
      (let* ((chars (cdr chars)) ;skip the first char
             (chars (skip-whitespace chars)))
        (if (endp chars)
            nil ; (hard-error 'second-non-whitespace-char "No more chars!" nil)
          (first chars))))))

;returns (mv char chars)
(defund parse-next-non-whitespace-char (chars)
  (declare (xargs :guard (character-listp chars)))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        (mv (hard-error 'parse-next-non-whitespace-char "No more chars!" nil)
            chars)
      (mv (first chars) (rest chars)))))

(defthm character-listp-of-mv-nth-1-of-parse-next-non-whitespace-char
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-next-non-whitespace-char chars))))
  :hints (("Goal" :in-theory (enable parse-next-non-whitespace-char))))

(defthm len-of-parse-next-non-whitespace-char-weak
  (<= (len (mv-nth 1 (parse-next-non-whitespace-char chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-next-non-whitespace-char))))

(defthm len-of-parse-next-non-whitespace-char
  (implies (consp chars)
           (< (len (mv-nth 1 (parse-next-non-whitespace-char chars))) (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-next-non-whitespace-char))))

;; Skip whitespace and then consume the next char, which mst be KNOWN-CHAR or
;; an error is thrown.
;; todo: require the skipped char to be as expected
;; todo: sometimes we shouldn't skip whitespace
(defund skip-known-char (known-char chars)
  (declare (xargs :guard (and (characterp known-char)
                              (character-listp chars))))
  (mv-let (first-char chars)
          (parse-next-non-whitespace-char chars)
          (if (eql first-char known-char)
              chars
            (hard-error 'skip-known-char "Unexpected char.  Got ~x0 but expected ~x1." (acons #\0 first-char (acons #\1 known-char nil))))))

(defthm character-listp-of-skip-known-char
  (implies (character-listp chars)
           (character-listp (skip-known-char known-char chars)))
  :hints (("Goal" :in-theory (enable skip-known-char))))

(defthm len-of-skip-known-char-weak
  (<= (len (skip-known-char known-char chars)) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-known-char))))

(defthm len-of-skip-known-char
  (implies (consp chars)
           (< (len (skip-known-char known-char chars)) (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-known-char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
(defund skip-char (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (first-char chars)
          (parse-next-non-whitespace-char chars)
          (declare (ignore first-char))
    chars))

(defthm character-listp-of-skip-char
  (implies (character-listp chars)
           (character-listp (skip-char chars)))
  :hints (("Goal" :in-theory (enable skip-char))))

(defthm <-of-len-of-skip-chars
  (implies (consp chars)
           (< (len (skip-char chars))
              (len chars)))
  :hints (("Goal" :in-theory (enable skip-char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund skip-two-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (first-char chars)
          (parse-next-non-whitespace-char chars)
          (declare (ignore first-char))
          (mv-let (second-non-whitespace-char chars)
                  (parse-next-non-whitespace-char chars)
                  (declare (ignore second-non-whitespace-char))
            chars)))

(defthm character-listp-of-skip-two-chars
  (implies (character-listp chars)
           (character-listp (skip-two-chars chars)))
  :hints (("Goal" :in-theory (enable skip-two-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund skip-through-two-chars (first-non-whitespace-char second-non-whitespace-char chars)
  (declare (xargs :guard (and (characterp first-non-whitespace-char)
                              (characterp second-non-whitespace-char)
                              (character-listp chars))
                  :measure (len chars)
                  ;; :guard-hints (("Goal" :in-theory (enable two-non-whitespace-chars-existp skip-whitespace)))
                  ))
  (if (or (endp chars) (endp (rest chars))) ;for termination (think about this)
      (er hard? 'skip-through-two-chars "Not enough chars" nil)
    (if (and (eql first-non-whitespace-char (next-non-whitespace-char chars))
             (eql second-non-whitespace-char (second-non-whitespace-char chars)))
        (skip-two-chars chars)
      (skip-through-two-chars first-non-whitespace-char second-non-whitespace-char (skip-char chars)))))

(defthm character-listp-of-skip-through-two-chars
  (implies (character-listp chars)
           (character-listp (skip-through-two-chars first-non-whitespace-char second-non-whitespace-char chars)))
  :hints (("Goal" :in-theory (enable skip-through-two-chars))))

(defund skip-xml-prolog (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (and (eql #\< (next-non-whitespace-char chars))
           (eql #\? (second-non-whitespace-char chars)))
      (let* ((chars (skip-two-chars chars))
             (chars (skip-through-two-chars #\? #\> chars)))
        chars)
    chars))

(defthm character-listp-of-skip-xml-prolog
  (implies (character-listp chars)
           (character-listp (skip-xml-prolog chars)))
  :hints (("Goal" :in-theory (enable skip-xml-prolog))))

;; Returns (mv erp some-chars chars).  Throws an error if the delimiter is not found.
;; Does not consume the delimiter.
;does not skip whitespace??
(defund parse-until-delim (delim chars)
  (declare (xargs :guard (and (characterp delim)
                              (character-listp chars))
                  :measure (len chars)))
  (if (not (consp chars))
      (mv `(:missing-delimiter ,delim) nil nil)
    (let ((first (first chars))) ;next-non-whitespace-char
      (if (eql delim first)
          (mv nil nil chars)
        (b* (((mv erp rest chars)
              (parse-until-delim delim (rest chars)))
             ((when erp) (mv erp nil nil)))
          (mv nil (cons first rest) chars))))))

(defthm character-listp-of-mv-nth-1-of-parse-until-delim
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-until-delim delim chars))))
  :hints (("Goal" :in-theory (enable parse-until-delim))))

(defthm character-listp-of-mv-nth-2-of-parse-until-delim
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-until-delim delim chars))))
  :hints (("Goal" :in-theory (enable parse-until-delim))))

(defthm <=-of-len-of-mv-nth-2-of-parse-until-delim
  (<= (len (mv-nth 2 (parse-until-delim delim chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-until-delim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;does not skip whitespace
;returns (mv some-chars chars)
(defund parse-until-any-delim (delims chars)
  (declare (xargs :guard (and (character-listp delims)
                              (character-listp chars))))
  (if (endp chars)
      (mv (hard-error 'parse-until-any-delim "Ran out of chars." nil)
          chars)
    (let ((first-char (first chars)))
      (if (member first-char delims)
          (mv nil chars)
        (mv-let (rest chars)
                (parse-until-any-delim delims (rest chars))
                (mv (cons first-char rest)
                    chars))))))

(defthm character-listp-of-mv-nth-0-of-parse-until-any-delim
  (implies (character-listp chars)
           (character-listp (mv-nth 0 (parse-until-any-delim delims chars))))
  :hints (("Goal" :in-theory (enable parse-until-any-delim))))

(defthm character-listp-of-mv-nth-1-of-parse-until-any-delim
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-until-any-delim delims chars))))
  :hints (("Goal" :in-theory (enable parse-until-any-delim))))

(defthm len-of-parse-until-any-delim
  (<= (len (mv-nth 1 (parse-until-any-delim delims chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-until-any-delim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;  Defining this separately so we can disable it
(defund parse-element-name-chars ()
  (declare (xargs :guard t))
   (append *whitespace-chars* '(#\> #\/ #\<)))
(in-theory (disable (:e parse-element-name-chars))) ;TODO: Without this, some goals printed below are quite weird

(defthm character-listp-of-parse-element-name-chars
  (character-listp (parse-element-name-chars))
  :hints (("Goal" :in-theory (enable parse-element-name-chars))))

;fixme think about what chars are legal here
;returns (mv element-name element-name-chars chars)
(defund parse-element-name (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (name-chars chars)
          (parse-until-any-delim (parse-element-name-chars) chars)
          (mv (coerce name-chars 'string) name-chars chars)))

(defthm stringp-of-mv-nth-0-of-parse-element-name
  (implies (character-listp chars)
           (stringp (mv-nth 0 (parse-element-name chars))))
  :hints (("Goal" :in-theory (enable parse-element-name))))

(defthm character-listp-of-mv-nth-1-of-parse-element-name
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-element-name chars))))
  :hints (("Goal" :in-theory (enable parse-element-name))))

(defthm character-listp-of-mv-nth-2-of-parse-element-name
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-element-name chars))))
  :hints (("Goal" :in-theory (enable parse-element-name))))

(defthm len-of-parse-element-name
  (<= (len (mv-nth 2 (parse-element-name chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (parse-element-name) (BINARY-APPEND)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp string chars).
(defund parse-attribute-name (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv erp name-chars chars)
        (parse-until-delim #\= chars))
       ((when erp) (mv erp "" nil)))
    (mv nil (coerce name-chars 'string) chars)))

(defthm character-listp-of-mv-nth-2-of-parse-attribute-name
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-attribute-name chars))))
  :hints (("Goal" :in-theory (enable parse-attribute-name))))

(defthm stringp-of-mv-nth-1-of-parse-attribute-name
  (implies t ;(character-listp chars)
           (stringp (mv-nth 1 (parse-attribute-name chars))))
  :hints (("Goal" :in-theory (enable parse-attribute-name))))

(defthm <=-of-len-of-mv-nth-2-of-parse-attribute-name
  (<= (len (mv-nth 2 (parse-attribute-name chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-attribute-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp string chars).
(defund parse-quoted-string (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* ((chars (skip-known-char #\" chars))
       ((mv erp string-chars chars)
        (parse-until-delim #\" chars))
       ((when erp) (mv erp "" nil))
       (chars (skip-known-char #\" chars)))
    (mv nil (coerce string-chars 'string) chars)))

(defthm character-listp-of-mv-nth-2-of-parse-quoted-string
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-quoted-string chars))))
  :hints (("Goal" :in-theory (enable parse-quoted-string))))

(defthm stringp-of-mv-nth-1-of-parse-quoted-string
  (implies (character-listp chars)
           (stringp (mv-nth 1 (parse-quoted-string chars))))
  :hints (("Goal" :in-theory (enable parse-quoted-string))))

(defthm <=-of-len-of-mv-nth-2-of-parse-quoted-string
  (<= (len (mv-nth 2 (parse-quoted-string chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-quoted-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv erp attrib chars)
; Parse an attribute like foo="bar"
(defund parse-xml-attrib (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* ((chars (skip-whitespace chars))
       ((mv erp name chars)
        (parse-attribute-name chars))
       ((when erp) (mv erp '(= "" "") nil))
       (chars (skip-known-char #\= chars)) ; can there be whitespace here?
       ((mv erp val chars) (parse-quoted-string chars))
       ((when erp) (mv erp '(= "" "") nil)))
    (mv nil `(= ,name ,val) chars)))

(defthm <-of-len-of-mv-nth-2-of-parse-xml-attrib
  (implies (consp chars)
           (< (len (mv-nth 2 (parse-xml-attrib chars)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-xml-attrib
                                     skip-known-char ;todo
                                     parse-next-non-whitespace-char
                                     ))))

(defthm character-listp-of-mv-nth-2-of-parse-xml-attrib
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-xml-attrib chars))))
  :hints (("Goal" :in-theory (enable parse-xml-attrib))))

(defthm xml-attributep-of-mv-nth-1-of-parse-xml-attrib
  (implies (character-listp chars)
           (xml-attributep (mv-nth 1 (parse-xml-attrib chars))))
  :hints (("Goal" :in-theory (enable parse-xml-attrib xml-attributep))))

(defthm <=-of-len-of-parse-xml-attrib
  (<= (len (mv-nth 2 (parse-xml-attrib chars)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-xml-attrib))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp attribs chars).
;; Parse attributes of the form foo="bar" until > or /> is seen
(defund parse-xml-attribs (chars)
  (declare (xargs :guard (character-listp chars)
                  :guard-debug t
                  :measure (len chars)))
  (if (endp chars) ;for termination (think about this)
      (mv nil nil chars)
    (if (not (member (next-non-whitespace-char chars) '(#\> #\/)))
        (b* (((mv erp attrib chars)
              (parse-xml-attrib chars))
             ((when erp) (mv erp nil nil))
             ((mv erp attribs chars)
              (parse-xml-attribs chars))
             ((when erp) (mv erp nil nil)))
          (mv nil (cons attrib attribs) chars))
      (mv nil nil chars))))

(defthm xml-attribute-listp-of-mv-nth-1-of-parse-xml-attribs
  (implies (character-listp chars)
           (xml-attribute-listp (mv-nth 1 (parse-xml-attribs chars))))
  :hints (("Goal" :in-theory (enable parse-xml-attribs
                                     xml-attribute-listp))))

(defthm character-listp-of-mv-nth-2-of-parse-xml-attribs
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (parse-xml-attribs chars))))
  :hints (("Goal" :in-theory (enable parse-xml-attribs))))

(defthm <=-of-len-of-mv-nth-2-of-parse-xml-attribs
  (<= (len (mv-nth 2 (parse-xml-attribs chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-xml-attribs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;does not allow whitespace to intervene
(defund skip-known-chars (target-chars chars)
  (declare (xargs :guard (and (character-listp target-chars)
                              (character-listp chars))))
  (if (endp target-chars)
      chars
    (if (endp chars)
        (hard-error 'skip-known-chars "Ran out of chars!" nil)
      (if (not (eql (first chars) (first target-chars)))
          (hard-error 'skip-known-chars "Known char mismatch! Expected ~x0 but got ~x1" (acons #\0 (first target-chars) (acons #\1 (first chars) nil)))
        (skip-known-chars (rest target-chars) (rest chars))))))

(defthm character-listp-of-skip-known-chars
  (implies (character-listp chars)
           (character-listp (skip-known-chars target-chars chars)))
  :hints (("Goal" :in-theory (enable skip-known-chars))))

(defthm <=-of-len-of-skip-known-chars
  (<= (len (skip-known-chars target-chars chars)) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-known-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;TODO:  We may know that there is no whitespace before the < ?
(defund skip-matching-tag (element-name-chars chars)
  (declare (xargs :guard (and (character-listp element-name-chars)
                              (character-listp chars))))
  (let* ((chars (skip-known-char #\< chars))
         (chars (skip-known-char #\/ chars))
         (chars (skip-known-chars element-name-chars chars))
         (chars (skip-known-char #\> chars)))
    chars))

(defthm character-listp-of-skip-matching-tag
  (implies (character-listp chars)
           (character-listp (skip-matching-tag target-chars chars)))
  :hints (("Goal" :in-theory (enable skip-matching-tag))))

(defthm <=-of-len-of-skip-matching-tag
  (<= (len (skip-matching-tag target-chars chars)) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-matching-tag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm second-non-whitespace-char-when-not-consp-of-cdr
  (implies (not (consp (cdr chars)))
           (equal (second-non-whitespace-char chars)
                  nil))
  :hints (("Goal" :in-theory (enable second-non-whitespace-char skip-whitespace))))

;; (defthm skip-known-char-when-not-consp-of-cdr
;;   (implies (and (not (consp (cdr chars)))
;;                 (characterp char)
;;                 (equal char (NEXT-NON-WHITESPACE-CHAR CHARS)))
;;            (equal (skip-known-char char chars)
;;                   (final-cdr chars)))
;;   :hints (("Goal" :in-theory (enable skip-known-char parse-next-non-whitespace-char skip-whitespace))))

(defund read-to-end-of-xml-comment (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (< (len chars) 3)
      (er hard? 'read-to-end-of-xml-comment "Ran out of chars when parsing comment.")
    (if (and (eql #\- (first chars))
             (eql #\- (second chars))
             (eql #\> (third chars)))
        ;; Found the end of the comment, so skip past it and we're done:
        (rest (rest (rest chars)))
      (read-to-end-of-xml-comment (rest chars)))))

(local
  (defthm len-of-read-to-end-of-xml-comment-linear
    (<= (len (read-to-end-of-xml-comment chars))
        (len chars))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable read-to-end-of-xml-comment)))))

(defthm character-listp-of-read-to-end-of-xml-comment
  (implies (character-listp chars)
           (character-listp (read-to-end-of-xml-comment chars)))
  :hints (("Goal" :in-theory (enable read-to-end-of-xml-comment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; chars should begin with <!--
(defund skip-xml-comment (chars)
  (declare (xargs :guard (character-listp chars)))
  (let* ((chars (skip-known-char #\< chars))
         (chars (skip-known-char #\! chars))
         (chars (skip-known-char #\- chars))
         (chars (skip-known-char #\- chars)))
    (read-to-end-of-xml-comment chars)))

(defthm character-listp-of-skip-xml-comment
  (implies (character-listp chars)
           (character-listp (skip-xml-comment chars)))
  :hints (("Goal" :in-theory (enable skip-xml-comment))))

(local
  (defthm <=-of-len-of-skip-xml-comment
    (implies (equal #\< (car chars))
             (<= (len (skip-xml-comment chars))
                 (len chars)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable skip-xml-comment)))))

;; Initially, this called (len chars), which was slow
(defund maybe-skip-xml-comment (chars)
  (declare (xargs :guard (character-listp chars)
                  :guard-hints (("Goal" :in-theory (enable skip-xml-comment)))))
  ;; a comment starts with <!--
  (if (and (consp chars)
           (eql #\< (car chars))
           (consp (cdr chars))
           (eql #\! (cadr chars))
           (consp (cddr chars))
           (eql #\- (caddr chars))
           (consp (cdddr chars))
           (eql #\- (cadddr chars)))
      (read-to-end-of-xml-comment (rest (rest (rest (rest chars)))))
    chars))

(defthm character-listp-of-maybe-skip-xml-comment
  (implies (character-listp chars)
           (character-listp (maybe-skip-xml-comment chars)))
  :hints (("Goal" :in-theory (enable maybe-skip-xml-comment))))

(local
  (defthm <=-of-len-of-maybe-skip-xml-comment
    (<= (len (maybe-skip-xml-comment chars))
        (len chars))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable maybe-skip-xml-comment)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv string-chars remaining-chars).
(defund xml-string-chars (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))
                  :measure (len chars)))
  (let ((chars (maybe-skip-xml-comment chars))) ; todo: do this more, elsewhere?
    (if (endp chars)
        (mv (reverse acc) nil)
      (let* ((char (first chars)))
        (if (eql #\< char) ;end of the string
            (mv (reverse acc) chars)
          (xml-string-chars (rest chars) (cons char acc)))))))

(defthm character-listp-of-mv-nth-0-of-xml-string-chars
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (mv-nth 0 (xml-string-chars chars acc))))
  :hints (("Goal" :in-theory (enable xml-string-chars))))

(defthm character-listp-of-mv-nth-1-of-xml-string-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (xml-string-chars chars acc))))
  :hints (("Goal" :in-theory (enable xml-string-chars))))

(defthm <=-of-len-of-mv-nth-1-of-xml-string-chars-linear
  (<= (len (mv-nth 1 (xml-string-chars chars acc)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable xml-string-chars maybe-skip-xml-comment))))

(defthm <-of-len-of-mv-nth-1-of-xml-string-chars
  (implies (and (consp chars)
                (not (equal  #\< (first chars))))
           (< (len (mv-nth 1 (xml-string-chars chars acc)))
              (len chars)))
  :hints (("Goal" :in-theory (enable xml-string-chars maybe-skip-xml-comment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse an XML string up to an occurrence of '<' indicating the next element.
;; Returns (mv string chars).
(defund parse-xml-string (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (string-chars remaining-chars)
    (xml-string-chars chars nil)
    (mv (coerce string-chars 'string)
        remaining-chars)))

(defthm character-listp-of-mv-nth-1-of-parse-xml-string
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-xml-string chars))))
  :hints (("Goal" :in-theory (enable parse-xml-string))))

(defthm stringp-of-mv-nth-0-of-parse-xml-string
  (implies (character-listp chars)
           (stringp (mv-nth 0 (parse-xml-string chars))))
  :hints (("Goal" :in-theory (enable parse-xml-string))))

(defthm <-of-len-of-mv-nth-1-of-parse-xml-string-linear
  (implies (and (consp chars)
                (not (equal  #\< (first chars))))
           (< (len (mv-nth 1 (parse-xml-string chars)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-xml-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
  ;; Parse an XML element, which should be either an empty element of the form
  ;; <elementname attrib1="val" attrib2="val2" ... /> (note the trailing slash)
  ;; or an element with subelements, of the form <elementname attrib1="val"
  ;; attrib2="val2" ... > ... characters and sub elements ... </elementname>.
  ;; Returns (mv erp elem chars).  The first character of CHARS should be <.
  ;; Whitespace within the tag itself is not significant (todo: clarify), but
  ;; whitespace between tags is.
  (defund parse-xml-element (chars)
    (declare (xargs :guard (character-listp chars)
                    :verify-guards nil ; done below
                    :measure (make-ord 1 (+ 1 (len chars)) 0)
                    :hints (("Goal" ; :induct t
                             :in-theory (enable maybe-skip-xml-comment skip-xml-comment)
                             ;; :expand (PARSE-XML-ELEMENT CHARS) ;todo: illegal hint!
                             ))))
    (if (endp chars)
        (prog2$ (cw "ERROR: Not enough chars!")
                (mv :not-enough-chars nil nil))
      (let ((first-char (first chars)))
        (if (not (eql #\< first-char))
            (prog2$ (cw  "ERROR: Element must start with a <, but we got ~x0." first-char)
                    (mv :missing-< nil nil))
          (b* ((chars (rest chars))
               ((mv element-name element-name-chars chars)
                (parse-element-name chars))
               ((mv erp attribs chars)
                (parse-xml-attribs chars))
               ((when erp) (mv erp nil nil)))
            (if (eql #\/ (next-non-whitespace-char chars))
                ;;an empty element like <name .../> (i.e., no nested elements)
                (let* ((chars (skip-known-char #\/ chars))
                       (chars (skip-known-char #\> chars)))
                  (mv nil
                      (make-xml-element element-name attribs nil) ;no sub-elements
                      chars))
              (if (eql #\> (next-non-whitespace-char chars))
                  ;; not an empty element, so parse any nested strings/elements:
                  (b* ((chars (skip-known-char #\> chars))
                       ((mv erp items chars)
                        (parse-xml-elements-and-strings chars))
                       ((when erp) (mv erp nil nil))
                       (chars (skip-matching-tag element-name-chars chars)))
                    (mv nil
                        (make-xml-element element-name attribs items)
                        chars))
                (mv :unexpected-char
                    (hard-error 'parse-xml-element "Unexpected char in XML element opening tag." nil)
                    chars))))))))

  ;; Parse the contents of an XML element, which may be strings and
  ;; child elements, up to a closing tag.
  ;; Returns (mv erp elems chars).
  (defund parse-xml-elements-and-strings (chars)
    (declare (xargs :guard (character-listp chars)
                    :measure (make-ord 1 (+ 1 (len chars)) 1)))
    (if (not (consp chars))
        (mv nil nil nil)
      (let ((first-char (first chars))
            (orig-chars chars))
        (if (not (eql #\< first-char))
            ;; Anything other than < gets parsed as a string:
            (mv-let (item chars)
              (parse-xml-string chars)
              (b* (((mv erp items chars)
                    (parse-xml-elements-and-strings chars))
                   ((when erp) (mv erp nil nil)))
                (mv nil (cons item items) chars)))
          ;; the first-char is < :
          (if (eql #\/ (next-non-whitespace-char (rest chars)))
              ;; It's a closing tag, </...>, so stop
              (mv nil nil chars)
            (if (and (>= (len chars) 4) ;; a comment starts with <!-- ;TODO: slow?
                     (eql #\! (cadr chars))
                     (eql #\- (caddr chars))
                     (eql #\- (cadddr chars)))
                ;; It's a comment, so skip it:
                (let ((chars (skip-xml-comment chars)))
                  (parse-xml-elements-and-strings chars))
              ;; It's a tag but not a comment or a closing tag, so parse an element:
              (b* (((mv erp item chars)
                    (parse-xml-element chars))
                   ((when erp) (mv erp nil nil)))
                (if (not (mbt (< (len chars) (len orig-chars))))
                    (prog2$ (er hard 'parse-xml-elements-and-strings "This should never happen.")
                            (mv :error nil nil))
                  (b* (((mv erp items chars)
                        (parse-xml-elements-and-strings chars))
                       ((when erp) (mv erp nil nil)))
                    (mv nil (cons item items) chars)))))))))))

(include-book "tools/flag" :dir :system)
(make-flag parse-xml-element
           :hints (("Goal" ; :induct t
                    :in-theory (enable maybe-skip-xml-comment skip-xml-comment)
                    ;; :expand (PARSE-XML-ELEMENT CHARS) ;todo: illegal hint!
                    )))

(in-theory (disable xml-elementp-rewrite)) ; todo

(defthm-flag-parse-xml-element
  (defthm theorem-for-parse-xml-element
    (implies (and (not (mv-nth 0 (parse-xml-element chars))) ; no error
                  (character-listp chars))
             (and (xml-elementp (mv-nth 1 (parse-xml-element chars)))
                  (character-listp (mv-nth 2 (parse-xml-element chars)))
                  (<= (len (mv-nth 2 (parse-xml-element chars)))
                      (len chars))))
    :flag parse-xml-element)
  (defthm theorem-for-parse-xml-elements-and-strings
    (implies (and (not (mv-nth 0 (parse-xml-elements-and-strings chars))) ; no error
                  (character-listp chars))
             (and (xml-item-listp (mv-nth 1 (parse-xml-elements-and-strings chars)))
                  (character-listp (mv-nth 2 (parse-xml-elements-and-strings chars)))
                  (<= (len (mv-nth 2 (parse-xml-elements-and-strings chars)))
                      (len chars))))
    :flag parse-xml-elements-and-strings)
  :hints (("Goal" :in-theory (enable parse-xml-elements-and-strings
                                     parse-xml-element))))

(defthm <=-of-len-of-mv-nth-2-of-parse-xml-elements-and-strings-linear
  (implies (and (not (mv-nth 0 (parse-xml-elements-and-strings chars))) ; no error
                (character-listp chars))
           (<= (len (mv-nth 2 (parse-xml-elements-and-strings chars)))
               (len chars)))
  :rule-classes :linear)

(defthm <-of-len-of-mv-nth-2-of-parse-xml-element
  (implies (and (equal #\< (car chars))
                (character-listp chars))
           (< (len (mv-nth 2 (parse-xml-element chars)))
              (len chars)))
  :hints (("Goal" :expand (parse-xml-element chars) :in-theory (enable parse-xml-element))))

(verify-guards parse-xml-element :otf-flg t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Returns (mv erp result) where result is a list of XML elements and strings.
;; TODO: Return the prolog
;; TODO: Allow an epilog
(defund parse-xml-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* ((chars (skip-xml-prolog chars))
       ((mv erp items chars)
        (parse-xml-elements-and-strings chars))
       ((when erp) (mv erp nil))
       (chars (skip-whitespace chars))) ;skip any trailing whitespace (can this happen?)
    (if (endp chars)
        (mv nil items)
      (progn$ (cw "Chars left: ~x0" chars)
              (hard-error 'parse-xml-chars "Unexpected chars found." nil) ; todo: should this really be an error?  can this even happen?
              (mv :unexpected-chars items)))))

(defthm xml-item-listp-of-mv-nth-1-of-parse-xml-chars
  (implies (character-listp chars)
           (xml-item-listp (mv-nth 1 (parse-xml-chars chars))))
  :hints (("Goal" :in-theory (enable parse-xml-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;TODO: Must there be a single top-level element?  This is more general
;;Returns (mv erp elements-and-strings state)
(defund parse-xml-file (input-xml-file drop-whitespace-stringsp state)
  (declare (xargs :guard (and (stringp input-xml-file)
                              (booleanp drop-whitespace-stringsp))
                  :stobjs state))
  (mv-let (erp bytes state) ; todo: read directly into a character list?
    (read-file-into-byte-list input-xml-file state)
    (if erp
        (prog2$ (cw "Error reading from ~x0." input-xml-file)
                (mv erp nil state))
      (b* ((chars (map-code-char bytes))
           ((mv erp parsed-items) (parse-xml-chars chars))
           ((when erp) (mv erp nil state))
           (parsed-items (if drop-whitespace-stringsp
                             (drop-whitespace-strings-from-parsed-xml-items parsed-items)
                           parsed-items)))
        (mv nil parsed-items state)))))
