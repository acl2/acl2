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
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

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

(defconst *whitespace-chars*
  '(#\Space #\Tab #\Newline #\))

(defund whitespace-char-p (char)
  (declare (xargs :guard t))
  (member char *whitespace-chars*))

(defun all-whitespace-char-p (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      t
    (and (whitespace-char-p (first chars))
         (all-whitespace-char-p (rest chars)))))

(defun whitespace-string-p (str)
  (declare (xargs :guard (stringp str)))
  (all-whitespace-char-p (coerce str 'list)))

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
  (implies (and (not (consp chars))
                ;(true-listp chars)
                )
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

(defun non-whitespace-char-existsp (chars)
  (declare (xargs :guard (character-listp chars)))
  (consp (skip-whitespace chars)))

;peeks ahead to the next non-whitespace char (does not change the byte stream)
(defun next-non-whitespace-char (chars)
  (declare (xargs :guard (and (character-listp chars)
                              (non-whitespace-char-existsp chars))))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        (hard-error 'next-non-whitespace-char "No more chars!" nil)
      (first chars))))

(defund two-non-whitespace-chars-existp (chars)
  (declare (xargs :guard (character-listp chars)))
  (consp (skip-whitespace (cdr (skip-whitespace chars)))))

;peeks ahead to the second non-whitespace char (does not change the byte stream)
(defun second-non-whitespace-char (chars)
  (declare (xargs :guard (and (character-listp chars)
                              (two-non-whitespace-chars-existp chars))))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        (hard-error 'second-non-whitespace-char "No more chars!" nil)
      (let* ((chars (cdr chars)) ;skip the first char
             (chars (skip-whitespace chars)))
        (if (endp chars)
            (hard-error 'second-non-whitespace-char "No more chars!" nil)
          (first chars))))))

;returns (mv char chars)
(defund parse-next-non-whitespace-char (chars)
  (declare (xargs :guard (character-listp chars)))
  (let ((chars (skip-whitespace chars)))
    (if (endp chars)
        (mv (hard-error 'parse-next-non-whitespace-char "No more chars!" nil)
            chars)
      (mv (first chars) (rest chars)))))

(defthm CHARACTER-LISTP-of-MV-NTH-1-of-PARSE-NEXT-NON-WHITESPACE-CHAR
  (IMPLIES (CHARACTER-LISTP chars)
           (CHARACTER-LISTP (MV-NTH 1 (PARSE-NEXT-NON-WHITESPACE-CHAR CHARS))))
  :hints (("Goal" :in-theory (enable PARSE-NEXT-NON-WHITESPACE-CHAR))))

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

(defun skip-char (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (first-char chars)
          (parse-next-non-whitespace-char chars)
          (declare (ignore first-char))
          chars))

(defun skip-two-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (first-char chars)
          (parse-next-non-whitespace-char chars)
          (declare (ignore first-char))
          (mv-let (second-non-whitespace-char chars)
                  (parse-next-non-whitespace-char chars)
                  (declare (ignore second-non-whitespace-char))
                  chars)))

(defun skip-through-two-chars (first-non-whitespace-char second-non-whitespace-char chars)
  (declare (xargs ;; :guard (and (characterp first-non-whitespace-char)
                  ;;             (characterp second-non-whitespace-char)
                  ;;             (character-listp chars))
                  :measure (len chars)
                  ;; :guard-hints (("Goal" :in-theory (enable two-non-whitespace-chars-existp skip-whitespace)))
                  ))
  (if (or (endp chars) (endp (rest chars))) ;for termination (think about this)
      (er hard? 'skip-through-two-chars "Not enough chars" nil)
    (if (and (eql first-non-whitespace-char (next-non-whitespace-char chars))
             (eql second-non-whitespace-char (second-non-whitespace-char chars)))
        (skip-two-chars chars)
      (skip-through-two-chars first-non-whitespace-char second-non-whitespace-char (skip-char chars)))))

(defun skip-xml-prolog (chars)
;;  (declare (xargs :guard (character-listp chars)))
  (if (and (eql #\< (next-non-whitespace-char chars))
           (eql #\? (second-non-whitespace-char chars)))
      (let* ((chars (skip-two-chars chars))
             (chars (skip-through-two-chars #\? #\> chars)))
        chars)
    chars))

;returns (mv some-chars chars)
;does not skip whitespace??
(defun parse-until-delim (delim chars)
  (declare (xargs :guard (and (characterp delim) (character-listp chars))
                  :measure (len chars)))
  (if (not (consp chars))
      (prog2$ (er hard? 'parse-until-delim "Not enough chars" nil)
              (mv nil chars))
    (let ((first (first chars))) ;next-non-whitespace-char
      (if (eql delim first)
          (mv nil chars)
        (mv-let (rest chars)
          (parse-until-delim delim (rest chars))
          (mv (cons first rest)
              chars))))))

(defthm len-of-parse-until-delim
  (<= (len (mv-nth 1 (parse-until-delim delim chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable))))

;does not skip whitespace
;returns (mv some-chars chars)
(defund parse-until-delims (delims chars)
  (if (endp chars)
      (mv (hard-error 'parse-until-delims "Ran out of chars." nil)
          chars)
    (let ((first-char (first chars)))
      (if (member first-char delims)
          (mv nil chars)
        (mv-let (rest chars)
                (parse-until-delims delims (rest chars))
                (mv (cons first-char rest)
                    chars))))))

(defthm len-of-parse-until-delims
  (<= (len (mv-nth 1 (parse-until-delims delims chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (parse-until-delims) ()))))

;;  Defining this separately so we can disable it
(defund parse-element-name-chars ()
   (append *whitespace-chars* '(#\> #\/ #\<)))
(in-theory (disable (:e parse-element-name-chars))) ;TODO: Without this, some goals printed below are quite weird

;fixme think about what chars are legal here
;returns (mv element-name element-name-chars chars)
(defund parse-element-name (chars)
  (mv-let (name-chars chars)
          (parse-until-delims (parse-element-name-chars) chars)
          (mv (coerce name-chars 'string) name-chars chars)))

(defthm len-of-parse-element-name
  (<= (len (mv-nth 2 (parse-element-name chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (parse-element-name) (BINARY-APPEND)))))

(defund parse-attribute-name (chars)
  (mv-let (name-chars chars)
          (parse-until-delim #\= chars)
          (mv (coerce name-chars 'string) chars)))

(defthm len-of-parse-attribute-name
  (<= (len (mv-nth 1 (parse-attribute-name chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-attribute-name))))

(defund parse-quoted-string (chars)
;  (declare (xargs :guard (character-listp chars)))
  (let ((chars (skip-known-char #\" chars)))
    (mv-let (string-chars chars)
            (parse-until-delim #\" chars)
            (let ((chars (skip-known-char #\" chars)))
              (mv (coerce string-chars 'string) chars)))))

(defthm len-of-parse-quoted-string
  (<= (len (mv-nth 1 (parse-quoted-string chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-quoted-string))))

;returns (mv attrib chars)
; Parse an attribute like foo="bar"
(defund parse-xml-attrib (chars)
;  (declare (xargs :guard (character-listp chars)))
  (let ((chars (skip-whitespace chars)))
    (mv-let (name chars)
            (parse-attribute-name chars)
            (let ((chars (skip-known-char #\= chars)))
              (mv-let (val chars)
                      (parse-quoted-string chars)
                      (mv `(= ,name ,val)
                          chars))))))

(defthm len-of-PARSE-XML-ATTRIB
  (implies (consp chars)
           (< (len (MV-NTH 1 (PARSE-XML-ATTRIB CHARS)))
              (len chars)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable PARSE-XML-ATTRIB
                                     SKIP-KNOWN-CHAR ;todo
                                     parse-next-non-whitespace-char
                                     ))))

(defthm len-of-PARSE-XML-ATTRIB-weak
  (<= (len (MV-NTH 1 (PARSE-XML-ATTRIB CHARS)))
      (len chars))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable PARSE-XML-ATTRIB))))

;returns (mv attribs chars)
;Parse attributes of the form foo="bar" until > or /> is seen
(defun parse-xml-attribs (chars)
  (declare (xargs :measure (len chars)))
  (if (endp chars) ;for termination (think about this)
      (mv nil chars)
    (if (not (member (next-non-whitespace-char chars) '(#\> #\/)))
        (mv-let (attrib chars)
          (parse-xml-attrib chars)
          (mv-let (attribs chars)
            (parse-xml-attribs chars)
            (mv (cons attrib attribs)
                chars)))
      (mv nil chars))))

(defthm len-of-parse-xml-attribs
  (<= (len (mv-nth 1 (parse-xml-attribs chars))) (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-xml-attribs))))

;does not allow whitespace to intervene
(defun skip-known-chars (target-chars chars)
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
  :hints (("Goal" :in-theory (enable skip-known-char))))

;TODO:  We may know that there is no whitespace before the < ?
(defun skip-matching-tag (element-name-chars chars)
  (declare (xargs :guard (and (character-listp element-name-chars)
                              (character-listp chars))))
  (let* ((chars (skip-known-char #\< chars))
         (chars (skip-known-char #\/ chars))
         (chars (skip-known-chars element-name-chars chars))
         (chars (skip-known-char #\> chars)))
    chars))

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
      (er hard? 'skip-xml-comment "Ran out of chars when parsing comment.")
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

;; chars should begin with <!--
(defun skip-xml-comment (chars)
  (declare (xargs :guard (character-listp chars)))
  (let* ((chars (skip-known-char #\< chars))
         (chars (skip-known-char #\! chars))
         (chars (skip-known-char #\- chars))
         (chars (skip-known-char #\- chars)))
    (read-to-end-of-xml-comment chars)))

;; Initially, this called (len chars), which was slow
(defun maybe-skip-xml-comment (chars)
  (declare (xargs :guard (character-listp chars)))
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

(mutual-recursion
 ;; Parse an XML element, which should be either an empty element the form
 ;; <elementname attrib1="val" attrib2="val2" ... /> or an element with
 ;; subelements, of the form <elementname attrib1="val" attrib2="val2" ... >
 ;; ... characters and sub elements ... </elementname>.  Returns (mv elem
 ;; chars).  The first character of CHARS should be <.  Whitespace within the
 ;; tag itself is not significant (but whitespace between tags is).
 (defun parse-xml-element (chars)
   (declare (xargs; :guard (character-listp chars)
                   :measure (make-ord 1 (+ 1 (len chars)) 0)
                   :hints (("Goal" ; :induct t
                            :in-theory (disable SKIP-char next-non-whitespace-char second-non-whitespace-char)
                            ;;:expand (PARSE-XML-ELEMENT CHARS) ;todo: illegal hint!
                            ))))
   (if (endp chars)
       (prog2$ (er hard 'parse-xml-element "Not enough chars!")
               (mv nil nil))
     (let ((first-char (first chars)))
       (if (not (eql #\< first-char))
           (mv nil (er hard? 'parse-xml-element "Element must start with a <, but we got ~x0." first-char))
         (let ((chars (rest chars)))
           (mv-let (element-name element-name-chars chars)
             (parse-element-name chars)
             (mv-let (attribs chars)
               (parse-xml-attribs chars)
               (if (eql #\/ (next-non-whitespace-char chars))
                   ;;an empty element (i.e., no nested elements)
                   (let* ((chars (skip-known-char #\/ chars))
                          (chars (skip-known-char #\> chars)))
                     (mv `(,element-name ,@attribs) ;no sub-elements
                         chars))
                 (if (eql #\> (next-non-whitespace-char chars))
                     ;; there are nested elements:
                     (let ((chars (skip-known-char #\> chars)))
                       (mv-let (items chars)
                         (parse-xml-elements-and-strings chars)
                         (let ((chars (skip-matching-tag element-name-chars chars)))
                           (mv `(,element-name ,@attribs ,@items)
                               chars))))
                   (mv (hard-error 'parse-xml-element "Unexpected char in XML element opening tag." nil)
                       chars))))))))))

 ;; Parse and XML string up to an occurrence of '<' indicating the next tag.
 ;; Returns (mv string chars).
 (defun parse-xml-string (chars)
   (declare (xargs; :guard (character-listp chars)
                   :measure (len chars)))
   (if (endp chars)
       (mv "" nil)
     (let* ((chars (maybe-skip-xml-comment chars))
            (first-char (first chars)))
       (if (eql #\< first-char) ;end of the string
           (mv "" chars)
         (mv-let (string2 chars)
           (parse-xml-string (rest chars))
           (mv (coerce (cons first-char (coerce string2 'list)) 'string)
               chars))))))

 ;; Parse the contents of an XML element, which may be strings and
 ;; sub-elements, up to a closing tag returns (mv elems chars)
 (defun parse-xml-elements-and-strings (chars)
   (declare (xargs; :guard (character-listp chars)
                   :measure (make-ord 1 (+ 1 (len chars)) 1)))
   (if (not (consp chars))
       (mv nil nil)
     (let ((first-char (first chars))
           (orig-chars chars))
       (if (not (eql #\< first-char))
           ;; Anything other than < gets parsed as a string:
           (mv-let (item chars)
             (parse-xml-string chars)
             (if (not (< (len chars) (len orig-chars)))
                 (prog2$ (er hard 'parse-xml-elements-and-strings "This should never happen.")
                         (mv nil nil))
               (mv-let (items chars)
                 (parse-xml-elements-and-strings chars)
                 (mv (cons item items) chars))))
         (if (eql #\/ (next-non-whitespace-char (rest chars)))
             ;; It's a closing tag, so stop
             (mv nil chars)
         (if (and (>= (len chars) 4) ;; a comment starts with <!-- ;TODO: slow?
                  (eql #\! (cadr chars))
                  (eql #\- (caddr chars))
                  (eql #\- (cadddr chars)))
             ;; It's a comment, so skip it
             (let ((chars (skip-xml-comment chars)))
               (parse-xml-elements-and-strings chars))
           ;; It's a tag but not a comment or a closing tag, so parse an element:
           (mv-let (item chars)
             (parse-xml-element chars)
             (if (not (< (len chars) (len orig-chars))) ;slow?!
                 (prog2$ (er hard 'parse-xml-elements-and-strings "This should never happen.")
                         (mv nil nil))
               (mv-let (items chars)
                 (parse-xml-elements-and-strings chars)
                 (mv (cons item items) chars)))))))))))

;Returns a list of XML elements and strings
(defun parse-xml-chars (chars)
  (declare (xargs ;; :guard (character-listp chars)
                  ))
  (let ((chars (skip-xml-prolog chars)))
    (mv-let (elem chars)
            (parse-xml-elements-and-strings chars)
            (let ((chars (skip-whitespace chars))) ;skip any trailing whitespace
              (if (endp chars)
                  elem
                ;cannot happen?
                (prog2$ (cw "Chars left: ~x0" chars)
                        (hard-error 'parse-xml-chars "Unexpected chars found." nil)))))))

(mutual-recursion
 (defun drop-whitespace-strings-from-parsed-xml-element (item)
   (if (not (consp item))
       (er hard? 'drop-whitespace-strings-from-parsed-xml-items "Bad XML item: ~x0" item)
     (let* ((name (car item))
            (attribs (get-xml-attributes (cdr item)))
            (sub-items (skip-xml-attributes (cdr item))))
       `(,name ,@attribs ,@(drop-whitespace-strings-from-parsed-xml-items sub-items)))))

 (defun drop-whitespace-strings-from-parsed-xml-items (items)
   (declare (xargs :measure (acl2-count items)))
   (if (endp items)
       nil
     (let ((item (first items)))
       (if (stringp item)
           (if (whitespace-string-p item)
               (drop-whitespace-strings-from-parsed-xml-items (rest items))
             (cons item (drop-whitespace-strings-from-parsed-xml-items (rest items))))
         (cons (drop-whitespace-strings-from-parsed-xml-element item)
               (drop-whitespace-strings-from-parsed-xml-items (rest items))))))))

;;TODO: Must there be a single top-level element?  This is more general
;;Returns (mv elements-and-strings state)
(defun parse-xml-file (input-xml-file drop-whitespace-stringsp state)
  (declare (xargs :stobjs state ;;:mode :program
                  :verify-guards nil ; todo
                  ))
  (mv-let (erp bytes state) ; todo: read directly into a character list?
    (read-file-into-byte-list input-xml-file state)
    (if erp
        (prog2$ (er hard? 'parse-xml-file "Error reading from ~x0." input-xml-file)
                (mv nil state))
      (let* ((chars (map-code-char bytes))
             (parsed-items (parse-xml-chars chars))
             (parsed-items (if drop-whitespace-stringsp
                               (drop-whitespace-strings-from-parsed-xml-items parsed-items)
                             parsed-items)))
        (mv parsed-items state)))))
