; Converts parsed BibTeX entries to XDOC documentation
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Aakash Koneru (akitaki79 on GitHub)

(in-package "ACL2")

(include-book "bibtex-parser")  ; Use the parser
(include-book "xdoc/top" :dir :system)
(include-book "std/strings/strsubst" :dir :system)

; Conversion functions for XDOC generation
; TODO: add guards

(defun strip-brackets (str)
  "Remove curly braces from BibTeX strings"
  (if (stringp str)
      (str::strsubst "{" "" (str::strsubst "}" "" str))  ; replace with empty string
    str))

(defun convert-bibtex-diacritics (str)
  (if (not (stringp str))
      str
    (let* (
           ; Acute accents (\')
           (step1 (str::strsubst "\\'a" "&aacute;" str))
           (step2 (str::strsubst "\\'A" "&Aacute;" step1))
           (step3 (str::strsubst "\\'e" "&eacute;" step2))
           (step4 (str::strsubst "\\'E" "&Eacute;" step3))
           (step5 (str::strsubst "\\'i" "&iacute;" step4))
           (step6 (str::strsubst "\\'I" "&Iacute;" step5))
           (step7 (str::strsubst "\\'o" "&oacute;" step6))
           (step8 (str::strsubst "\\'O" "&Oacute;" step7))
           (step9 (str::strsubst "\\'u" "&uacute;" step8))
           (step10 (str::strsubst "\\'U" "&Uacute;" step9))
           (step10A (str::strsubst "\\'n" "&nacute;" step10))
           (step10B (str::strsubst "\\'N" "&Nacute;" step10A))

           ; Grave accents (\`)
           (step11 (str::strsubst "\\`a" "&agrave;" step10B))
           (step12 (str::strsubst "\\`A" "&Agrave;" step11))
           (step13 (str::strsubst "\\`e" "&egrave;" step12))
           (step14 (str::strsubst "\\`E" "&Egrave;" step13))
           (step15 (str::strsubst "\\`i" "&igrave;" step14))
           (step16 (str::strsubst "\\`I" "&Igrave;" step15))
           (step17 (str::strsubst "\\`o" "&ograve;" step16))
           (step18 (str::strsubst "\\`O" "&Ograve;" step17))
           (step19 (str::strsubst "\\`u" "&ugrave;" step18))
           (step20 (str::strsubst "\\`U" "&Ugrave;" step19))

           ; Circumflex accents (\^)
           (step21 (str::strsubst "\\^a" "&acirc;" step20))
           (step22 (str::strsubst "\\^A" "&Acirc;" step21))
           (step23 (str::strsubst "\\^e" "&ecirc;" step22))
           (step24 (str::strsubst "\\^E" "&Ecirc;" step23))
           (step25 (str::strsubst "\\^i" "&icirc;" step24))
           (step26 (str::strsubst "\\^I" "&Icirc;" step25))
           (step27 (str::strsubst "\\^o" "&ocirc;" step26))
           (step28 (str::strsubst "\\^O" "&Ocirc;" step27))
           (step29 (str::strsubst "\\^u" "&ucirc;" step28))
           (step30 (str::strsubst "\\^U" "&Ucirc;" step29))

           ; Umlaut/diaeresis (\")
           (step31 (str::strsubst "\\\"a" "&auml;" step30))
           (step32 (str::strsubst "\\\"A" "&Auml;" step31))
           (step33 (str::strsubst "\\\"e" "&euml;" step32))
           (step34 (str::strsubst "\\\"E" "&Euml;" step33))
           (step35 (str::strsubst "\\\"i" "&iuml;" step34))
           (step36 (str::strsubst "\\\"I" "&Iuml;" step35))
           (step37 (str::strsubst "\\\"o" "&ouml;" step36))
           (step38 (str::strsubst "\\\"O" "&Ouml;" step37))
           (step39 (str::strsubst "\\\"u" "&uuml;" step38))
           (step40 (str::strsubst "\\\"U" "&Uuml;" step39))

           ; Tilde (\~)
           (step41 (str::strsubst "\\~a" "&atilde;" step40))
           (step42 (str::strsubst "\\~A" "&Atilde;" step41))
           (step43 (str::strsubst "\\~n" "&ntilde;" step42))
           (step44 (str::strsubst "\\~N" "&Ntilde;" step43))
           (step45 (str::strsubst "\\~o" "&otilde;" step44))
           (step46 (str::strsubst "\\~O" "&Otilde;" step45))

           ; Ring above (\r)
           (step47 (str::strsubst "\\ra" "&aring;" step46))
           (step48 (str::strsubst "\\rA" "&Aring;" step47))

           ; Cedilla (\c)
           (step49 (str::strsubst "\\cc" "&ccedil;" step48))
           (step50 (str::strsubst "\\cC" "&Ccedil;" step49))

           ;Ogonek (\k)
           (step51 (str::strsubst "\\ka" "&aogon;" step50))
           (step52 (str::strsubst "\\kA" "&Aogon;" step51))
           (step53 (str::strsubst "\\ke" "&eogon;" step52))
           (step54 (str::strsubst "\\kE" "&Eogon;" step53))
           (step55 (str::strsubst "\\ku" "&uogon;" step54))
           (step56 (str::strsubst "\\kU" "&Uogon;" step55))
           (step57 (str::strsubst "\\ki" "&iogon;" step56))
           (step58 (str::strsubst "\\kI" "&Iogon;" step57)))
      step58)))

(defun find-next-dollar (str start-pos)
  (declare (xargs :measure (nfix (- (length str) start-pos))))
  (if (or (not (stringp str))
          (not (natp start-pos))
          (>= start-pos (length str)))
      nil
    (if (equal (char str start-pos) #\$)
        start-pos
      (find-next-dollar str (+ start-pos 1)))))

(defun convert-math-syntax-helper (str pos acc in-math)
  "Convert $...$ to @($...$) by processing character by character"
  (declare (xargs :measure (if (and (stringp str) (natp pos))
                               (nfix (- (length str) pos))
                             0)))
  (if (or (not (stringp str))
          (not (natp pos))
          (>= pos (length str)))
      acc
    (let ((current-char (char str pos)))
      (cond
        ;; Found $ and we're not in math mode - start math
        ((and (equal current-char #\$) (not in-math))
         (convert-math-syntax-helper str (+ pos 1)
                                   (concatenate 'string acc "@($")
                                   t))
        ;; Found $ and we're in math mode - end math
        ((and (equal current-char #\$) in-math)
         (convert-math-syntax-helper str (+ pos 1)
                                   (concatenate 'string acc "$)")
                                   nil))
        ;; Regular character - just append
        (t (convert-math-syntax-helper str (+ pos 1)
                                     (concatenate 'string acc (string current-char))
                                     in-math))))))

; Convert all occurrences of $...$ in bibtex to @($...$) for XDOC Katex"
(defun convert-math-syntax (str)
  (if (stringp str)
      (convert-math-syntax-helper str 0 "" nil)
    str))

; formatting functions

(defun format-author-names (author-str)
  "Format author names for display"
  (if (stringp author-str)
      (convert-bibtex-diacritics (convert-math-syntax (strip-brackets author-str)))
    "Unknown Author"))

(defun format-title (title-str)
  "Format title for display"
  (if (stringp title-str)
      (convert-bibtex-diacritics (convert-math-syntax (strip-brackets title-str)))
    "Untitled"))

(defun get-field-value (field-name fields)
  "Get the value of a field from the fields alist"
  (let ((pair (assoc-equal field-name fields)))
    (if pair
        (cdr pair)
      nil)))

(defun get-entry-field (field-name entry)
  "Get a top-level field from a BibTeX entry (type, key, or fields)"
  (let ((pair (assoc-equal field-name entry)))
    (if pair
        (cdr pair)
      nil)))

(defun format-year (year-str)
  "Format year for display"
  (if year-str
      year-str
    "Unknown Year"))

(defun format-pages (pages-str)
  "Format page numbers for display"
  (if pages-str
      (concatenate 'string "pp. " pages-str)
    ""))

(defun format-entry-type (entry-type)
  "Format entry type for display"
  (cond ((equal entry-type "article") "Journal Article")
        ((equal entry-type "inproceedings") "Conference Paper")
        ((equal entry-type "incollection") "Book Chapter")
        ((equal entry-type "techreport") "Technical Report")
        (t (concatenate 'string
                        (string-upcase (subseq entry-type 0 1))
                        (subseq entry-type 1 nil)))))

(defun generate-bibtex-entry-XDOC (entry)
  "Generate XDOC list item for a single BibTeX entry"
  (let* ((entry-type (get-entry-field "type" entry))
         (fields (get-entry-field "fields" entry))
         (author (get-field-value "author" fields))
         (title (get-field-value "title" fields))
         (year (get-field-value "year" fields))
         (pages (get-field-value "pages" fields))
         (publisher (get-field-value "publisher" fields))
         (booktitle (get-field-value "booktitle" fields))
         (month (get-field-value "month" fields))
         (isbn (get-field-value "isbn" fields))
         (doi (get-field-value "doi" fields)))

    (concatenate 'string
                 "<li><b>" (format-title title) "</b>, "
                 (format-author-names author)
                 (if booktitle
                     (concatenate 'string ", in <i>" (strip-brackets booktitle) "</i>")
                   "")
                 (if publisher
                     (concatenate 'string ", " (strip-brackets publisher))
                   "")
                 (if year
                     (concatenate 'string ", " (strip-brackets year))
                   "")
                 (if month
                     (concatenate 'string ", " (strip-brackets month))
                   "")
                 (if pages
                     (concatenate 'string ", " (format-pages pages))
                   "")
                 (if isbn
                     (concatenate 'string ", ISBN: " (strip-brackets isbn))
                   "")
                 (if doi
                     (concatenate 'string ", DOI: " (strip-brackets doi))
                   "")
                 ". [" (format-entry-type entry-type) "]"
                 "</li>")))

(defun generate-bibtex-entries-XDOC (entries)
  "Generate XDOC list items for all BibTeX entries"
  (if (endp entries)
      ""
    (let ((entry-pair (car entries)))
      (if (and (consp entry-pair)
               (stringp (car entry-pair))
               (alistp (cdr entry-pair)))
          (concatenate 'string
                       (generate-bibtex-entry-XDOC (cdr entry-pair))
                       (generate-bibtex-entries-XDOC (cdr entries)))
        (generate-bibtex-entries-XDOC (cdr entries))))))
