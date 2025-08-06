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

(defun contains-diacritics-p (str)
  (declare (xargs :guard (stringp str)))
  (or (and (search "\\'" str) t)
      (and (search "\\`" str) t)
      (and (search "\\^" str) t)
      (and (search "\\\"" str) t)
      (and (search "\\~" str) t)
      (and (search "\\r" str) t)
      (and (search "\\c" str) t)
      (and (search "\\k" str) t)))

(defun contains-dollar-signs-p (str)
  (declare (xargs :guard (stringp str)))
  (and (search "$" str) t))

(defun convert-bibtex-diacritics (str)
  (declare (xargs :guard (stringp str)))
  (if (not (contains-diacritics-p str))
      str
    (let* (
           ; Acute accents (\')
           (str (str::strsubst "\\'a" "&aacute;" str))
           (str (str::strsubst "\\'A" "&Aacute;" str))
           (str (str::strsubst "\\'e" "&eacute;" str))
           (str (str::strsubst "\\'E" "&Eacute;" str))
           (str (str::strsubst "\\'i" "&iacute;" str))
           (str (str::strsubst "\\'I" "&Iacute;" str))
           (str (str::strsubst "\\'o" "&oacute;" str))
           (str (str::strsubst "\\'O" "&Oacute;" str))
           (str (str::strsubst "\\'u" "&uacute;" str))
           (str (str::strsubst "\\'U" "&Uacute;" str))
           (str (str::strsubst "\\'n" "&nacute;" str))
           (str (str::strsubst "\\'N" "&Nacute;" str))

           ; Grave accents (\`)
           (str (str::strsubst "\\`a" "&agrave;" str))
           (str (str::strsubst "\\`A" "&Agrave;" str))
           (str (str::strsubst "\\`e" "&egrave;" str))
           (str (str::strsubst "\\`E" "&Egrave;" str))
           (str (str::strsubst "\\`i" "&igrave;" str))
           (str (str::strsubst "\\`I" "&Igrave;" str))
           (str (str::strsubst "\\`o" "&ograve;" str))
           (str (str::strsubst "\\`O" "&Ograve;" str))
           (str (str::strsubst "\\`u" "&ugrave;" str))
           (str (str::strsubst "\\`U" "&Ugrave;" str))

           ; Circumflex accents (\^)
           (str (str::strsubst "\\^a" "&acirc;" str))
           (str (str::strsubst "\\^A" "&Acirc;" str))
           (str (str::strsubst "\\^e" "&ecirc;" str))
           (str (str::strsubst "\\^E" "&Ecirc;" str))
           (str (str::strsubst "\\^i" "&icirc;" str))
           (str (str::strsubst "\\^I" "&Icirc;" str))
           (str (str::strsubst "\\^o" "&ocirc;" str))
           (str (str::strsubst "\\^O" "&Ocirc;" str))
           (str (str::strsubst "\\^u" "&ucirc;" str))
           (str (str::strsubst "\\^U" "&Ucirc;" str))

           ; Umlaut/diaeresis (\")
           (str (str::strsubst "\\\"a" "&auml;" str))
           (str (str::strsubst "\\\"A" "&Auml;" str))
           (str (str::strsubst "\\\"e" "&euml;" str))
           (str (str::strsubst "\\\"E" "&Euml;" str))
           (str (str::strsubst "\\\"i" "&iuml;" str))
           (str (str::strsubst "\\\"I" "&Iuml;" str))
           (str (str::strsubst "\\\"o" "&ouml;" str))
           (str (str::strsubst "\\\"O" "&Ouml;" str))
           (str (str::strsubst "\\\"u" "&uuml;" str))
           (str (str::strsubst "\\\"U" "&Uuml;" str))

           ; Tilde (\~)
           (str (str::strsubst "\\~a" "&atilde;" str))
           (str (str::strsubst "\\~A" "&Atilde;" str))
           (str (str::strsubst "\\~n" "&ntilde;" str))
           (str (str::strsubst "\\~N" "&Ntilde;" str))
           (str (str::strsubst "\\~o" "&otilde;" str))
           (str (str::strsubst "\\~O" "&Otilde;" str))

           ; Ring above (\r)
           (str (str::strsubst "\\ra" "&aring;" str))
           (str (str::strsubst "\\rA" "&Aring;" str))

           ; Cedilla (\c)
           (str (str::strsubst "\\cc" "&ccedil;" str))
           (str (str::strsubst "\\cC" "&Ccedil;" str))

           ; Ogonek (\k)
           (str (str::strsubst "\\ka" "&aogon;" str))
           (str (str::strsubst "\\kA" "&Aogon;" str))
           (str (str::strsubst "\\ke" "&eogon;" str))
           (str (str::strsubst "\\kE" "&Eogon;" str))
           (str (str::strsubst "\\ki" "&iogon;" str))
           (str (str::strsubst "\\kI" "&Iogon;" str))
           (str (str::strsubst "\\ku" "&uogon;" str))
           (str (str::strsubst "\\kU" "&Uogon;" str)))
      str)))

(defun find-next-dollar (str start-pos)
  (declare (xargs :measure (nfix (- (length str) start-pos))
                  :guard (and (stringp str)
                              (natp start-pos)
                              (<= start-pos (length str)))))
  (if (or (not (mbt (natp start-pos)))
          (>= start-pos (length str)))
      nil
    (if (equal (char str start-pos) #\$)
        start-pos
      (find-next-dollar str (+ start-pos 1)))))

(defun convert-math-syntax-helper (str pos acc in-math)
  (declare (xargs :measure (if (and (stringp str) (natp pos))
                               (nfix (- (length str) pos))
                             0)
                  :guard (and (stringp str)
                              (natp pos)
                              (stringp acc)
                              (<= pos (length str)))))
  (if (or (not (mbt (stringp str)))
          (not (mbt (natp pos)))
          (>= pos (length str)))
      acc
    (let ((current-char (char str pos)))
      (cond
        ((and (equal current-char #\$) (not in-math))
         (convert-math-syntax-helper str (+ pos 1)
                                   (concatenate 'string acc "@($")
                                   t))
        ((and (equal current-char #\$) in-math)
         (convert-math-syntax-helper str (+ pos 1)
                                   (concatenate 'string acc "$)")
                                   nil))
        (t (convert-math-syntax-helper str (+ pos 1)
                                     (concatenate 'string acc (string current-char))
                                     in-math))))))

; Convert all occurrences of $...$ in bibtex to @($...$) for XDOC Katex"
(defun convert-math-syntax (str)
  (declare (xargs :guard (stringp str)))
  (if (not (contains-dollar-signs-p str))
      str
    (convert-math-syntax-helper str 0 "" nil)))

; formatting functions

(defun format-author-names (author-str)
  "Format author names for display"
  (if (stringp author-str)
      (convert-bibtex-diacritics (strip-brackets author-str))
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
