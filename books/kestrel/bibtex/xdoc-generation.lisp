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

; Helper functions for XDOC generation
; TODO: add guards

(defun strip-brackets (str)
  "Remove curly braces from BibTeX strings"
  (if (stringp str)
      (substitute #\  #\{ (substitute #\  #\} str))  ; replace with nothing
    str))

(defun format-author-names (author-str)
  "Format author names for display"
  (if (stringp author-str)
      (strip-brackets author-str)
    "Unknown Author"))

(defun format-title (title-str)
  "Format title for display, handling special characters"
  (if (stringp title-str)
      (strip-brackets title-str)
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
