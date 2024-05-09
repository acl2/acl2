; A utility to get all included books in the current world
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (in-theory (disable global-val)))

;; Returns a list of all books included in WRLD, including books brought in
;; indirectly via other include-books.  Returns a list of full-book-strings
;; (absolute pathnames, including the .lisp extensions).
;; Previously, this removed duplicates, but that doesn't seem necessary.
;; Another version of this sorted the result, but that doesn't seem necessary.
(defund all-included-books (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((include-book-alist (global-val 'include-book-alist wrld)))
    (if (not (alistp (global-val 'include-book-alist wrld)))
        (er hard? 'all-included-books "Ill-formed include-book-alist (not an alist): ~x0." include-book-alist)
      (let ((book-names (strip-cars include-book-alist)))
        (if (not (book-name-listp book-names))
            (er hard? 'all-included-books "Ill-formed include-book-alist (some car is not a book-name): ~x0." include-book-alist)
          (book-name-lst-to-filename-lst book-names
                                         (project-dir-alist wrld)
                                         'top-level))))))
