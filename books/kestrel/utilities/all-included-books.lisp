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

;; Returns a list of absolute pathnames
(defund all-included-books (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((include-book-alist (global-val 'include-book-alist wrld)))
    (if (not (alistp (global-val 'include-book-alist wrld)))
        (er hard? 'all-included-books "Ill-formed include-book-alist (not an alist): ~x0." include-book-alist)
      (let ((book-names (strip-cars include-book-alist)))
        (if (not (book-name-listp book-names))
            (er hard? 'all-included-books "Ill-formed include-book-alist (some car is not a book-name): ~x0." include-book-alist)
          (remove-duplicates-equal
           (book-name-lst-to-filename-lst book-names
                                          (project-dir-alist wrld)
                                          'top-level)))))))
