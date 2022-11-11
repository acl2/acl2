; A utility to get all currently-included books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a list of absolute paths.
;; This is based on something from Matt K:
(defun included-books-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program ; todo
                  ))
  (acl2::merge-sort-lexorder
   (remove-duplicates-equal ;todo: sort first and then optimize this
    (book-name-lst-to-filename-lst (strip-cars (global-val 'acl2::include-book-alist wrld))
                                   (project-dir-alist wrld)
                                   'top-level))))
