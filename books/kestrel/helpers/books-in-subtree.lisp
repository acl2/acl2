; Finding all the books in a dir or subtree
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/strings-light/strip-suffix-from-strings" :dir :system)
(include-book "kestrel/strings-light/split-string-repeatedly" :dir :system)
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(defttag books-in-subtree) ; for sys-call+ below

;; Looks for .lisp files in the current subtree.
;; Returns (mv book-paths state) where the BOOK-PATHS have no .lisp extensions.
(defun books-in-subtree (state)
  (declare (xargs :stobjs state))
  (mv-let (erp filename-lines state)
    (sys-call+ "find" '("." "-name" "*.lisp") state)
    (if erp
        (prog2$ (er hard? 'books-in-subtree "Failed to find books: ~x0." erp)
                (mv nil state))
      (mv (strip-suffix-from-strings ".lisp" (remove-equal "" (split-string-repeatedly filename-lines #\Newline)))
          state))))

;move
;; Looks for .lisp files in the current subtree.
;; Returns (mv book-paths state) where the BOOK-PATHS have no .lisp extensions.
(defun books-in-dir (state)
  (declare (xargs :stobjs state))
  (mv-let (erp filename-lines state)
    (sys-call+ "find" '("." "-maxdepth" "1" "-name" "*.lisp") state)
    (if erp
        (prog2$ (er hard? 'books-in-dir "Failed to find books: ~x0." erp)
                (mv nil state))
      (mv (strip-suffix-from-strings ".lisp" (remove-equal "" (split-string-repeatedly filename-lines #\Newline)))
          state))))
