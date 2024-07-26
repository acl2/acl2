; Use with-supporters to just get the code of improve-book
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

;; The point of this book is to provide the improve-book utility without
;; causing its supporting libraries to be included.  This helps minimize the
;; effect on the books being improved of including the improve-book tool
;; itself.

(defttag improve-book) ; because books-in-subtree and books-in-dir call sys-call+

(with-supporters
  (local (include-book "improve-book"))
  ;; Export only these functions/macros and their supporting definitions:
 :names (improve-books-in-subtree
         improve-books
         improve-books-fn
         improve-book
         improve-book-fn))
