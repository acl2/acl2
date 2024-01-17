; Adding .lisp to a book path if needed
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/strings-light/string-ends-withp" :dir :system)

;; Elaborates a book path that may not end in .lisp (e.g., when supplied by a
;; human).  If it already ends in .lisp, do nothing.  Otherwise, add .lisp.
;; (In the rare care that a file ends in .lisp.lisp, the whole path has to be
;; given.)
(defund maybe-add-dot-lisp-extension (book)
  (declare (xargs :guard (stringp book)))
  (if (string-ends-withp book ".lisp") ; tolerate existing .lisp extension
      book
    (concatenate 'string book ".lisp")))
