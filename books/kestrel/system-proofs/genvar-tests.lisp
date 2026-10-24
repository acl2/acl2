; Tests and examples for genvar.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; An example about genvar.  This book is not included by top.lisp.

(include-book "genvar")

;; The comments in genvar say that it generates a variable "in the same
;; package as pkg-witness", but the result can be a symbol imported into that
;; package:
(defthm genvar-can-return-an-imported-symbol
  (equal (genvar 'foo "LIST" nil nil)
         'common-lisp::list)
  :rule-classes nil)
