; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "top")
(include-book "char-kinds")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Attempting to include char-kinds.lisp into top.lisp
; causes an error in defs-program.lisp,
; which has something to do with including uncertified books.
; To work around this issue, we avoid including char.kinds.lisp in top.lisp,
; and instead create this extended "top" file
; and include it in ../top.lisp instead of top.lisp,
; so that we get everything in the manual
; (this is why we call this file top-doc.lisp).
; We should look into adapting defs-program.lisp
; to work with including char-kinds.lisp into top.lisp,
; and then we'll remove this top-doc.lisp file.
