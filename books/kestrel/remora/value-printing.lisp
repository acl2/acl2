; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold
; Contributing Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values-to-abstract-syntax")
(include-book "printer")

(include-book "std/strings/dec-digit-char-listp" :dir :system)

(local (include-book "std/omaps/top" :dir :system))
(local (include-book "arithmetic-3/top" :dir :system))

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ value-printing
  :parents (parsing-and-printing)
  :short "Printing of expression values in Remora concrete syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert expression values to expression ASTs,
     which we then print with the pretty-printer (see @(see printer))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-expr-value ((val expr-valuep) &key ((width natp) '80))
  :returns (mv (err booleanp) (string stringp))
  :short "Print an expression value in Remora concrete syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert the expression value back to an expression
     via @(tsee expr-value-to-expr)
     and print it with @(tsee print-expr).
     Fails when the conversion does (i.e. only for float values
     with no literal syntax)."))
  (b* (((mv err expr) (expr-value-to-expr val))
       ((when err) (mv t "")))
    (mv nil (print-expr expr :width width))))
