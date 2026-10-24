; Tests and examples for remove-guard-holders1-properties.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in
;; remove-guard-holders1-properties.lisp.  This book is not included by
;; top.lisp.

(include-book "remove-guard-holders1-properties")

;; The hypothesis about TO-DF is needed for the CHANGEDP contract: for a call
;; of TO-DF with two arguments, CHANGEDP is NIL but the second argument is
;; dropped.  (This doesn't indicate a bug, since translated terms have
;; correct arities.)
(defthm remove-guard-holders1-changedp-needs-unary-to-df
  (let ((term '(to-df x y)))
    (and (pseudo-termp term)
         (not (unary-to-df-callsp term))
         (equal (remove-guard-holders1 nil term nil)
                (mv nil '(to-df x)))))
  :hints (("Goal" :in-theory (enable unary-to-df-callsp)))
  :rule-classes nil)
