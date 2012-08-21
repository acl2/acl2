(in-package "ACL2")

; This books serves as a place to verify the termination and guards of ACL2
; system functions.  A user may wish to include this book or system/top.lisp
; when reasoning about system functions.

; Note that calling verify-termination also verifies the guards of any function
; that has a guard specified.  In the event that there is no guard specified,
; then one must also call verify-guards to verify that the implicit guard of
; "t" is strong enough.  See :doc verify-termination for further details.

(verify-termination fmt-char) ; and guards
(verify-termination fmt-var) ; and guards
(verify-termination missing-fmt-alist-chars1) ; and guards
(verify-termination missing-fmt-alist-chars) ; and guards
