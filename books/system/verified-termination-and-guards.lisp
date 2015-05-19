; Copyright (C) 2014, Regents of the University of Texas
; Written by David Rager (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; This books serves as a place to verify the termination and guards of ACL2
; system functions.  A user may wish to include this book or system/top.lisp
; when reasoning about system functions.

; Note that calling verify-termination also verifies the guards of any function
; that has a guard specified.  In the event that there is no guard specified,
; then one must also call verify-guards to verify that the implicit guard of
; "t" is strong enough.  See :doc verify-termination for further details.

; (verify-termination fmt-char) ; and guards
; (verify-termination fmt-var) ; and guards

(value-triple "This book formerly contained only two forms, both of which ~
               were executed only when #+acl2-legacy-doc.")
