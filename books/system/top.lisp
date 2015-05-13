; Copyright (C) 2014, Regents of the University of Texas
; Written (originally) by Matt Kaufmann (original date April, 2010)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book includes books verifying termination and guards of system
; functions.  Add an include-book for each new such book.  (Various people have
; done so since this book was originally added.)

; See *system-verify-guards-alist* in ACL2 source file boot-strap-pass-2.lisp
; for how this book relates to which functions in the ACL2 system come up in
; :logic mode.

(in-package "ACL2")

(include-book "hl-addr-combine")
(include-book "extend-pathname")

; The following (commented-out) form is not needed in support of ACL2_DEVEL
; builds, the ACL2 devel-check `make' target, or the ACL2 constant
; *system-verify-guards-alist*.  If we uncomment it, then this book depends
; ultimately on many other books, and certification fails for some of those
; books for ACL2 built with ACL2_DEVEL set.

; (include-book "too-many-ifs")

(include-book "verified-termination-and-guards")
(include-book "sublis-var")
(include-book "subcor-var")
(include-book "subst-expr")
(include-book "subst-var")
(include-book "convert-normalized-term-to-pairs")
(include-book "gather-dcls")
(include-book "meta-extract")
(include-book "legal-variablep")
(include-book "merge-sort-term-order")
(include-book "termp")

; The following is commented out only because we aren't currently motivated to
; its functions in ACL2 system constant *system-verify-guards-alist*.  Perhaps
; that would be easy to do, but note that guards would need to be verified for
; functions defined in untranslate-car-cdr.lisp.

; (include-book "untranslate-car-cdr")
