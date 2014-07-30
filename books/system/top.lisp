; Copyright (C) 2014, Regents of the University of Texas
; Written (originally) by Matt Kaufmann (original date April, 2010)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book includes books verifying termination and guards of system
; functions.  Add an include-book for each new such book.  (Various people have
; done so since this book was originally added.)

(in-package "ACL2")

(include-book "hl-addr-combine")
(include-book "extend-pathname")
; The following is not needed in support of ACL2_DEVEL builds, the ACL2
; devel-check `make' target, or the ACL2 constant *system-verify-guards-alist*.
; If we uncomment it, then this book depends ultimately on many other books,
; and certification fails for some of those books for ACL2 built with
; ACL2_DEVEL set.
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
