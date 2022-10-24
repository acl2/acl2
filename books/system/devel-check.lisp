; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book includes books verifying termination and guards of system
; functions, in support of ../../GNUmakefile target devel-check.  See
; *system-verify-guards-alist* in the ACL2 sources, or see :DOC
; verify-guards-for-system-functions, for how this book relates to which
; functions in the ACL2 system come up in :logic mode.  Over time various
; people have added books included below to support expansion of
; *system-verify-guards-alist*.

; This book's name is referenced in the ACL2 sources as the value of constant
; *devel-check-book*.

(in-package "ACL2")

(include-book "system/apply/loop-scions" :dir :system)

; The books included below are a subset (not necessarily a proper subset) of
; those included in top.lisp.

(include-book "verified-termination-and-guards")
(include-book "sublis-var")
(include-book "subcor-var")
(include-book "subst-expr")
(include-book "subst-var")
(include-book "meta-extract")
(include-book "legal-variablep")
(include-book "merge-sort-term-order")
(include-book "termp")
(include-book "kestrel")
(include-book "remove-guard-holders")
(include-book "merge-sort-symbol-lt")
(include-book "pseudo-good-worldp") ; for e.g. macro-args-structurep
(include-book "bind-macro-args")
(include-book "case-match")
(include-book "fmx-cw")
(include-book "all-fnnames")
(include-book "observation1-cw")
(include-book "defstobj")

; The following is commented out because we aren't currently motivated to put
; its functions into ACL2 system constant *system-verify-guards-alist*, which
; would require guards to be verified for functions in that book.

; (include-book "untranslate-car-cdr")
