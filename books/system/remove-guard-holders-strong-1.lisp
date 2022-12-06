; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The books remove-guard-holders-lemmas.lisp and remove-guard-holders.lisp are
; so named for historical reasons.  They actually get us through termination
; and guard verification only for remove-guard-holders-weak.  It is much more
; challenging to get remove-guard-holders in :logic mode, let alone
; guard-verified.  This book and remove-guard-holders-strong-ideal-mode.lisp
; make a start at that, putting several functions into :logic mode along the
; way.  The present book is restricted to promotion all the way to being
; guard-verified.  The book remove-guard-holders-strong-ideal-mode.lisp
; contains work towards putting remove-guard-holders.lisp into logic mode that
; puts some system functions into :logic mode without guard verification.  Do
; not include that book when you are using ACL2!  It may slow down ACL2
; significantly.

; Further progress is attempted in remove-guard-holders-strong-2.lisp, which
; however is flawed, as explained there.

; I'd be happy for someone to finish this work!  Please inform me if you work
; on that, to avoid duplication of effort.

(in-package "ACL2")

(include-book "remove-guard-holders")
(include-book "termp")
(include-book "subst-var")

(verify-termination flatten-ands-in-lit-lst) ; and guards
(verify-termination translate-declaration-to-guard/integer-gen) ; and guards
(verify-termination subst-each-for-var) ; and guards
(verify-termination possibly-dirty-lambda-objectp1) ; and guards

(local (in-theory (disable remove-guard-holders-weak)))

(verify-termination translate-declaration-to-guard1-gen) ; and guards
(verify-termination translate-declaration-to-guard-gen) ; and guards
(verify-termination subst-each-for-var) ; and guards

; See remove-guard-holders-strong-2.lisp for an attempt to make further
; progress towards putting remove-guard-holders into :logic mode.
; File remove-guard-holders-strong-3.lsp might be worth a look, too.
