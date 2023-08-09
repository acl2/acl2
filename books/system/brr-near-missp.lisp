; Copyright (C) 2023, ForrestHunt, Inc.
; Written by J Moore, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For relevant discussion see brr-near-missp-support.lisp.

(in-package "ACL2")

(local (include-book "brr-near-missp-support"))

(verify-termination one-way-unify1-quotep-subproblems)
(verify-termination one-way-unify1)
(verify-guards one-way-unify1)
(verify-termination one-way-unify)
(verify-termination alistp-listp)
(verify-termination one-way-unify-restrictions1)
(verify-termination one-way-unify-restrictions)
(verify-termination gsym)
(verify-termination genvar1-guardp)

; For genvar1 to be in guard-verified logic mode, we need legal-variablep to be
; as well.  In brr-near-missp-support.lisp this is accomplished by including
; tools/flag, but here, without including that book, we need to be explicit.
(verify-termination legal-variable-or-constant-namep)
(verify-guards legal-variable-or-constant-namep)
(verify-termination legal-variablep)
(verify-guards legal-variablep)

(verify-termination genvar1
  (declare (xargs :measure
                  (:? pkg-witness char-lst avoid-lst cnt))))
(verify-termination genvar-guardp)
(verify-termination genvar)
(verify-termination abstract-pat1)
(verify-guards abstract-pat1)
(verify-termination abstract-pat)
(verify-termination symbol-alist-to-keyword-value-list)
(verify-termination brr-criteria-alistp)
(verify-termination make-built-in-brr-near-miss-msg)
(verify-termination get-brr-one-way-unify-info)
(verify-termination built-in-brr-near-missp)
