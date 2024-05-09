; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book was called remove-guard-holders.lisp through late January, 2023.

(in-package "ACL2")

(local (include-book "remove-guard-holders1"))

(include-book "subcor-var") ; since remove-guard-holders1 calls subcor-var

(verify-termination weak-badge-userfn-structure-alistp) ; and guards

(verify-termination apply$-badge-p) ; and guards

(verify-termination badge-userfn-structure-alistp) ; and guards

(verify-termination apply$-badge-alistp-ilks-t) ; and guards

#+acl2-devel ; avoid error for redundant def. with raw Lisp code
(verify-termination ilks-plist-worldp) ; and guards

(verify-termination ilks-per-argument-slot) ; and guards

(verify-termination remove-guard-holders1)
(verify-guards remove-guard-holders1)

(verify-termination remove-guard-holders-weak) ; and guards
