; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "subcor-var")

; This use of make-event is awkward.  But I couldn't find a better way to avoid
; problems caused by make-event storing a redundant event for
; verify-termination of remove-guard-holders1 during the first pass, which
; causes a failure during the second pass.
(make-event
 (er-let* ((event (verify-termination-fn '(remove-guard-holders1) state)))
   (value `(defmacro verify-termination-remove-guard-holders1 ()
             ',event))))

(local (include-book "remove-guard-holders-lemmas"))

(verify-termination weak-apply$-badge-alistp) ; and guards

(verify-termination ilks-plist-worldp) ; and guards

(verify-termination ilks-per-argument-slot) ; and guards

(verify-termination-remove-guard-holders1) ; and guards

(verify-termination remove-guard-holders-weak) ; and guards
