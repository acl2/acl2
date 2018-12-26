; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book (and its included sub-book, sub.lisp) illustrates a potential
; problem with verify-termination.  We reference this book in ACL2 source
; function verify-termination1.

; To see the problem, which was fixed in December, 2018, try the following
; certification using an earlier ACL2 version.

; (certify-book "sub")
; :u
; (certify-book "top")

; What happened before the change?  The make-event expansion for the
; verify-termination form below during the first pass of (certify-book "top")
; was (VALUE-TRIPLE :REDUNDANT), which left foo in :program mode during pass 2
; of certification of "top.lisp".  That caused the (:logic mode) definition of
; bar below to fail.

; After the change, that make-event expansion was a defun form.  In general
; such a generated defun may be redundant, and that's fine.  But now that we
; push redundancy checking to that generated defun, the verify-termination form
; below is no longer redundant, because the generated defun is not redundant.
; That defun puts foo into :logic mode, which allows the definition of bar to
; succeed.

(in-package "ACL2")

(local (include-book "sub"))

(defun foo (x)
  (declare (xargs :mode :program))
  x)

(verify-termination foo)

(defun bar (x)
  (foo x))
