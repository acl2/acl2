; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See :DOC partial-encapsulate.

(in-package "ACL2")

; The following book sets everything up without requiring a trust tag.  It
; introduces a constrained function, ln-constrained, and a wrapper for it, ln.
; These are intended to represent a rational approximation to the natural log
; function.
(include-book "partial-encapsulate-support")

; Now we install raw Lisp code for the constrained function, ln-constrained.
; This makes the function ln executable.  Note that the invocation of
; install-ln introduces a trust tag.
(install-ln)

; This little test shows that we can execute ln, even during proofs.  Thus, we
; have extended the constraints for ln-constrained using our raw Lisp
; definition; one of those constrains is the equality below.
(defthm test-ln
  (equal (ln 3)
         10986123/10000000)
  :rule-classes nil)
