; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

; Recognize tests-and-calls records (defrec tests-and-calls (tests . calls) nil)
; where each of the two fields is a list of terms.
; These records are built into ACL2.

(defun pseudo-tests-and-callsp (x)
  (declare (xargs :guard t))
  (case-match x
    (('TESTS-AND-CALLS tests . calls)
     (and (pseudo-term-listp tests)
          (pseudo-term-listp calls)))
    (& nil)))
