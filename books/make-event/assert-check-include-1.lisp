; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (Comment from Matt K. August 2011: I no longer know what this test is
; intended to accomplish, and the comment on the next line looks misguided.)
; Here we make sure that we can include assert-check.

(in-package "ACL2")

; Portcullis command:
; (include-book "eval")

(must-fail
 (include-book "assert-check"))

; Check that inclusion of assert-check did not make it to the end.
(must-fail
 (make-event
  '(value-triple (assert-check-end 3))))
