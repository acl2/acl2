; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "pseudo-tests-and-callsp")

(defsection pseudo-tests-and-calls-listp
  :parents (system-utilities-non-built-in)
  :short "Recognize true lists of well-formed @('tests-and-calls') records."

  (defun pseudo-tests-and-calls-listp (x)
    (declare (xargs :guard t))
    (cond ((atom x) (null x))
          (t (and (pseudo-tests-and-callsp (car x))
                  (pseudo-tests-and-calls-listp (cdr x)))))))
