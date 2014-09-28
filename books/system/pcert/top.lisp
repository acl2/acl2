; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(progn (make-event '(make-event '(defun r1 (x) x)))
       (defun r2 (x) x))

(include-book "mid")

; Check for fix in late 9/2014 for pcert bug.

(defun f1 (x) x)

(verify-guards+ f1)
