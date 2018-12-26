; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun foo (x)
  (declare (xargs :mode :program))
  x)

(verify-termination foo)
