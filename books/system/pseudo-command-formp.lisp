; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

; Recognize command forms.

(defun pseudo-command-formp (x)

; We see no reasonable way to restrict the form of a command, other than to
; insist that it is a true list.

  (declare (xargs :guard t))
  (true-listp x))
