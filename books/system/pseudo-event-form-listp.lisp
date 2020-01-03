; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "pseudo-event-formp")

; Here we recognize true lists of event forms.  See pseudo-event-form.lisp.

(defun pseudo-event-form-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (pseudo-event-formp (car x))
         (pseudo-event-form-listp (cdr x)))))
