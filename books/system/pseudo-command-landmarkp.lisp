; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "pseudo-command-formp")

(defsection pseudo-command-landmarkp
  :parents (system-utilities-non-built-in)
  :short "Recognize command landmarks in the ACL2 @(see world)."
  :long
  "<p>Warning: Keep this in sync with
      @('(defrec command-tuple ...)') in the ACL2 sources.</p>"

  (defun pseudo-command-landmarkp (val)
    (declare (xargs :guard t))
    (and (consp val)
         (or (eql (car val) -1) (natp (car val)))
         (consp (cdr val))
         (consp (cadr val))
         (if (keywordp (car (cadr val)))
             (and (eq (car (cadr val)) :logic)
                  (pseudo-command-formp (cdr (cadr val))))
           (pseudo-command-formp (cadr val)))
         (consp (cddr val))
         (or (null (caddr val))
             (stringp (caddr val)))
         (or (null (cdddr val))
             (pseudo-command-formp (cdddr val))))))
