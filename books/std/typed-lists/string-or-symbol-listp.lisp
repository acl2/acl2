; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defsection string-or-symbol-listp
  :parents (std/typed-lists)
  :short "Recognize true lists of strings and symbols."

  (defun string-or-symbol-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (null x)
      (and (or (stringp (car x))
               (symbolp (car x)))
           (string-or-symbol-listp (cdr x))))))
