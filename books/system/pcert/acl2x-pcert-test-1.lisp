; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(make-event '(defun f (x) x))

(encapsulate
 ()
 (local (make-event '(defun g (x) x)))
 (defun h (x) x))
