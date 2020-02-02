; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Not sure about making this a test, but a useful thing is to trace
; get-translate-cert-data-record and see that it gets everything expected.

(in-package "ACL2")

(encapsulate
  ((f-encap (x) t))
  (local (defun f-encap (x) (cons x x)))
  (defun h-encap (x) (car x))
  (defthm consp-f-encap
    (consp (f-encap x))))

(encapsulate
  ()
  (defun g-encap (x) (cons x x))
  (defthm consp-g-encap
    (consp (g-encap x))))
