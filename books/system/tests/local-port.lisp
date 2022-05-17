; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Small test of local portcullis events.

; Porcullis commands:
; (defun f1 (x) x)
; (local (defun f2 (x) x))
; (defun f3 (x) x)

(in-package "ACL2")

(defun g (x)
  (cons (f1 x) (f3 x)))

(value-triple (equal (g 3) '(3 . 3))
              :on-skip-proofs t)
