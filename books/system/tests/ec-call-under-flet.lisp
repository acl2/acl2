; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun f (x)
  (declare (xargs :guard t))
  x)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; accepted in ACL2 8.7
(defun g ()
  (declare (xargs :verify-guards nil))
  (flet ((f (x) (cons x x)))
    (ec-call (f 3))))
)

; The remaining events were accepted in ACL2 8.7, but are now commented out,
; since the defun of g above is no longer admissible.

#|
(defthm lemma-1
  (equal (g) '(3 . 3))
  :rule-classes nil)

(verify-guards g)

(defthm lemma-2
  (equal (g) 3)
  :rule-classes nil)

(defthm contradiction
  nil
  :hints (("Goal"
           :in-theory (disable (:e g))
           :use (lemma-1 lemma-2)))
  :rule-classes nil)
|#
