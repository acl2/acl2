; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is similar to basic-pkg.lisp, but with :check-expansion t (just as
; basic-check.lisp is related to basic.lisp).

(in-package "FOO")

(make-event
 '(defun test1 (x)
    (list x x))
 :check-expansion t)

(make-event
 (value '(defun test2 (x)
           (cons x x)))
 :check-expansion t)

(defun bar (x)
  (cons (test1 x) (test2 x)))

(defthm bar-prop
  (equal (bar x)
         (cons (list x x)
               (cons x x))))
