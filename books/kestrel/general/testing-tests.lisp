; Testing Facilities -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the macros in testing.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 (must-fail$ (defthm th (natp (1+ x)))))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 (must-fail$ (defthm th (natp (1+ x))) :with-output-off nil))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 (must-fail$ (defthm th (natp (1+ x)))
             :with-output-off (summary)
             :check-expansion t))

(must-succeed**
 nil ; :with-output-off
 t ; :check-expansion
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 (must-fail$ (defthm th (natp (1+ x)))))

(must-succeed**
 (summary) ; :with-output-off
 nil ; :check-expansion
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 (must-fail$ (defthm th (natp (1+ x)))))

(must-succeed*
 (defun f (x) x)
 (must-be-redundant (defun f (x) x))
 (defthm th (acl2-numberp (+ x y)))
 (must-be-redundant (defthm th (acl2-numberp (+ x y)))))
