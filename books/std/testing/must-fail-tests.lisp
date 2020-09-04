; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-fail")

(include-book "must-succeed-star")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y))))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y))))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y))))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 :with-output-off nil
 :check-expansion t)

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 :with-output-off (summary))

(must-succeed*
 (defun f (x) x)
 (must-fail (defun f (x) (cons x x)))
 (defun g (x y) (f (cons x y)))
 :check-expansion t)
