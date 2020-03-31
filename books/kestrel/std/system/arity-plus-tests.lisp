; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arity-plus")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (arity+ 'len (w state)) 1)

(must-succeed*
 (defun f (x y zz aaa b77) (list x y zz aaa b77))
 (assert-equal (arity+ 'f (w state)) 5))

(assert-equal (arity+ '(lambda (x y) (binary-+ x y)) (w state))
              2)

(assert-equal (arity+ '(lambda () '33) (w state))
              0)
