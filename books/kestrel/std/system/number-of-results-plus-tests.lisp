; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "number-of-results-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (number-of-results+ 'cons (w state)) 1)

(assert-equal (number-of-results+ 'len (w state)) 1)

(must-succeed*
 (defun f (x) (mv x (list x)))
 (assert-equal (number-of-results+ 'f (w state)) 2))

(must-succeed*
 (defun f (x) (mv x (list x) (list x x)))
 (assert-equal (number-of-results+ 'f (w state)) 3))
