; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "irecursivep-plus")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (irecursivep+ 'cons (w state)) nil)

(assert-equal (irecursivep+ 'len (w state)) '(len))

(assert-equal (irecursivep+ 'pseudo-termp (w state))
              '(pseudo-termp pseudo-term-listp))

(must-succeed*
 (defun f (x) (if (consp x) (f (car x)) 0))
 (assert-equal (irecursivep+ 'f (w state)) '(f)))
