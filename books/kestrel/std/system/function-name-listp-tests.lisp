; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "function-name-listp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (function-name-listp nil (w state)))

(assert! (function-name-listp '(len cons atom) (w state)))

(assert! (not (function-name-listp '(len cons aaaaatom) (w state))))

(must-succeed*
 (defun f (x) x)
 (defun g (x) x)
 (assert! (function-name-listp '(f g g) (w state))))

(assert! (not (function-name-listp 33 (w state))))

(assert! (not (function-name-listp '(1 2 3) (w state))))

(assert! (not (function-name-listp "ab" (w state))))
