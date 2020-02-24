; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "function-namep")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (function-namep 'len (w state)))

(assert! (not (function-namep 'cons-car-cdr (w state))))

(assert! (not (function-namep 'bbbbbbbbbbb (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (function-namep 'f (w state))))

(assert! (not (function-namep 33 (w state))))

(assert! (not (function-namep "len" (w state))))
