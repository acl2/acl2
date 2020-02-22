; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logic-function-namep")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (logic-function-namep 'len (w state)))

(assert! (not (logic-function-namep 'car-cdr-elim (w state))))

(assert! (not (logic-function-namep 'aaaaaaaaa (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (logic-function-namep 'f (w state))))

(assert! (not (logic-function-namep "len" (w state))))

(assert! (not (logic-function-namep 'error1 (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert! (not (logic-function-namep 'f (w state)))))
