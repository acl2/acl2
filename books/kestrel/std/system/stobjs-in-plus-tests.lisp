; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "stobjs-in-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (stobjs-in+ 'cons (w state)) '(nil nil))

(assert-equal (stobjs-in+ 'fmt (w state)) '(nil nil nil state nil))

(must-succeed*
 (defstobj s)
 (defun f (x s state)
   (declare (ignore x s state) (xargs :stobjs (s state)))
   nil)
 (assert-equal (stobjs-in+ 'f (w state)) '(nil s state)))
