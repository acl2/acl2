; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "stobjs-in-plus")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (stobjs-in+ 'cons (w state)) '(nil nil))

(assert-equal (stobjs-in+ 'fmt (w state)) '(nil nil nil state nil))

(must-succeed*
 (defstobj s)
 (defun f (x s state)
   (declare (ignore x s state) (xargs :stobjs (s state)))
   nil)
 (assert-equal (stobjs-in+ 'f (w state)) '(nil s state)))
