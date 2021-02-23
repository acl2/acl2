; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is like hons-acons-bang.lisp except that there's a local event first.
; The present book even failed certification before mid-February 2021, with the
; error, "Fast alist stolen by HONS-ACONS!.".

; The solution is to avoid the stolen-alist error during include-book.  That
; seems reasonable because stolen-alist check is sort of a heads-up; the actual
; problem would presamably be with subsequent slow hons-get, which would be
; signaled then.

; Below, "habl" comes from the filename.

(in-package "ACL2")
(local (defun habl-fn (x) x))
(defconst *habl* (hons-acons! 1 2 nil))
