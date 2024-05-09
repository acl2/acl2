; The definition of lookup-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See lookup-equal.lisp for theorems.

;; Look up KEY in ALIST, using equal as the test, returning the value to which
;; KEY is bound, or nil if KEY is not bound.
(defund lookup-equal (key alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal key alist)))
