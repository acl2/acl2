; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-executablep-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (non-executablep+ 'not (w state))))

(assert! (not (non-executablep+ 'len (w state))))

(must-succeed*
 (defun-nx f (x) x)
 (assert! (non-executablep+ 'f (w state))))

(must-succeed*
 (defun-sk g (x) (forall (y z) (equal x (cons y z))))
 (assert! (non-executablep+ 'g (w state))))

(must-succeed*
 (defun-sk h (x y) (exists z (equal z (cons x y)))
   :witness-dcls ((declare (xargs :non-executable nil))))
 (assert! (not (non-executablep+ 'h (w state)))))
