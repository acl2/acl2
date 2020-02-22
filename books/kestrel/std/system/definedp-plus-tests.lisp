; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definedp-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (definedp+ 'not (w state)))

(assert! (not (definedp+ 'cons (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (definedp+ 'f (w state))))

(must-succeed*
 (defstub f (*) => *)
 (assert! (not (definedp+ 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm th (equal (f x) x)))
 (assert! (not (definedp+ 'f (w state)))))

(must-succeed*
 (defchoose f x (y) (equal x y))
 (assert! (not (definedp+ 'f (w state)))))
