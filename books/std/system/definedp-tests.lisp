; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definedp")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (definedp 'not (w state)))

(assert! (not (definedp 'cons (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (definedp 'f (w state))))

(must-succeed*
 (defstub f (*) => *)
 (assert! (not (definedp 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm th (equal (f x) x)))
 (assert! (not (definedp 'f (w state)))))

(must-succeed*
 (defchoose f x (y) (equal x y))
 (assert! (not (definedp 'f (w state)))))
