; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-program-ffn-symbs")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-program-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(cons x y) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :logic)) x)
 (assert-equal (all-program-ffn-symbs '(cons (f x) (g (f y))) nil (w state))
               '(f)))
