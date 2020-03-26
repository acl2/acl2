; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-non-gv-ffn-symbs")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-non-gv-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-non-gv-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-non-gv-ffn-symbs '(cons (len a) '3) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-equal (all-non-gv-ffn-symbs '(zp (f '4)) nil (w state)) '(f)))
