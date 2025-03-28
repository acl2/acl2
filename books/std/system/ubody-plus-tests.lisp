; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubody-plus")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubody+ 'atom (w state)) '(not (consp x)))

(must-succeed*
 (defun f (x) x)
 (assert-equal (ubody+ 'f (w state)) 'x))

(must-succeed*
 (defun p (x) (and (natp x) (natp 3)))
 (assert-equal (body 'p t (w state)) '(natp x))
 (assert-equal (ubody+ 'p (w state)) '(if (natp x) (natp '3) 'nil)))

(assert-equal (ubody+ '(lambda (x y) (cons x (h '3))) (w state))
              '(cons x (h '3)))

(assert-equal (ubody+ '(lambda (a) (h a '"abc")) (w state))
              '(h a '"abc"))
