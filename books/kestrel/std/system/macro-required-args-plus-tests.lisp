; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-required-args-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (macro-required-args+ 'tthm (w state)) '(fn))

(assert-equal (macro-required-args+ 'list (w state)) nil)

(assert-equal (macro-required-args+ 'defun (w state)) nil)

(assert-equal (macro-required-args+ 'defthm (w state)) '(name term))

(assert-equal (macro-required-args+ 'defun-sk (w state)) '(name args))

(must-succeed*
 (defmacro m (a) `(list ,a))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))

(must-succeed*
 (defmacro m (a &key b) `(list ,a ,(or b :default)))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))

(must-succeed*
 (defmacro m (&whole form a &optional b &key c (d '3) (e '#\e e-p))
   `(list ,a ,b ,c ,d ,e ,e-p ,form))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))
