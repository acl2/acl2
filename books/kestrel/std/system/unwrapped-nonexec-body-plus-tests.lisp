; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unwrapped-nonexec-body-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-nx f (x) (cons (list x) (list x)))
 (assert-equal (ubody 'f (w state))
               '(return-last 'progn
                             (throw-nonexec-error 'f (cons x 'nil))
                             (cons (cons x 'nil) (cons x 'nil))))
 (assert-equal (unwrapped-nonexec-body+ 'f (w state))
               '(cons (cons x 'nil) (cons x 'nil))))
