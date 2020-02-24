; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-exec-fnsp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-exec-fnsp 'x (w state)))

(assert! (guard-verified-exec-fnsp '(quote 4) (w state)))

(assert! (guard-verified-exec-fnsp '(cons x y) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert! (not (guard-verified-exec-fnsp '(cons (f x) (g (f y))) (w state)))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert! (not (guard-verified-exec-fnsp '(cons (mycar z) (len y)) (w state))))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert! (guard-verified-exec-fnsp (body 'f nil (w state)) (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) (cons (ec-call (f x)) (len x)))
 (assert! (guard-verified-exec-fnsp (body 'g nil (w state)) (w state))))
