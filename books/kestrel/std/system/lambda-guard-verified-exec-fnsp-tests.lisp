; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambda-guard-verified-exec-fnsp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-guard-verified-exec-fnsp '(lambda (x) x) (w state)))

(assert! (lambda-guard-verified-exec-fnsp '(lambda (tt) '4) (w state)))

(assert! (lambda-guard-verified-exec-fnsp '(lambda (x y) (cons x y)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert! (not (lambda-guard-verified-exec-fnsp
                '(lambda (x y) (cons (f x) (g (f y)))) (w state)))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert! (not (lambda-guard-verified-exec-fnsp
                '(lambda (x y z) (cons (mycar z) (len y))) (w state))))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert! (lambda-guard-verified-exec-fnsp
           (make-lambda '(x) (body 'f nil (w state))) (w state))))
