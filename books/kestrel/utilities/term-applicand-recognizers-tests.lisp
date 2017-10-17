; Term Applicand Recognizers -- Tests
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "term-applicand-recognizers")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (pseudo-lambdap "abc")))

(assert! (not (pseudo-lambdap (cons 3 6))))

(assert! (not (pseudo-lambdap '(lambda (x) x extra))))

(assert! (not (pseudo-lambdap '(lambd (x) x))))

(assert! (not (pseudo-lambdap '(lambda (x 8) x))))

(assert! (not (pseudo-lambdap '(lambda (x y) #\a))))

(assert! (pseudo-lambdap '(lambda (x) x)))

(assert! (pseudo-lambdap '(lambda (x y z) (+ x (* y z)))))

(assert! (pseudo-lambdap '(lambda (x y z) (+ x x))))

(assert! (pseudo-lambdap '(lambda (x y z) (+ a b))))

(must-succeed*
 (defconst *term* '((lambda (x) (1+ x)) y))
 (assert! (pseudo-termp *term*))
 (assert! (pseudo-lambdap (ffn-symb *term*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-fn/lambda-p 'f))

(assert! (pseudo-fn/lambda-p '(lambda (x) x)))

(assert! (not (pseudo-fn/lambda-p 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambdap '(lambda (x y) (binary-+ x (len (cons '3 'nil)))) (w state)))

(assert! (not (lambdap '(lambda (x) (fffff x)) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (fn/lambda-p "cons" (w state))))

(assert! (not (fn/lambda-p 'fffffffff (w state))))

(assert! (fn/lambda-p 'cons (w state)))

(assert! (fn/lambda-p 'len (w state)))

(assert! (not (fn/lambda-p 'car-cdr-elim (w state))))

(must-succeed*
 (defun h (x) x)
 (assert! (fn/lambda-p 'h (w state))))

(assert!
 (fn/lambda-p '(lambda (x y) (binary-+ x (len (cons '3 'nil)))) (w state)))

(assert! (not (fn/lambda-p '(lambda (x) (fffff x)) (w state))))
