; Terms -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the term manipulation utilities in terms.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "terms")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (legal-variable-listp nil))

(assert-event (legal-variable-listp '(x y z)))

(assert-event (not (legal-variable-listp '(t a))))

(assert-event (not (legal-variable-listp '(*c*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (not (pseudo-lambda-expr-p "abc")))

(assert-event (not (pseudo-lambda-expr-p (cons 3 6))))

(assert-event (not (pseudo-lambda-expr-p '(lambda (x) x extra))))

(assert-event (not (pseudo-lambda-expr-p '(lambd (x) x))))

(assert-event (not (pseudo-lambda-expr-p '(lambda (x 8) x))))

(assert-event (not (pseudo-lambda-expr-p '(lambda (x y) #\a))))

(assert-event (pseudo-lambda-expr-p '(lambda (x) x)))

(assert-event (pseudo-lambda-expr-p '(lambda (x y z) (+ x (* y z)))))

(assert-event (pseudo-lambda-expr-p '(lambda (x y z) (+ x x))))

(assert-event (pseudo-lambda-expr-p '(lambda (x y z) (+ a b))))

(must-succeed*
 (defconst *term* '((lambda (x) (1+ x)) y))
 (assert-event (pseudo-termp *term*))
 (assert-event (pseudo-lambda-expr-p (ffn-symb *term*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (lambda-expr-closedp '(lambda (x) (* '2 x))))

(assert-event (lambda-expr-closedp '(lambda (x y) (- y x))))

(assert-event (not (lambda-expr-closedp '(lambda (x) (cons x a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (pseudo-functionp 'f))

(assert-event (pseudo-functionp '(lambda (x) x)))

(assert-event (not (pseudo-functionp 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (apply-term 'f '('4 y)) '(f '4 y)))

(assert-event (equal (apply-term '(lambda (x y) (* (1+ x) (1- y))) '(a b))
                     '(* (1+ a) (1- b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (apply-term* 'f ''4 'y) '(f '4 y)))

(assert-event (equal (apply-term* '(lambda (x y) (* (1+ x) (1- y))) 'a 'b)
                     '(* (1+ a) (1- b))))
