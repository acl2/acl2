; Term Utilities -- Tests
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

(assert-event (equal (all-fns 'x) nil))

(assert-event (equal (all-fns ''3) nil))

(assert-event (equal (all-fns '(f x)) '(f)))

(assert-event (equal (all-fns '(f '"ab")) '(f)))

(assert-event (equal (all-fns '(f (g a) (h '4/5))) '(h g f)))

(assert-event (equal (all-fns '((lambda (x y) (f x y)) (g '1) (h x x)))
                     '(h g f)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (apply-unary-to-terms 'f '(x (g y) '2))
                     '((f x) (f (g y)) (f '2))))

(assert-event (equal (apply-unary-to-terms '(lambda (z) (cons z z))
                                           '(x (g y) '2))
                     '((cons x x) (cons (g y) (g y)) '(2 . 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (term-logicp '(len (cons x x)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert-event (not (term-logicp '(cons (f x) '3) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (lambda-expr-logicp '(lambda (x y) (len (cons x x))) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert-event
  (not (lambda-expr-logicp '(lambda (z) (cons (f x) '3)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (term-no-stobjs-p '(binary-+ x (cons y '#\a)) (w state)))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert-event (not (term-no-stobjs-p '(list (f state)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (lambda-expr-no-stobjs-p '(lambda (x y) (binary-+ x (cons y '#\a))) (w state)))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert-event
  (not (lambda-expr-no-stobjs-p '(lambda (state) (list (f state))) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (terms-fns-guard-verified-p '(cons (len a) '3) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-event (not (terms-fns-guard-verified-p '(zp (f '4)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (lambda-expr-fns-guard-verified-p '(lambda (a) (cons (len a) '3)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-event
  (not (lambda-expr-fns-guard-verified-p '(lambda (x) (zp (f '4)))
                                         (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (lambda-expr-p '(lambda (x y) (binary-+ x (len (cons '3 'nil)))) (w state)))

(assert-event (not (lambda-expr-p '(lambda (x) (fffff x)) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (mv-list 2 (check-user-term 3 (w state)))
                     '('3 (nil))))

(assert-event (equal (mv-list 2 (check-user-term 'x (w state)))
                     '(x (nil))))

(assert-event (equal (mv-list 2 (check-user-term '(len x) (w state)))
                     '((len x) (nil))))

(assert-event (equal (mv-list 2 (check-user-term '(mv x y z) (w state)))
                     '((cons x (cons y (cons z 'nil))) (nil nil nil))))

(assert-event (equal (mv-list 2 (check-user-term 'state (w state)))
                     '(state (state))))

(assert-event (equal (mv-list 2 (check-user-term '(mv state 1) (w state)))
                     '((cons state (cons '1 'nil)) (state nil))))

(must-succeed*
 (defstobj s)
 (assert-event (equal (mv-list 2 (check-user-term '(mv s 0 state) (w state)))
                      '((cons s (cons '0 (cons state 'nil))) (s nil state)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (mv-list 2 (check-user-term '(+ x y) (w state)))
               '((binary-+ x y) (nil)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (mv-list 2 (check-user-term '(+ (len x) 55) (w state)))
               '((binary-+ (len x) '55) (nil)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value
  (equal (mv-list 2 (check-user-term '(let ((x 4)) (+ x (len y))) (w state)))
         '(((lambda (x y) (binary-+ x (len y))) '4 y) (nil)))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-term '(f x) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       "(lambda (x) x)" (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x) x . more) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x) x y) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x)) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambdaa (x) x) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda "x" x) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x x) x) (w state))))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x "y") x) (w state))))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr '(lambda (x) 3) (w state)))
        '((lambda (x) '3) (nil))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr '(lambda (x) x) (w state)))
        '((lambda (x) x) (nil))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr '(lambda (y) (len x)) (w state)))
        '((lambda (y) (len x)) (nil))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr
                    '(lambda (x y) (mv x y z)) (w state)))
        '((lambda (x y) (cons x (cons y (cons z 'nil)))) (nil nil nil))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr '(lambda (state) state) (w state)))
        '((lambda (state) state) (state))))

(assert-event
 (equal (mv-list 2 (check-user-lambda-expr
                    '(lambda (state) (mv state 1)) (w state)))
        '((lambda (state) (cons state (cons '1 'nil))) (state nil))))

(must-succeed*
 (defstobj s)
 (assert-event (equal (mv-list 2 (check-user-lambda-expr
                                  '(lambda (state s) (mv s 0 state)) (w state)))
                      '((lambda (state s) (cons s (cons '0 (cons state 'nil))))
                        (s nil state)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (mv-list 2 (check-user-lambda-expr
                           '(lambda (x y) (+ x y)) (w state)))
               '((lambda (x y) (binary-+ x y)) (nil)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (mv-list 2 (check-user-lambda-expr
                           '(lambda (z) (+ (len x) 55)) (w state)))
               '((lambda (z) (binary-+ (len x) '55)) (nil)))))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (mv-list 2 (check-user-lambda-expr
                           '(lambda (u) (let ((x 4)) (+ x (len y)))) (w state)))
               '((lambda (u) ((lambda (x y) (binary-+ x (len y))) '4 y))
                 (nil)))))

(assert-event (msgp (nth 0 (mv-list 2 (check-user-lambda-expr
                                       '(lambda (x) (f x)) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (trans-macro 'list (w state))
               ''nil)))

(must-eval-to-t ; ASSERT-EVENT does not work here
 (value (equal (trans-macro 'make-list (w state))
               '(make-list-ac size 'nil 'nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (term-guard-obligation 'x state) ''t))

(assert-event (equal (term-guard-obligation '(binary-+ x '4) state)
                     '(acl2-numberp x)))
