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

(assert! (lambda-closedp '(lambda (x) (* '2 x))))

(assert! (lambda-closedp '(lambda (x y) (- y x))))

(assert! (not (lambda-closedp '(lambda (x) (cons x a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-fn/lambda-p 'f))

(assert! (pseudo-fn/lambda-p '(lambda (x) x)))

(assert! (not (pseudo-fn/lambda-p 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-term 'f '('4 y))
              '(f '4 y))

(assert-equal (apply-term '(lambda (x y) (* (1+ x) (1- y))) '(a b))
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-term* 'f ''4 'y)
              '(f '4 y))

(assert-equal (apply-term* '(lambda (x y) (* (1+ x) (1- y))) 'a 'b)
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-unary-to-terms 'f '(x (g y) '2))
              '((f x) (f (g y)) (f '2)))

(assert-equal (apply-unary-to-terms '(lambda (z) (cons z z))
                                    '(x (g y) '2))
              '((cons x x) (cons (g y) (g y)) '(2 . 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-program-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(cons x y) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :logic)) x)
 (assert!
  (set-equiv (all-program-ffn-symbs '(cons (f x) (g (f y))) nil (w state))
             '(f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-logic-fnsp '(lambda (x y) (len (cons x x))) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert! (not (lambda-logic-fnsp '(lambda (z) (cons (f x) '3)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (term-no-stobjs-p '(binary-+ x (cons y '#\a)) (w state)))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert! (not (term-no-stobjs-p '(list (f state)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert!
 (lambda-no-stobjs-p '(lambda (x y) (binary-+ x (cons y '#\a))) (w state)))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert!
  (not (lambda-no-stobjs-p '(lambda (state) (list (f state))) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-fnsp '(cons (len a) '3) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert! (not (guard-verified-fns-listp '(zp (f '4)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-non-gv-exec-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(cons x y) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert!
  (set-equiv (all-non-gv-exec-ffn-symbs '(cons (f x) (g (f y))) nil (w state))
             '(f))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert!
  (set-equiv (all-non-gv-exec-ffn-symbs '(cons (mycar z) (len y)) nil (w state))
             '(mycar)))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert-equal (all-non-gv-exec-ffn-symbs (body 'f nil (w state)) nil (w state))
               nil))

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

(assert! (not (lambdap '(lambda (x) (fffff x)) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-guard-verified-fnsp '(lambda (a) (cons (len a) '3)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert!
  (not (lambda-guard-verified-fnsp '(lambda (x) (zp (f '4))) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (check-user-term 3 (w state)))
              '('3 (nil)))

(assert-equal (mv-list 2 (check-user-term 'x (w state)))
              '(x (nil)))

(assert-equal (mv-list 2 (check-user-term '(len x) (w state)))
              '((len x) (nil)))

(assert-equal (mv-list 2 (check-user-term '(mv x y z) (w state)))
              '((cons x (cons y (cons z 'nil))) (nil nil nil)))

(assert-equal (mv-list 2 (check-user-term 'state (w state)))
              '(state (state)))

(assert-equal (mv-list 2 (check-user-term '(mv state 1) (w state)))
              '((cons state (cons '1 'nil)) (state nil)))

(must-succeed*
 (defstobj s)
 (assert-equal (mv-list 2 (check-user-term '(mv s 0 state) (w state)))
               '((cons s (cons '0 (cons state 'nil))) (s nil state))))

(assert-equal (mv-list 2 (check-user-term '(+ x y) (w state)))
              '((binary-+ x y) (nil)))

(assert-equal (mv-list 2 (check-user-term '(+ (len x) 55) (w state)))
              '((binary-+ (len x) '55) (nil)))

(assert-equal
 (mv-list 2 (check-user-term '(let ((x 4)) (+ x (len y))) (w state)))
 '(((lambda (x y) (binary-+ x (len y))) '4 y) (nil)))

(assert! (msgp (nth 0 (mv-list 2 (check-user-term '(f x) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  "(lambda (x) x)" (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) x . more) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) x y) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x)) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambdaa (x) x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda "x" x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x x) x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x "y") x) (w state))))))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x) 3) (w state)))
              '((lambda (x) '3) (nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x) x) (w state)))
              '((lambda (x) x) (nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (y) (len x)) (w state)))
              '((lambda (y) (len x)) (nil)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (x y) (mv x y z)) (w state)))
 '((lambda (x y) (cons x (cons y (cons z 'nil)))) (nil nil nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (state) state) (w state)))
              '((lambda (state) state) (state)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (state) (mv state 1)) (w state)))
 '((lambda (state) (cons state (cons '1 'nil))) (state nil)))

(must-succeed*
 (defstobj s)
 (assert-equal (mv-list 2 (check-user-lambda
                           '(lambda (state s) (mv s 0 state)) (w state)))
               '((lambda (state s) (cons s (cons '0 (cons state 'nil))))
                 (s nil state))))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x y) (+ x y)) (w state)))
              '((lambda (x y) (binary-+ x y)) (nil)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (z) (+ (len x) 55)) (w state)))
 '((lambda (z) (binary-+ (len x) '55)) (nil)))

(assert-equal (mv-list 2 (check-user-lambda
                          '(lambda (u) (let ((x 4)) (+ x (len y)))) (w state)))
              '((lambda (u) ((lambda (x y) (binary-+ x (len y))) '4 y))
                (nil)))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) (f x)) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (trans-macro 'list (w state))
              ''nil)

(assert-equal (trans-macro 'make-list (w state))
              '(make-list-ac size 'nil 'nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (term-guard-obligation 'x state)
              ''t)

(assert-equal (term-guard-obligation '(binary-+ x '4) state)
              '(acl2-numberp x))
