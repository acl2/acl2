; System Utilities -- Term Utilities -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "terms")
(include-book "kestrel/utilities/testing" :dir :system)

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

(assert-equal (term-guard-obligation 'x state)
              ''t)

(assert-equal (term-guard-obligation '(binary-+ x '4) state)
              '(acl2-numberp x))
