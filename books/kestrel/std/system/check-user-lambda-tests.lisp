; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-user-lambda")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/eval" :dir :system)

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
