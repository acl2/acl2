; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-user-term")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/eval" :dir :system)

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
