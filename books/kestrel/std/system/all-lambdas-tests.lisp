; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-lambdas")

(include-book "std/testing/assert-equal" :dir :system) ; includes ASSERT!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro same-member-equal (x y)
  `(let ((x ,x) (y ,y))
     (and (subsetp-equal x y)
          (subsetp-equal y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-lambdas 'x nil) nil)

(assert-equal (all-lambdas '(quote #\x) nil) nil)

(assert-equal (all-lambdas '(f a b) nil) nil)

(assert-equal (all-lambdas '((lambda (u) (cons u u)) (g '3)) nil)
              '((lambda (u) (cons u u))))

(assert! (same-member-equal (all-lambdas '((lambda (x y) (+ x y))
                                           (h a b c)
                                           ((lambda (y) y) z))
                                         nil)
                            '((lambda (x y) (+ x y))
                              (lambda (y) y))))

(assert! (same-member-equal (all-lambdas '(f ((lambda (q) y) '3/4)
                                             (len ((lambda (a b) (+ a b))
                                                   aaa
                                                   bbb)))
                                         nil)
                            '((lambda (q) y)
                              (lambda (a b) (+ a b)))))
