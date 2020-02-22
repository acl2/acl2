; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "close-lambdas")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (close-lambdas 'x) 'x)

(assert-equal (close-lambdas '(quote #\+)) '(quote #\+))

(assert-equal (close-lambdas '(g a b)) '(g a b))

(assert-equal (close-lambdas
               '((lambda (x y) (cons x y)) a y))
              '((lambda (x y) (cons x y)) a y))

(assert-equal (close-lambdas
               '((lambda (x) (cons x y)) (f a)))
              '((lambda (x y) (cons x y)) (f a) y))

(assert-equal (close-lambdas
               '((lambda (x y z) (cons y y)) u v w))
              '((lambda (x y z) (cons y y)) u v w))
