; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-unused-vars")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-unused-vars 'var) 'var)

(assert-equal (remove-unused-vars '(quote 3/4)) '(quote 3/4))

(assert-equal (remove-unused-vars '(f x y)) '(f x y))

(assert-equal (remove-unused-vars '((lambda (x) x) y))
              '((lambda (x) x) y))

(assert-equal (remove-unused-vars
               '((lambda (x y) (cons x x)) (1st a b) (2nd c d)))
              '((lambda (x) (cons x x)) (1st a b)))

(assert-equal (remove-unused-vars
               '((lambda (x y z) (f)) '1 '2 '3))
              '(f))

(assert-equal (remove-unused-vars
               '(f x ((lambda (y z) z) '1 '2)))
              '(f x ((lambda (z) z) '2)))
