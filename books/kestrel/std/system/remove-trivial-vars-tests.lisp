; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-trivial-vars")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-trivial-vars 'x) 'x)

(assert-equal (remove-trivial-vars '(quote "abc")) '(quote "abc"))

(assert-equal (remove-trivial-vars '(f x y z)) '(f x y z))

(assert-equal (remove-trivial-vars '((lambda (x) x) (f u)))
              '((lambda (x) x) (f u)))

(assert-equal (remove-trivial-vars
               '((lambda (x y) (cons x y)) (f u) y))
              '((lambda (x) (cons x y)) (f u)))

(assert-equal (remove-trivial-vars
               '((lambda (x y) (cons x y)) x (g v)))
              '((lambda (y) (cons x y)) (g v)))

(assert-equal (remove-trivial-vars
               '((lambda (x y) (cons x y)) (f u) (g v)))
              '((lambda (x y) (cons x y)) (f u) (g v)))

(assert-equal (remove-trivial-vars
               '((lambda (x y) (cons x y))
                 ((lambda (u v w) (binary-+ u (binary-* v w)))
                  u (f '3) w)
                 y))
              '((lambda (x) (cons x y))
                ((lambda (v) (binary-+ u (binary-* v w)))
                 (f '3))))

(assert-equal (remove-trivial-vars
               '((lambda (x y) ((lambda (a b) (cons a b))
                                a
                                (f '0)))
                 x
                 (g '3/4)))
              '((lambda (y) ((lambda (b) (cons a b))
                             (f '0)))
                (g '3/4)))
