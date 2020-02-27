; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-mv-nth-calls")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (make-mv-nth-calls 'x 0) nil)

(assert-equal (make-mv-nth-calls '(quote 1) 0) nil)

(assert-equal (make-mv-nth-calls '(f a b) 0) nil)

(assert-equal (make-mv-nth-calls '((lambda (x) (cons x x)) y) 0) nil)

(assert-equal (make-mv-nth-calls 'x 4)
              `((mv-nth '0 x)
                (mv-nth '1 x)
                (mv-nth '2 x)
                (mv-nth '3 x)))

(assert-equal (make-mv-nth-calls '(quote 1) 4)
              `((mv-nth '0 '1)
                (mv-nth '1 '1)
                (mv-nth '2 '1)
                (mv-nth '3 '1)))

(assert-equal (make-mv-nth-calls '(f a b) 4)
              `((mv-nth '0 (f a b))
                (mv-nth '1 (f a b))
                (mv-nth '2 (f a b))
                (mv-nth '3 (f a b))))

(assert-equal (make-mv-nth-calls '((lambda (x) (cons x x)) y) 4)
              `((mv-nth '0 ((lambda (x) (cons x x)) y))
                (mv-nth '1 ((lambda (x) (cons x x)) y))
                (mv-nth '2 ((lambda (x) (cons x x)) y))
                (mv-nth '3 ((lambda (x) (cons x x)) y))))
