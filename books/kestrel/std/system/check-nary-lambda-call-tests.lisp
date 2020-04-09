; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-nary-lambda-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 4 (check-nary-lambda-call 'x 1))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call 'x 6))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '(quote 7/5) 3))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '(quote 7/5) 0))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '(h a b) 1))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '(h a b) 2))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call
                          '((lambda (x y) (cons x y)) a b) 2))
              '(t (x y) (cons x y) (a b)))

(assert-equal (mv-list 4 (check-nary-lambda-call
                          '((lambda (x y) (cons x y)) a b) 1))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '((lambda () '0)) 0))
              '(t () '0 ()))

(assert-equal (mv-list 4 (check-nary-lambda-call '((lambda () '0)) 3))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-nary-lambda-call '((lambda (u) u) uu) 1))
              '(t (u) u (uu)))

(assert-equal (mv-list 4 (check-nary-lambda-call '((lambda (u) u) uu) 2))
              '(nil nil nil nil))
