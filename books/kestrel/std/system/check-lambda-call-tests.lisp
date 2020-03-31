; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-lambda-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 4 (check-lambda-call 'x))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-lambda-call '(quote 7/5)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-lambda-call '(h a b)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-lambda-call '((lambda (x y) (cons x y)) a b)))
              '(t (x y) (cons x y) (a b)))

(assert-equal (mv-list 4 (check-lambda-call '((lambda () '0))))
              '(t () '0 ()))

(assert-equal (mv-list 4 (check-lambda-call '((lambda (u) u) uu)))
              '(t (u) u (uu)))
