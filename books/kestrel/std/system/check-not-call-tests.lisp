; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-not-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (check-not-call 'x))
              '(nil nil))

(assert-equal (mv-list 2 (check-not-call '(quote 7/5)))
              '(nil nil))

(assert-equal (mv-list 2 (check-not-call '((lambda (x y) (cons x y)) a b)))
              '(nil nil))

(assert-equal (mv-list 2 (check-not-call '(h a b)))
              '(nil nil))

(assert-equal (mv-list 2 (check-not-call '(not a)))
              '(t a))

(assert-equal (mv-list 2 (check-not-call '(not (not x))))
              '(t (not x)))
