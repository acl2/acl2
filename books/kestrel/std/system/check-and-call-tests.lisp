; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-and-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 3 (check-and-call 'x))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(quote 4)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(quote t)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(quote nill)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(f x y)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '((lambda (x) (cons x x)) a)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(if a 'nil b)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-and-call '(if a b 'nil)))
              '(t a b))

(assert-equal (mv-list 3 (check-and-call '(if (if a b c) d 'nil)))
              '(t (if a b c) d))
