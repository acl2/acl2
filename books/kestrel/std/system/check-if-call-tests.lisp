; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-if-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 4 (check-if-call 'x))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '(quote 4)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '(quote t)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '(quote nill)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '(f x y)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '((lambda (x) (cons x x)) a)))
              '(nil nil nil nil))

(assert-equal (mv-list 4 (check-if-call '(if a b c)))
              '(t a b c))
