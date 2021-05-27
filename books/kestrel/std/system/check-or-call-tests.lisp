; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-or-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 3 (check-or-call 'x))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(quote 4)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(quote t)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(quote nill)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(f x y)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '((lambda (x) (cons x x)) a)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(if a 'nil b)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(if a b 'nil)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-or-call '(if a a b)))
              '(t a b))

(assert-equal (mv-list 3 (check-or-call '(if a a (if b c d))))
              '(t a (if b c d)))
