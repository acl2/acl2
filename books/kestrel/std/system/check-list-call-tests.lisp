; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-list-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (check-list-call 'x))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(quote 4)))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(quote t)))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(quote nill)))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(quote nil)))
              '(t nil))

(assert-equal (mv-list 2 (check-list-call *nil*))
              '(t nil))

(assert-equal (mv-list 2 (check-list-call '(f x y z)))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(cons x y)))
              '(nil nil))

(assert-equal (mv-list 2 (check-list-call '(cons x 'nil)))
              '(t (x)))

(assert-equal (mv-list 2 (check-list-call '(cons x (cons y 'nil))))
              '(t (x y)))

(assert-equal (mv-list 2 (check-list-call '(cons x (cons y (cons z 'nil)))))
              '(t (x y z)))
