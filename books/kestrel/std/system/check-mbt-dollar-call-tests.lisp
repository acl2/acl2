; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-mbt-dollar-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (check-mbt$-call 'x))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(quote 4)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(quote t)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(quote nill)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(f x y)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '((lambda (x) (cons x x)) a)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(return-last 'something 't x)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(return-last 'mbe1-raw 'tt x)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call '(return-last 'mbe1-raw 't x)))
              '(nil nil))

(assert-equal (mv-list 2 (check-mbt$-call
                          '(return-last 'mbe1-raw 't (if x 't 'nil))))
              '(t x))

(assert-equal (mv-list 2 (check-mbt$-call
                          '(return-last 'mbe1-raw 't (if (f x y) 't 'nil))))
              '(t (f x y)))
