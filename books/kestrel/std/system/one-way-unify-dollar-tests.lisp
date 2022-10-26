; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "one-way-unify-dollar")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (one-way-unify$ 'x ''3 state))
              (list t (list (cons 'x ''3))))

(assert-equal (mv-list 2 (one-way-unify$ ''3 'x state))
              (list nil nil))

(assert-equal (mv-list 2 (one-way-unify$ '(f x '3) '(f '1 '3) state))
              (list t (list (cons 'x ''1))))
