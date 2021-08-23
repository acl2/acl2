; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-fn-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 3 (check-fn-call 'x))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-fn-call '(quote 7/5)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-fn-call '((lambda (x y) (cons x y)) a b)))
              '(nil nil nil))

(assert-equal (mv-list 3 (check-fn-call '(h a b)))
              '(t h (a b)))

(assert-equal (mv-list 3 (check-fn-call '(nullary)))
              '(t nullary nil))
