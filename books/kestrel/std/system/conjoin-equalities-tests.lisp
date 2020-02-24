; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjoin-equalities")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (conjoin-equalities nil nil) *t*)

(assert-equal (conjoin-equalities (list 'lhs) (list 'rhs))
              '(equal lhs rhs))

(assert-equal (conjoin-equalities (list 'var
                                        '(quote #\c)
                                        '(f a b))
                                  (list '((lambda (x) (cons x x)) '2)
                                        'xb
                                        '(h (j '3) (k x y z))))
              '(if (equal var ((lambda (x) (cons x x)) '2))
                   (if (equal '#\c xb)
                       (equal (f a b) (h (j '3) (k x y z)))
                     'nil)
                 'nil))
