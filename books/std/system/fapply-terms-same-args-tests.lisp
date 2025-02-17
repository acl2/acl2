; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fapply-terms-same-args")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fapply-terms-same-args '(f
                                        g
                                        (lambda (x) (cons x x)))
                                      '(a))
              '((f a)
                (g a)
                (cons a a)))

(assert-equal (fapply-terms-same-args '((lambda (x y) (* (1+ x) (1- y)))
                                        hh)
                                      '(a b))
              '((* (1+ a) (1- b))
                (hh a b)))
