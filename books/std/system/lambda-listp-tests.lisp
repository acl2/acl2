; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lambda-listp")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-listp nil (w state)))

(assert! (lambda-listp (list '(lambda (x) x)
                             '(lambda (x y z) (binary-+ x x)))
                       (w state)))

(assert! (not (lambda-listp (list "abc" '(lambda (x) x)) (w state))))

(assert! (not (lambda-listp (list '(lambda (x) (- x))) (w state))))

(assert! (not (lambda-listp (list* '(lambda (x) (unary-- x))
                                   '(lambda (y) (cons y y)))
                            (w state))))
