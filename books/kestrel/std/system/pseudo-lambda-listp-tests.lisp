; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambda-listp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-lambda-listp nil))

(assert! (pseudo-lambda-listp (list '(lambda (x) x)
                                    '(lambda (x y z) (+ x x)))))

(assert! (not (pseudo-lambda-listp (list "abc" '(lambda (x) x)))))

(assert! (not (pseudo-lambda-listp (list* '(lambda (x) x)
                                          '(lambda (x y z) (+ x x))
                                          '(lambda (y) (cons y y))))))
