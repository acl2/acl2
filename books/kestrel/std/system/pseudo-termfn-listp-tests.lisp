; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-termfn-listp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-termfn-listp nil))

(assert! (pseudo-termfn-listp (list '(lambda (x) x)
                                    'fn
                                    '(lambda (x y z) (+ x x)))))

(assert! (pseudo-termfn-listp (list 'a 'b)))

(assert! (not (pseudo-termfn-listp (list "abc" '(lambda (x) x)))))

(assert! (not (pseudo-termfn-listp (list "abc" 'g))))

(assert! (not (pseudo-termfn-listp (list* '(lambda (x) x)
                                          '(lambda (x y z) (+ x x))
                                          '(lambda (y) (cons y y))))))
