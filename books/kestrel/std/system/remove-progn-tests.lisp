; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-progn")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-progn 'x) 'x)

(assert-equal (remove-progn '(quote #c(1 2))) '(quote #c(1 2)))

(assert-equal (remove-progn '(f a b)) '(f a b))

(assert-equal (remove-progn '((lambda (x) (cons x x)) (g y)))
              '((lambda (x) (cons x x)) (g y)))

(assert-equal (remove-progn '(return-last 'progn (f x) (g y)))
              '(g y))

(assert-equal (remove-progn '(return-last 'progn
                                          x
                                          (return-last 'progn
                                                       (f a b)
                                                       (g c d))))
              '(g c d))

(assert-equal (remove-progn '(return-last 'mbe1-raw a b))
              '(return-last 'mbe1-raw a b))
