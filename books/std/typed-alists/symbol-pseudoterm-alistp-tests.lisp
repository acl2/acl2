; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-pseudoterm-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-pseudoterm-alistp nil))

(assert! (symbol-pseudoterm-alistp '((var . x)
                                     (qconst . (quote 3/4))
                                     (fnapp . (f a b))
                                     (lamapp . ((lambda (x y) (cons x y))
                                                a b)))))

(assert! (not (symbol-pseudoterm-alistp "abc")))

(assert! (not (symbol-pseudoterm-alistp '(x y z))))

(assert! (not (symbol-pseudoterm-alistp '((f a)
                                          (quote 3/4)))))

(assert! (not (symbol-pseudoterm-alistp '((x . nil)
                                          (y . (quote 1 2))))))

(assert! (not (symbol-pseudoterm-alistp '((x . nil)
                                          (y . ((lambda (x) x) '1 '2))))))
