; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fsublis-var")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fsublis-var '((x . '1) (y . '2)) '(quote "a"))
              '(quote "a"))

(assert-equal (fsublis-var '((x . '1) (y . '2)) 'z)
              'z)

(assert-equal (fsublis-var '((x . '1) (y . '2)) 'x)
              '(quote 1))

(assert-equal (fsublis-var '((x . '1) (y . '2)) '((lambda (x) x) y))
              '((lambda (x) x) '2))

(assert-equal (fsublis-var '((x . '1) (y . '2)) '(f x (g z)))
              '(f '1 (g z)))
