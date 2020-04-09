; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-vars-open")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/lists/sets" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (set-equiv (all-vars-open 'x)
                    '(x)))

(assert! (set-equiv (all-vars-open 'y)
                    '(y)))

(assert! (set-equiv (all-vars-open '(quote 0))
                    nil))

(assert! (set-equiv (all-vars-open '(f x (g y) z))
                    '(x y z)))

(assert! (set-equiv (all-vars-open '((lambda (z) (cons z z)) (f x)))
                    '(x)))

(assert! (set-equiv (all-vars-open '((lambda (z) (cons z z)) (f y)))
                    '(y)))

(assert! (set-equiv (all-vars-open '((lambda (z) (cons w z)) (f y)))
                    '(w y)))
