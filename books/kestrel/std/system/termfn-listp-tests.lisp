; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "termfn-listp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (termfn-listp nil (w state)))

(assert! (termfn-listp (list '(lambda (x) x)
                             'len
                             '(lambda (x y z) (binary-* x z)))
                       (w state)))

(assert! (termfn-listp (list 'not 'atom 'len) (w state)))

(assert! (termfn-listp (list 'not
                             'atom
                             '(lambda (a) (cons a a))
                             'len)
                       (w state)))

(assert! (not (termfn-listp (list "abc" '(lambda (x) x)) (w state))))

(assert! (not (termfn-listp (list 'len 'g) (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (term-listp (list 'f 'not) (w state))))
