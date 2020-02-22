; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "term-possible-numbers-of-results")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (term-possible-numbers-of-results 'x (w state))
              (list 1))

(assert-equal (term-possible-numbers-of-results '(quote 3) (w state))
              (list 1))

(must-succeed*
 (defun f (x) (mv x x x))
 (assert-equal (term-possible-numbers-of-results '(f x) (w state))
               (list 3)))

(assert-equal (term-possible-numbers-of-results '(cons a (cons b 'nil))
                                                (w state))
              (list 1 2))


(must-succeed*
 (defun f (x) (mv x x))
 (assert-equal (term-possible-numbers-of-results '(if something
                                                      (cons a (cons b 'nil))
                                                    (f c))
                                                 (w state))
               (list 2)))
