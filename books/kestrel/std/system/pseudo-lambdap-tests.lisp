; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambdap")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (pseudo-lambdap "abc")))

(assert! (not (pseudo-lambdap (cons 3 6))))

(assert! (not (pseudo-lambdap '(lambda (x) x extra))))

(assert! (not (pseudo-lambdap '(lambd (x) x))))

(assert! (not (pseudo-lambdap '(lambda (x 8) x))))

(assert! (not (pseudo-lambdap '(lambda (x y) #\a))))

(assert! (pseudo-lambdap '(lambda (x) x)))

(assert! (pseudo-lambdap '(lambda (x y z) (+ x (* y z)))))

(assert! (pseudo-lambdap '(lambda (x y z) (+ x x))))

(assert! (pseudo-lambdap '(lambda (x y z) (+ a b))))

(must-succeed*
 (defconst *term* '((lambda (x) (1+ x)) y))
 (assert! (pseudo-termp *term*))
 (assert! (pseudo-lambdap (ffn-symb *term*))))
