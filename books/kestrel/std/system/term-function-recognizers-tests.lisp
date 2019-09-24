; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "term-function-recognizers")

(include-book "misc/assert" :dir :system)
(include-book "misc/eval" :dir :system)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-termfnp 'f))

(assert! (pseudo-termfnp '(lambda (x) x)))

(assert! (not (pseudo-termfnp 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambdap '(lambda (x y) (binary-+ x (len (cons '3 'nil)))) (w state)))

(assert! (not (lambdap '(lambda (x) (fffff x)) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (termfnp "cons" (w state))))

(assert! (not (termfnp 'fffffffff (w state))))

(assert! (termfnp 'cons (w state)))

(assert! (termfnp 'len (w state)))

(assert! (not (termfnp 'car-cdr-elim (w state))))

(must-succeed*
 (defun h (x) x)
 (assert! (termfnp 'h (w state))))

(assert!
 (termfnp '(lambda (x y) (binary-+ x (len (cons '3 'nil)))) (w state)))

(assert! (not (termfnp '(lambda (x) (fffff x)) (w state))))
