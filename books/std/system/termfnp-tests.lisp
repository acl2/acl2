; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "termfnp")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

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
