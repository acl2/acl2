; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "untranslate-dollar")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal
 (untranslate$ 'x nil state)
 'x)

(assert-equal
 (untranslate$ ''4 nil state)
 4)

(assert-equal
 (untranslate$ ''"abc" nil state)
 "abc")

(assert-equal
 (untranslate$ '(f x) nil state)
 '(f x))

(assert-equal
 (untranslate$ '((lambda (x) (binary-+ '1 x)) '3)
               nil
               state)
 '(let ((x 3)) (+ 1 x)))

(assert-equal
 (untranslate$ '(if a b 'nil)
               nil
               state)
 '(and a b))

(assert-equal
 (untranslate$ '(if a a b)
               nil
               state)
 '(or a b))
