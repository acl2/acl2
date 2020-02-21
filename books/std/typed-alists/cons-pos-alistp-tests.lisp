; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "cons-pos-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (cons-pos-alistp nil))

(assert! (cons-pos-alistp '(((a . 2) . 4))))

(assert! (cons-pos-alistp '((("str" . #\c) . 88) ((:kwd . (1 2 3)) . 1))))

(assert! (not (cons-pos-alistp 3)))

(assert! (not (cons-pos-alistp '((3 . 4)))))

(assert! (not (cons-pos-alistp '(((a . b) . 3) (2/3 . 10)))))
