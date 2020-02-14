; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-pos-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-pos-alistp nil))

(assert! (symbol-pos-alistp '((a . 2))))

(assert! (symbol-pos-alistp '((t . 88) (:kwd . 1))))

(assert! (not (symbol-pos-alistp 3)))

(assert! (not (symbol-pos-alistp '(3))))

(assert! (not (symbol-pos-alistp '((x . 3) (2/3 . 10)))))

(assert! (not (symbol-pos-alistp '((xx . 1) (t . 0)))))

(assert! (not (symbol-pos-alistp '((xx . -100) (t . 1)))))
