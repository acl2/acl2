; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-symbol-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-symbol-alistp nil))

(assert! (symbol-symbol-alistp '((a . b))))

(assert! (symbol-symbol-alistp '((a . x) (b . y) (c . z))))

(assert! (symbol-symbol-alistp '((t . nil) (:logic . :program))))

(assert! (not (symbol-symbol-alistp 3)))

(assert! (not (symbol-symbol-alistp 55)))

(assert! (not (symbol-symbol-alistp '(3))))

(assert! (not (symbol-symbol-alistp '((x . y) (2/3 . nil)))))

(assert! (not (symbol-symbol-alistp '((xx . yy) (t . "nil")))))

(assert! (not (symbol-symbol-alistp '((a . "x") (b . y)))))

(assert! (not (symbol-symbol-alistp '((a . x) ("b" . y)))))
