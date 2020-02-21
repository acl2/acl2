; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-string-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-string-alistp nil))

(assert! (symbol-string-alistp '((x . "x") (y . "y") (z . "z"))))

(assert! (not (symbol-string-alistp '(("x" . x)))))

(assert! (not (symbol-string-alistp '((symbol . "string") 77))))
