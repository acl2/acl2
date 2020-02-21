; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-truelist-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-truelist-alistp nil))

(assert! (symbol-truelist-alistp '((a . nil) (b . (1 2 3)) (c . (z)))))

(assert! (not (symbol-truelist-alistp 55)))

(assert! (not (symbol-truelist-alistp '((a . "x") (b . (1 2))))))

(assert! (not (symbol-truelist-alistp '((a . (1 2)) ("b" . (10))))))
