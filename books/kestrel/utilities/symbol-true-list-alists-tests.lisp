; Alists from Symbols to True Lists -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-true-list-alists")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-true-list-alistp nil))

(assert! (symbol-true-list-alistp '((a . nil) (b . (1 2 3)) (c . (z)))))

(assert! (not (symbol-true-list-alistp 55)))

(assert! (not (symbol-true-list-alistp '((a . "x") (b . (1 2))))))

(assert! (not (symbol-true-list-alistp '((a . (1 2)) ("b" . (10))))))
