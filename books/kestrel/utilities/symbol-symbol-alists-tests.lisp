; Alists from Symbols to Symbols -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-symbol-alists")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (symbol-symbol-alistp nil))

(assert! (symbol-symbol-alistp '((a . x) (b . y) (c . z))))

(assert! (not (symbol-symbol-alistp 55)))

(assert! (not (symbol-symbol-alistp '((a . "x") (b . y)))))

(assert! (not (symbol-symbol-alistp '((a . x) ("b" . y)))))
