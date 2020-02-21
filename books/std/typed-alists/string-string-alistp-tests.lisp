; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-string-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (string-string-alistp nil))

(assert! (string-string-alistp '(("abc" . "def"))))

(assert! (string-string-alistp '(("" . "1") ("U" . "string"))))

(assert! (not (string-string-alistp 465)))

(assert! (not (string-string-alistp '("a" "b" "c"))))

(assert! (not (string-string-alistp '(("a" . "b") (c . "d")))))

(assert! (not (string-string-alistp '(("a" . "b") ("c" . d)))))
