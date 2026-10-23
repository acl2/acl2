; Apply the Formal Unit Tester to ClassTest
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book runs the Formal Unit Tester on all the tests in ClassTest.java.

; (depends-on "ClassTest.class")

(include-book "kestrel/axe/jvm/tester" :dir :system)

;; In this one, we assume x is non-null, so the null test in the code doesn't do much:
(test-file "ClassTest.java" :assume-object-params-non-null t)

;; In this one, we don't assume x is non-null, relying on the null test in the code:
;; TODO: Avoid printing "WARNING: Unexpected state term:" in this example:
(test-file "ClassTest.java" :assume-object-params-non-null nil)
