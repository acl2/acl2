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

(test-file "ClassTest.java")
