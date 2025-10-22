; Apply the Formal Unit Tester to BinarySearch
;
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book runs the Formal Unit Tester on all the tests in BinarySearch.java.

;; NOTE: This file is only used for regression testing and debugging.  Normally
;; the Formal Unit Tester would be invoked from the command line or from within
;; an IDE.

; (depends-on "BinarySearch.class")

(include-book "kestrel/axe/jvm/tester" :dir :system)

(test-file "BinarySearch.java")
