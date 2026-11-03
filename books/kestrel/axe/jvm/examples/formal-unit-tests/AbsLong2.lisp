; Apply the Formal Unit Tester to AbsLong2Test.
;
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book runs the Formal Unit Tester on the tests in AbsLong2Test.java.
;; The point of this book is to show that the tool works when the tests are in
;; a separate class from the code being tested.

; (depends-on "AbsLong2Test.class")

(include-book "kestrel/axe/jvm/tester" :dir :system)

(test-class "AbsLong2Test")
