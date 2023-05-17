; Apply the Formal Unit Tester to BinarySearch
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; (depends-on "BinarySearch.class")

(include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system)

(test-file "BinarySearch.java")
