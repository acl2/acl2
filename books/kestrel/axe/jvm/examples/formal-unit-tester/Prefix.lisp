; Apply the Formal Unit Tester to Prefix
;
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; (depends-on "Prefix.class")

(include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system)

;; TODO: BV-ARRAY-READ-OF-BV-ARRAY-WRITE introduces <
(test-file "Prefix.java")
