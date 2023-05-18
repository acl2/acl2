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

;; NOTE: This file is only used for regression testing and debugging.  Normally
;; the Formal Unit Tester would be invoked from the command line or from within
;; an IDE.

; (depends-on "Prefix.class")

(include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system)

;; TODO: BV-ARRAY-READ-OF-BV-ARRAY-WRITE introduces <
(test-file "Prefix.java")
