; Apply the Formal Unit Tester to BinarySearchBuggy
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; NOTE: This file is only used for regression testing and debugging.  Normally
;; the Formal Unit Tester would be invoked from the command line or from within
;; an IDE.

; (depends-on "BinarySearchBuggy.class")

(include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system)

;; The test fails as follows (with my version of STP):
;; (Counterexample:
;;   Node 0: DATA is (-2147483648 0 0 0 0 0 0 0 0 0).
;;   Node 1: TARGET is -2147483648.
;;   Node 2: (LEN DATA) is 10.
;;   Node 130: (TRUE-LISTP DATA) is T.
;;   Node 132: (ALL-UNSIGNED-BYTE-P '32 DATA) is T.)
(test-file "BinarySearchBuggy.java")
