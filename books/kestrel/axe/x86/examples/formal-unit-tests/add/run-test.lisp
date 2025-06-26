; A trivial example of calling the x86 Formal Unit Tester
;
; Copyright (C) 2025 Kestrel Institutea
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X") ; X is the package for doing x86 proofs with Axe

;; Include the Axe Formal Unit Tester for x86:
(include-book "kestrel/axe/x86/tester" :dir :system)

;; (depends-on "add.elf64")

;; The Formal Unit Tester proves that the function always returns 1, for all
;; inputs (subject to reasonable assumptions):
(test-function "test_unsigned_long_add_commutative" "add.elf64")
