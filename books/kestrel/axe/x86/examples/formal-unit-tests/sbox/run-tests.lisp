; An example of calling the x86 Formal Unit Tester
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

;; (depends-on "sbox.elf64")
;; cert_param: (uses-stp)

;; Runs all 7 tests in the file, including proving the inversion and
;; injectivity properties of the sboxes.  6 tests are expected to pass (because
;; their names start with "test_") and 1 is expected to fail (because its name
;; starts with "fail_test_").  The Tester ensures that all results are as
;; expected.  Note that the failed attempt to prove fail_test_box_not_zero
;; produces the counterexample: (:var-counterexample ((rdi . 82) (r9 . 0) (r8
;; . 0) (rcx . 0) (rdx . 0) (rsi . 0))) This assigns the value 82 to RDI, which
;; is the argument, i, of the test.  82 is the index of the zero value in the
;; sbox array.  This is the counterexample to the test's claim that sbox[i] is
;; not zero.
(test-file "sbox.elf64")
