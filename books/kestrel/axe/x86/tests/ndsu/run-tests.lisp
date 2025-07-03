; Tests of the x86 Formal Unit Tester and x86 instruction models
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X") ; X is the package for doing x86 proofs with Axe

;; cert_param: (uses-stp)

;; Include the Axe Formal Unit Tester for x86:
(include-book "kestrel/axe/x86/tester" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "adc-CF.elf64")
(test-file "adc-CF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "add-AF.elf64")
(test-file "add-AF.elf64")

;; (depends-on "add-CF.elf64")
(test-file "add-CF.elf64")

;; (depends-on "add-OF.elf64")
(test-file "add-OF.elf64")

;; (depends-on "add-PF0.elf64")
(test-file "add-PF0.elf64")

;; (depends-on "add-PF1.elf64")
(test-file "add-PF1.elf64")

;; (depends-on "add-SF.elf64")
(test-file "add-SF.elf64")

;; (depends-on "add-ZF.elf64")
(test-file "add-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "and-CF.elf64")
(test-file "and-CF.elf64")

;; (depends-on "and-OF.elf64")
(test-file "and-OF.elf64")

;; (depends-on "and-SF.elf64")
(test-file "and-SF.elf64")

;; (depends-on "and-ZF.elf64")
(test-file "and-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "cmp-CF.elf64")
(test-file "cmp-CF.elf64")

;; (depends-on "cmp-PF0.elf64")
(test-file "cmp-PF0.elf64")

;; (depends-on "cmp-PF1.elf64")
(test-file "cmp-PF1.elf64")

;; (depends-on "cmp-SF.elf64")
(test-file "cmp-SF.elf64")

;; (depends-on "cmp-ZF.elf64")
(test-file "cmp-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "or-CF.elf64")
(test-file "or-CF.elf64")

;; (depends-on "or-OF.elf64")
(test-file "or-OF.elf64")

;; (depends-on "or-SF.elf64")
(test-file "or-SF.elf64")

;; (depends-on "or-ZF.elf64")
(test-file "or-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "sub-CF.elf64")
(test-file "sub-CF.elf64")

;; (depends-on "sub-OF.elf64")
;todo: (test-file "sub-OF.elf64")

;; (depends-on "sub-PF0.elf64")
(test-file "sub-PF0.elf64")

;; (depends-on "sub-PF1.elf64")
(test-file "sub-PF1.elf64")

;; (depends-on "sub-SF.elf64")
(test-file "sub-SF.elf64")

;; (depends-on "sub-ZF.elf64")
(test-file "sub-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "add-commutative.elf64")
(test-file "add-commutative.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "inc_dec.elf64")
(test-file "inc_dec.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "test-CF.elf64")
(test-file "test-CF.elf64")

;; (depends-on "test-OF.elf64")
(test-file "test-OF.elf64")

;; (depends-on "test-SF.elf64")
(test-file "test-SF.elf64")

;; (depends-on "test-ZF.elf64")
(test-file "test-ZF.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "xor-CF.elf64")
(test-file "xor-CF.elf64")

;; (depends-on "xor-OF.elf64")
(test-file "xor-OF.elf64")

;; (depends-on "xor-SF.elf64")
(test-file "xor-SF.elf64")

;; (depends-on "xor-ZF.elf64")
(test-file "xor-ZF.elf64")
