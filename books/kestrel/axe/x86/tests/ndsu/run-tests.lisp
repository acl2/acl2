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

;; (depends-on "and-CF.elf64")
(test-file "and-CF.elf64")

;; (depends-on "and-OF.elf64")
(test-file "and-OF.elf64")

;; (depends-on "and-PF.elf64")
;; todo: (test-file "and-PF.elf64")

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
(test-file "sub-OF.elf64")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "add.elf64")
(test-file "add.elf64")

;; (depends-on "add-r-imm.elf64")
(test-file "add-r-imm.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "add-r32-m32.elf64")
(test-file "add-r32-m32.elf64")

;; (depends-on "add-imm.macho64")
(test-file "add-imm.macho64")

;; (depends-on "sub-imm.macho64")
(test-file "sub-imm.macho64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "add-all-configurations.macho64")
(test-file "add-all-configurations.macho64")

;; (depends-on "add-all-configurations.pe64")
(test-file "add-all-configurations.pe64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "sub-all-configurations.macho64")
(test-file "sub-all-configurations.macho64")

;; (depends-on "sub-all-configurations.pe64")
(test-file "sub-all-configurations.pe64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "and.macho64")
;;(test-file "and.macho64")

;; (depends-on "and.pe64")
(test-file "and.pe64")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "or.macho64")
(test-file "or.macho64")

;; (depends-on "or.pe64")
(test-file "or.pe64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "xor.macho64")
(test-file "xor.macho64")

;; (depends-on "xor.pe64")
(test-file "xor.pe64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "cmp.macho64")
(test-file "cmp.macho64")

;; (depends-on "cmp.pe64")
(test-file "cmp.pe64")

