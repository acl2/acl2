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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "and.macho64")
(test-file "and.macho64")

;; (depends-on "and.pe64")
(test-file "and.pe64")

;; (depends-on "and.elf64")
(test-file "and.elf64")
