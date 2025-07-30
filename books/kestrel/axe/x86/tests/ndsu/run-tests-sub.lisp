
; Tests of the x86 Formal Unit Tester and x86 instruction models
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; cert_param: (ttags :all)
; cert_param: (uses-stp)
(in-package "X") ; X is the package for doing x86 proofs with Axe

;; Include the Axe Formal Unit Tester for x86:
(include-book "kestrel/axe/x86/tester" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (depends-on "sub-all-configurations.macho64")
(test-file "sub-all-configurations.macho64")

;; (depends-on "sub-all-configurations.pe64")
(test-file "sub-all-configurations.pe64")


;; (depends-on "sub-all-configurations.elf64")
(test-file "sub-all-configurations.elf64")



