; A proof of a very simple x86 binary function that adds 2 numbers
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: COMPLETE

;; Lifts the functionality of add.elf64 into logic using the Axe-based x86
;; lifter and proves that the value returned by the (lifted) code is correct.

;; (depends-on "add.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lift the subroutine into logic: Creates the function add-elf64, which
;; represents the effect of the program on the x86 state.
(def-unrolled add-elf64
  :executable "add.elf64"
  :target "add"
  :stack-slots 2)

;; Shows that the program stores in RAX the sum of the initial values of RDI
;; and RSI.
(defthm add-elf64-correct
  (equal (rax (add-elf64 x86))
         (bvplus 32 (rdi x86) (rsi x86))))
