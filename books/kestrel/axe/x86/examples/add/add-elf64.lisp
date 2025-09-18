; A proof of a very simple x86 binary function that adds 2 numbers
;
; Copyright (C) 2016-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: COMPLETE

;; Lifts the functionality of add.elf64 into logic using the Axe-based x86
;; lifter and prove equivalent to spec.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)

;; Lift the subroutine into logic:
(def-unrolled add-elf64
  "add.elf64"
  :target "add"
  :stack-slots 2)

;; The above command created the function add-elf64, which represents the
;; effect of the program on the x86 state.

;; Shows that the program stores in RAX the sum of the initial values of RDI
;; and RSI.
(defthm add-elf64-correct
  (equal (rax (add-elf64 x86))
         (bvplus 32 (rdi x86) (rsi x86))))
