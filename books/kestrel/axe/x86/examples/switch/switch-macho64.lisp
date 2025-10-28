; A proof of a simple x86 binary function with a switch statement
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: INCOMPLETE (awaiting jump table support in Axe)

;; This example demonstrates lifting a switch statement that compiles to a jump
;; table.  The compiler generates a jump table for the switch statement, which
;; uses indirect jumps (jmpq *%rax).  This is currently not supported by the Axe
;; x86 lifter.  Once jump table support is implemented, this example should work.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "switch.macho64")

#|
;; TODO: Uncomment when jump table support is added to Axe

;; Lift the subroutine into logic:
(def-unrolled classify-value
  :executable "switch.macho64"
  :target "_classify_value"
  :stack-slots 2)

;; The above command created the function classify-value, which represents the
;; effect of the program on the x86 state.

;; Shows that the program correctly implements the switch statement.
;; For inputs 0-3, it returns 100, 200, 300, 400 respectively.
;; For all other inputs, it returns -1 (0xFFFFFFFF in 32-bit representation).
(defthm classify-value-correct-case-0
  (equal (rax (classify-value (init-x86-state (list 0) x86)))
         100))

(defthm classify-value-correct-case-1
  (equal (rax (classify-value (init-x86-state (list 1) x86)))
         200))

(defthm classify-value-correct-case-2
  (equal (rax (classify-value (init-x86-state (list 2) x86)))
         300))

(defthm classify-value-correct-case-3
  (equal (rax (classify-value (init-x86-state (list 3) x86)))
         400))

(defthm classify-value-correct-default
  (implies (not (member-equal x '(0 1 2 3)))
           (equal (rax (classify-value (init-x86-state (list x) x86)))
                  (bvuminus 32 1))))
|#
