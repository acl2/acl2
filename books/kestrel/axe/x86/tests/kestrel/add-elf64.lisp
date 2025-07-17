; A simple test of the unrolling lifter
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Simple test of the unrolling lifter

;; May not be strictly needed for this example but will be in general:
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;; (depends-on "add.elf64")
;; Lift the add function into logic by unrolling:
(def-unrolled add "add.elf64" :target "add"
  :output :rax ; return only the sum
  )

;;expected result:
(must-be-redundant
  (defun add (x86)
    (declare (xargs :non-executable t :mode :logic)) ; from defun-nx
    (declare (xargs :stobjs x86 :verify-guards nil))
    (prog2$ (acl2::throw-nonexec-error 'add (list x86))
            ;; RDI and RSI are the first 2 arguments:
            (bvplus 32 (rsi x86) (rdi x86)))))
