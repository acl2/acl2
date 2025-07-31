; A test of the unrolling lifter on a PE64 executable
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; May not be strictly needed for this example but will be in general:
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;; (depends-on "add.pe64")
;; Lift the add function into logic by unrolling:
(def-unrolled add "add.pe64" :target "add"
  :output :rax ; return only the sum
  )

;;expected result:
(must-be-redundant
  (defun add (x86)
    (declare (xargs :non-executable t :mode :logic)) ; from defun-nx
    (declare (xargs :stobjs x86 :verify-guards nil))
    (prog2$ (acl2::throw-nonexec-error 'add (list x86))
            ;; Note that the registers used to pass the arguments are different
            ;; than for ELF64 files:
            (bvplus 32 (rdx x86) (rcx x86)))))
