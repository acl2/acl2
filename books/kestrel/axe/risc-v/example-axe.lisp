; Axe verification of a RISC-V program that adds 2 numbers
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Move to examples subdir

;; STATUS: COMPLETE

(include-book "unroll")
(include-book "kestrel/axe/equivalence-checker" :dir :system)

; (depends-on "add.elf32")

;; Lift the code, creating the dag *add*.
;; (There are no loops to unroll.)
;; todo: add support for naming the inputs:
(def-unrolled add
  :target "f"
  :executable "add.elf32"
  ;; extract the return value (the sum), which by convention is in register a0:
  :output :a0)

;; Prove that the lifted code is correct:
(acl2::prove-equal-with-axe
  ;; the lifted code:
  *add*
  ;; the spec (add the first 2 arguments, which by convention are in registers a0 and a1):
  '(bvplus 32 (a0 stat) (a1 stat))
  ;; expand the register aliases:
  :extra-rules '(a0 a1 x10 x11))

;; todo: also characterize the rest of the state components
