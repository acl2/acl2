; Axe verification of a ARM program that adds 2 numbers
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

;; STATUS: COMPLETE, needs cleaning up

(include-book "kestrel/axe/arm/unroller" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm conditionpassed-of-14
 (equal (arm::conditionpassed 14 arm)
        t)
 :hints (("Goal" :in-theory (enable arm::conditionpassed))))

(defthm conditionpassed-of-9
  (equal (arm::conditionpassed 9 arm)
         (not (and (equal (apsr.c arm) 1)
                   (equal (apsr.z arm) 0))))
 :hints (("Goal" :in-theory (enable arm::conditionpassed))))

;; (depends-on "add.elf32-musl-static")

;; Lift the code, creating the dag *add*.
;; (There are no loops to unroll.)
;; todo: add support for naming the inputs:
(def-unrolled add
    :target "add"
    :executable "add.elf32-musl-static"
    ;; extract the return value (the sum), which by convention is in register a0:
    :output :r0
    :extra-assumptions '((unsigned-byte-p '32 base-address)  ; todo: automate
                         (integerp base-address)             ; todo: automate
                         (equal '0 (bvchop 2 (reg '14 arm))) ; todo: automate
                         ;; name the inputs:
                         (equal (reg 0 arm) x)
                         (equal (reg 1 arm) y)))


;; Prove that the lifted code is correct:
(prove-equal-with-axe
 ;; the lifted code:
 *add*
 ;; the spec (add the first 2 arguments):
 '(bvplus 32 x y))

;; todo: also characterize the rest of the state components
