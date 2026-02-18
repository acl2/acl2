; The "A" package for ARM Axe proofs
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; to support LDing this file, since in this dir, ACL2 starts in the "A" package

(include-book "kestrel/axe/imported-symbols" :dir :system)
(include-book "kestrel/arm/portcullis" :dir :system)

;; Users of the ARM variant of Axe can use this "A" package for their books
;; that use Axe to lift/verify ARM code.

;; This is similar to the "X" package used by the x86 variant of Axe.

;; In general, we import function names, but not theorem names, from other
;; packages into this package.

(defconst *arm-symbols*
  '(arm::arm ; the stobj name
    arm::armp ; stobj recognizer

    arm::registers
    arm::apsr
    arm::isetstate
    arm::itstate
    arm::endianstate
    arm::memory

    arm::read-byte
    arm::read-bytes
    arm::read
    arm::write-byte
    arm::write-bytes
    arm::write
    arm::arm32-decode
    arm::pc
    arm::step
    arm::reg
    arm::set-reg
    arm::pc
    arm::r0
    arm::r1
    arm::r2
    arm::r3
    arm::r4
    arm::r5
    arm::r6
    arm::r7
    arm::r8
    arm::r9
    arm::r10
    arm::r11
    arm::r12
    arm::r13
    arm::r14
    arm::r15
    arm::error
    arm::*pc*
    arm::*sp*
    arm::*lr*
    arm::register-numberp

    arm::apsr.n
    arm::apsr.z
    arm::apsr.c
    arm::apsr.v
    arm::apsr.q

    arm::set-apsr.n
    arm::set-apsr.z
    arm::set-apsr.c
    arm::set-apsr.v
    arm::set-apsr.q

    arm::in-region32p
    arm::subregion32p
    arm::disjoint-regions32p

    arm::*patterns*

    arm::*InstrSet_ARM*
    arm::*InstrSet_Thumb*
    arm::*InstrSet_Jazelle*
    arm::*InstrSet_ThumbEE*

    ;; keeping this axe-specific for now:
    ;; arm::update-call-stack-height-aux
    ;; arm::update-call-stack-height
    ;; arm::run-until-return-aux
    ;; arm::run-until-return
    ;; arm::run-subroutine
    ))

;; (defconst *arm-symbols-in-acl2-package*
;;   '(ubyte32-list-fix))

(defconst *axe-arm-implementation-symbols*
  '(ensure-arm))

(defconst *common-arm-names*
  ;; Some of these are common used field names in instructions
  '(arm::s
    arm::rn
    arm::rm
    arm::rd
    arm::imm12
    ;; todo more
    arm::n1
    arm::n2
    arm::ad1
    arm::ad2
    arm::val
    ))

;; todo: make consistent with X package
(defpkg "A"
    (append *symbols-from-acl2-package*
            *axe-rule-lists*
            *apt-symbols*
            *axe-term-symbols*
            *bv-list-symbols*
            *axe-implementation-symbols*
            *axe-rule-symbols*
            *arithmetic-symbols*
            *logops-symbols*
            *axe-tools*
            *common-acl2-formals*
            ;; *memory-region-symbols*

            ;; ARM-specific stuff:
            *arm-symbols*
            *axe-arm-implementation-symbols*
            ;; *arm-symbols-in-acl2-package*

            (set-difference-eq *acl2-exports*
                               '(pc ; we need this name for accessing the program counter
                                 ))))
