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
    arm::error
    arm::*pc* ; todo: more
    ))

;; (defconst *arm-symbols-in-acl2-package*
;;   '(ubyte32-list-fix))

(defconst *axe-arm-implementation-symbols*
  '(ensure-arm))

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
            *memory-region-symbols*

            ;; ARM-specific stuff:
            *arm-symbols*
            *axe-arm-implementation-symbols*
            ;; *arm-symbols-in-acl2-package*

            (set-difference-eq *acl2-exports*
                               '(pc ; we need this name for accessing the program counter
                                 ))))
