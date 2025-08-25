; Verification of a RISC-V program that adds 2 numbers
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Move to examples subdir

;; STATUS: COMPLETE, needs automation

(include-book "support-top")
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system)) ; for acl2::mod-becomes-bvchop-when-power-of-2p
(local (include-book "kestrel/bv/rules" :dir :system)) ; for ACL2::BVPLUS-OF-LOGEXT-ARG3, etc.

;; Read in the executable:
(acl2::defconst-x86 *executable* "add.elf32")

;; after running, we extract the return value and prove that it is the correct sum
;; todo: also characterize the rest of the state components
(make-event
  `(defthm add-correct
     (implies (and (equal (pc stat) #x101b0 ; this is the offset of "f" ; todo: shorter name afor read32-pc
                          ;(bvplus 32  base-address) ; for position-independent mode (but see below)
                          )
                   ;; Generates the assumptions:
                   ,@(assumptions-elf32! *executable*
                                         nil ; t doesn't work because ACL2 doesn't want to substitute in the PC expression
                                         )
                   )
              (equal (a0 (run-subroutine stat) ; btw, 14 steps seem needed
                         )
                     (bvplus 32 (a0 stat) (a1 stat))))
     :hints (("Goal" :expand ((:free (n stat) (step32n n stat)))))))
