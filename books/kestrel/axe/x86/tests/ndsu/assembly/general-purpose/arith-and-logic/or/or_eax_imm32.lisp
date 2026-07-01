; Proofs about a 1-instruction binary that ORs EAX with an immediate (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_eax_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_eax_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function or_eax_imm32, which
;; represents the effect of the program on the x86 state.
;; OR EAX, 1000 is encoded as 0D E8 03 00 00 (5 bytes), so stop PC = 0x401005.
(def-unrolled or_eax_imm32
  :executable "or_eax_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401005))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit OR result zero-extended to 64 bits
;; (32-bit ops in 64-bit mode always zero-extend the result).
(defthm or_eax_imm32-rax
  (equal (rax (or_eax_imm32 x86))
         (bvor 32 (eax x86) 1000)))

;; EAX contains the 32-bit OR result (the natural statement for this instruction).
(defthm or_eax_imm32-eax
  (equal (eax (or_eax_imm32 x86))
         (bvor 32 (eax x86) 1000)))

;; The RIP is advanced by 5 (OR EAX, imm32 is 5 bytes: 0D E8 03 00 00)
(defthm or_eax_imm32-rip
  (equal (rip (or_eax_imm32 x86))
         (+ 5 #x401000)))

;; Registers other than RAX are unchanged.
(defthm or_eax_imm32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (or_eax_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: OR clears CF).
(defthm or_eax_imm32-cf
  (equal (get-flag :cf (or_eax_imm32 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: OR clears OF).
(defthm or_eax_imm32-of
  (equal (get-flag :of (or_eax_imm32 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm or_eax_imm32-zf
  (equal (get-flag :zf (or_eax_imm32 x86))
         (if (equal 0 (bvor 32 (eax x86) 1000))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm or_eax_imm32-sf
  (equal (get-flag :sf (or_eax_imm32 x86))
         (getbit 31 (bvor 32 (eax x86) 1000))))

(defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_eax_imm32-pf
  (equal (get-flag :pf (or_eax_imm32 x86))
         (if (evenp (bvcount 8 (bvor 32 (eax x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

;; All memory addresses are unchanged
(defthm or_eax_imm32-memory-unchanged
  (equal (memi address (or_eax_imm32 x86))
         (memi address x86)))

(defthm or_eax_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_eax_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
