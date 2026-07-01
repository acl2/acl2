; Proofs about a 1-instruction binary that ORs a sign-extended 8-bit immediate to EBX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_ebx_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_ebx_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite ebx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function or_ebx_imm8, which
;; represents the effect of the program on the x86 state.
;; OR EBX, 5 is encoded as 83 CB 05 (3 bytes), so stop PC = 0x401003.
;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is unchanged.
(def-unrolled or_ebx_imm8
  :executable "or_ebx_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 32-bit OR result; 32-bit writes zero-extend into the upper 32 bits.
(defthm or_ebx_imm8-rbx
  (equal (rbx (or_ebx_imm8 x86))
         (bvor 32 (ebx x86) 5)))

;; EBX contains the 32-bit OR result (the natural statement for this instruction).
;; (Intel SDM Vol 2A: DEST <- DEST OR SignExtend(SRC); sign-extending 5 gives 5)
(defthm or_ebx_imm8-ebx
  (equal (ebx (or_ebx_imm8 x86))
         (bvor 32 (ebx x86) 5)))

;; The RIP is advanced by 3 (OR EBX, 5 is 3 bytes: 83 CB 05)
(defthm or_ebx_imm8-rip
  (equal (rip (or_ebx_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RBX are unchanged.
(defthm or_ebx_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (or_ebx_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: OR clears CF).
(defthm or_ebx_imm8-cf
  (equal (get-flag :cf (or_ebx_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: OR clears OF).
(defthm or_ebx_imm8-of
  (equal (get-flag :of (or_ebx_imm8 x86))
         0))

;; The zero flag is 1 iff the OR result is 0.
(defthm or_ebx_imm8-zf
  (equal (get-flag :zf (or_ebx_imm8 x86))
         (if (equal 0 (bvor 32 (ebx x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm or_ebx_imm8-sf
  (equal (get-flag :sf (or_ebx_imm8 x86))
         (getbit 31 (bvor 32 (ebx x86) 5))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_ebx_imm8-pf
  (equal (get-flag :pf (or_ebx_imm8 x86))
         (if (evenp (bvcount 8 (bvor 32 (ebx x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm or_ebx_imm8-memory-unchanged
  (equal (memi address (or_ebx_imm8 x86))
         (memi address x86)))

(defthm or_ebx_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_ebx_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
