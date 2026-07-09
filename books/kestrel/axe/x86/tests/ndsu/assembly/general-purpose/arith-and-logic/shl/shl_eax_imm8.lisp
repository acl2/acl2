; Proofs about a 1-instruction binary that shifts a register (32-bit) left by 3
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_eax_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_eax_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function shl_eax_imm8, which
;; represents the effect of the program on the x86 state.
;; SHL EAX, 3 is encoded as C1 E0 03 (3 bytes), so stop PC = 0x401003.
(def-unrolled shl_eax_imm8
  :executable "shl_eax_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit shifted result zero-extended to 64 bits (32-bit ops in 64-bit mode always zero-extend the result).
(defthm shl_eax_imm8-rax
  (equal (rax (shl_eax_imm8 x86))
         (bvshl 32 (eax x86) 3))
  :hints (("Goal" :in-theory (enable bvshl))))

;; EAX after the operation: DEST is shifted left by 3, filling with 0 on
;; the right (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift).
(defthm shl_eax_imm8-eax
  (equal (eax (shl_eax_imm8 x86))
         (bvshl 32 (eax x86) 3))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The RIP is advanced by 3 (SHL EAX, 3 is encoded as C1 E0 03 (3 bytes), so stop PC = 0x401003.)
(defthm shl_eax_imm8-rip
  (equal (rip (shl_eax_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shl_eax_imm8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shl_eax_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit (32 - 3) = bit 29
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_eax_imm8-cf
  (equal (get-flag :cf (shl_eax_imm8 x86))
         (getbit 29 (eax x86))))

;; OF is undefined for shifts other than by 1 (Intel SDM Vol 2B SHL/SAL
;; entry: "The OF flag is affected only on 1-bit shifts."), so no theorem is
;; stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm shl_eax_imm8-zf
  (equal (get-flag :zf (shl_eax_imm8 x86))
         (if (equal 0 (bvshl 32 (eax x86) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm shl_eax_imm8-sf
  (equal (get-flag :sf (shl_eax_imm8 x86))
         (getbit 31 (bvshl 32 (eax x86) 3)))
  :hints (("Goal" :in-theory (enable bvshl))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shl_eax_imm8-pf
  (equal (get-flag :pf (shl_eax_imm8 x86))
         (if (evenp (bvcount 8 (bvshl 32 (eax x86) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm shl_eax_imm8-memory-unchanged
  (equal (memi address (shl_eax_imm8 x86))
         (memi address x86)))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shl_eax_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_eax_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
