; Proofs about a 1-instruction binary that shifts a register (32-bit) right by 3 (logical)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shr_eax_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shr_eax_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function shr_eax_imm8, which
;; represents the effect of the program on the x86 state.
;; SHR EAX, 3 is encoded as C1 E8 03 (3 bytes), so stop PC = #x401003.
(def-unrolled shr_eax_imm8
  :executable "shr_eax_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit shifted result zero-extended to 64 bits (32-bit ops in 64-bit mode always zero-extend the result).
(defthm shr_eax_imm8-rax
  (equal (rax (shr_eax_imm8 x86))
         (bvshr 32 (eax x86) 3))
  :hints (("Goal" :in-theory (enable bvshr))))

;; EAX after the operation: DEST is shifted right by 3, filling with 0 on
;; the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHR entry: logical right shift).
(defthm shr_eax_imm8-eax
  (equal (eax (shr_eax_imm8 x86))
         (bvshr 32 (eax x86) 3))
  :hints (("Goal" :in-theory (enable bvshr))))

;; The RIP is advanced by 3 (SHR EAX, 3 is encoded as C1 E8 03 (3 bytes), so stop PC = #x401003.)
(defthm shr_eax_imm8-rip
  (equal (rip (shr_eax_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shr_eax_imm8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shr_eax_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit 2 of the original
;; operand (Intel SDM Vol 2B SHR entry).
(defthm shr_eax_imm8-cf
  (equal (get-flag :cf (shr_eax_imm8 x86))
         (getbit 2 (eax x86))))

;; OF is affected only on 1-bit shifts (Intel SDM Vol 2B SHR entry: "The OF
;; flag is affected only on 1-bit shifts."), so no theorem is stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm shr_eax_imm8-zf
  (equal (get-flag :zf (shr_eax_imm8 x86))
         (if (equal 0 (bvshr 32 (eax x86) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr zf-spec))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm shr_eax_imm8-sf
  (equal (get-flag :sf (shr_eax_imm8 x86))
         (getbit 31 (bvshr 32 (eax x86) 3)))
  :hints (("Goal" :in-theory (enable bvshr))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shr_eax_imm8-pf
  (equal (get-flag :pf (shr_eax_imm8 x86))
         (if (evenp (bvcount 8 (bvshr 32 (eax x86) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm shr_eax_imm8-memory-unchanged
  (equal (memi address (shr_eax_imm8 x86))
         (memi address x86)))

;; AF is undefined for SHR (Intel SDM Vol 2B SHR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shr_eax_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shr_eax_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
