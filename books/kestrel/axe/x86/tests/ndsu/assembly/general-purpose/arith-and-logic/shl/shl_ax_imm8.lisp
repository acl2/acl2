; Proofs about a 1-instruction binary that shifts a register (16-bit) left by 3
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_ax_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_ax_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function shl_ax_imm8, which
;; represents the effect of the program on the x86 state.
;; SHL AX, 3 is encoded as 66 C1 E0 03 (4 bytes), so stop PC = 0x401004.
(def-unrolled shl_ax_imm8
  :executable "shl_ax_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the shifted result; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm shl_ax_imm8-rax
  (equal (rax (shl_ax_imm8 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvshl 16 (ax x86) 3)))
  :hints (("Goal" :in-theory (enable bvshl))))

;; AX after the operation: DEST is shifted left by 3, filling with 0 on
;; the right (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift).
(defthm shl_ax_imm8-ax
  (equal (ax (shl_ax_imm8 x86))
         (bvshl 16 (ax x86) 3))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The RIP is advanced by 4 (SHL AX, 3 is encoded as 66 C1 E0 03 (4 bytes), so stop PC = 0x401004.)
(defthm shl_ax_imm8-rip
  (equal (rip (shl_ax_imm8 x86))
         (+ 4 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shl_ax_imm8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shl_ax_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit (16 - 3) = bit 13
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_ax_imm8-cf
  (equal (get-flag :cf (shl_ax_imm8 x86))
         (getbit 13 (ax x86))))

;; OF is undefined for shifts other than by 1 (Intel SDM Vol 2B SHL/SAL
;; entry: "The OF flag is affected only on 1-bit shifts."), so no theorem is
;; stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm shl_ax_imm8-zf
  (equal (get-flag :zf (shl_ax_imm8 x86))
         (if (equal 0 (bvshl 16 (ax x86) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm shl_ax_imm8-sf
  (equal (get-flag :sf (shl_ax_imm8 x86))
         (getbit 15 (bvshl 16 (ax x86) 3)))
  :hints (("Goal" :in-theory (enable bvshl))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shl_ax_imm8-pf
  (equal (get-flag :pf (shl_ax_imm8 x86))
         (if (evenp (bvcount 8 (bvshl 16 (ax x86) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec16-alt-def))))

;; All memory addresses are unchanged.
(defthm shl_ax_imm8-memory-unchanged
  (equal (memi address (shl_ax_imm8 x86))
         (memi address x86)))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shl_ax_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_ax_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
