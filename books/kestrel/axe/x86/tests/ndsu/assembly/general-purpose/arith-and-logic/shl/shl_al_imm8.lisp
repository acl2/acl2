; Proofs about a 1-instruction binary that shifts a register (8-bit) left by 3
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_al_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_al_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function shl_al_imm8, which
;; represents the effect of the program on the x86 state.
;; SHL AL, 3 is encoded as C0 E0 03 (3 bytes), so stop PC = 0x401003.
(def-unrolled shl_al_imm8
  :executable "shl_al_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: DEST is shifted left by 3, filling with 0 on
;; the right (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift).
(defthm shl_al_imm8-al
  (equal (al (shl_al_imm8 x86))
         (bvshl 8 (al x86) 3))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The RIP is advanced by 3 (SHL AL, 3 is encoded as C0 E0 03 (3 bytes), so stop PC = 0x401003.)
(defthm shl_al_imm8-rip
  (equal (rip (shl_al_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shl_al_imm8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shl_al_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit (8 - 3) = bit 5
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_al_imm8-cf
  (equal (get-flag :cf (shl_al_imm8 x86))
         (getbit 5 (al x86))))

;; OF is undefined for shifts other than by 1 (Intel SDM Vol 2B SHL/SAL
;; entry: "The OF flag is affected only on 1-bit shifts."), so no theorem is
;; stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm shl_al_imm8-zf
  (equal (get-flag :zf (shl_al_imm8 x86))
         (if (equal 0 (bvshl 8 (al x86) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm shl_al_imm8-sf
  (equal (get-flag :sf (shl_al_imm8 x86))
         (getbit 7 (bvshl 8 (al x86) 3)))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shl_al_imm8-pf
  (equal (get-flag :pf (shl_al_imm8 x86))
         (if (evenp (bvcount 8 (bvshl 8 (al x86) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged.
(defthm shl_al_imm8-memory-unchanged
  (equal (memi address (shl_al_imm8 x86))
         (memi address x86)))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shl_al_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_al_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
