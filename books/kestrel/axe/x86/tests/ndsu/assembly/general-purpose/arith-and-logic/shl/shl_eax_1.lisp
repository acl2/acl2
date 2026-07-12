; Proofs about a 1-instruction binary that shifts a register (32-bit) left by 1
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_eax_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_eax_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function shl_eax_1, which
;; represents the effect of the program on the x86 state.
;; SHL EAX, 1 is encoded as D1 E0 (2 bytes), so stop PC = 0x401002.
(def-unrolled shl_eax_1
  :executable "shl_eax_1.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit shifted result zero-extended to 64 bits (32-bit ops in 64-bit mode always zero-extend the result).
(defthm shl_eax_1-rax
  (equal (rax (shl_eax_1 x86))
         (bvshl 32 (eax x86) 1))
  :hints (("Goal" :in-theory (enable bvshl))))

;; EAX after the operation: DEST is shifted left by 1, filling with 0 on
;; the right (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift).
(defthm shl_eax_1-eax
  (equal (eax (shl_eax_1 x86))
         (bvshl 32 (eax x86) 1))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The RIP is advanced by 2 (SHL EAX, 1 is encoded as D1 E0 (2 bytes), so stop PC = 0x401002.)
(defthm shl_eax_1-rip
  (equal (rip (shl_eax_1 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shl_eax_1-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shl_eax_1 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit (32 - 1) = bit 31
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_eax_1-cf
  (equal (get-flag :cf (shl_eax_1 x86))
         (getbit 31 (eax x86))))

;; Bridge lemma: the top bit of a 1-bit left shift is the next-to-top bit of
;; the original operand.  Purely a fact about bvshl/getbit, not the x86 model.
(local (defthm getbit-31-of-bvshl-32-by-1
  (equal (getbit 31 (bvshl 32 x 1))
         (getbit 30 x))
  :hints (("Goal" :in-theory (enable bvshl)))))

;; For a 1-bit shift, OF is set to CF XOR the most-significant bit of the
;; result (Intel SDM Vol 2B SHL/SAL entry: OF affected only on 1-bit shifts;
;; for left shifts, OF = CF XOR MSB of the result).
(defthm shl_eax_1-of
  (equal (get-flag :of (shl_eax_1 x86))
         (bitxor (getbit 31 (eax x86))
                 (getbit 31 (bvshl 32 (eax x86) 1)))))

;; The zero flag is 1 iff the result is 0.
(defthm shl_eax_1-zf
  (equal (get-flag :zf (shl_eax_1 x86))
         (if (equal 0 (bvshl 32 (eax x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm shl_eax_1-sf
  (equal (get-flag :sf (shl_eax_1 x86))
         (getbit 31 (bvshl 32 (eax x86) 1)))
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
(defthm shl_eax_1-pf
  (equal (get-flag :pf (shl_eax_1 x86))
         (if (evenp (bvcount 8 (bvshl 32 (eax x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm shl_eax_1-memory-unchanged
  (equal (memi address (shl_eax_1 x86))
         (memi address x86)))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shl_eax_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_eax_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
