; Proofs about a 1-instruction binary that shifts a register (32-bit) left by CL
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_eax_cl.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_eax_cl.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))
;; Rewrite cl to bvchop-of-rcx so proofs reduce to the existing rcx form.
(local (defthm cl-rewrite
  (equal (cl x86) (bvchop 8 (rcx x86)))
  :hints (("Goal" :in-theory (enable cl rcx)))))

;; Lifts the subroutine into logic: Creates the function shl_eax_cl, which
;; represents the effect of the program on the x86 state.
;; SHL EAX, CL is encoded as D3 E0 (2 bytes), so stop PC = 0x401002.
(def-unrolled shl_eax_cl
  :executable "shl_eax_cl.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Since the destination is not 64 bits, the count in CL is masked to
;; 5 bits (Intel SDM Vol 2B SHL/SAL entry: "tempCOUNT <- (COUNT AND 1FH)"
;; when the operand size is not 64 bits).

;; RAX contains the 32-bit shifted result zero-extended to 64 bits (32-bit ops in 64-bit mode always zero-extend the result).
(defthm shl_eax_cl-rax
  (equal (rax (shl_eax_cl x86))
         (bvshl 32 (eax x86) (bvchop 5 (cl x86))))
  :hints (("Goal" :in-theory (enable bvshl))))

;; EAX after the operation: DEST is shifted left by the masked count in CL,
;; filling with 0 on the right (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL
;; entry: logical left shift).
(defthm shl_eax_cl-eax
  (equal (eax (shl_eax_cl x86))
         (bvshl 32 (eax x86) (bvchop 5 (cl x86))))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The RIP is advanced by 2 (SHL EAX, CL is encoded as D3 E0 (2 bytes), so stop PC = 0x401002.)
(defthm shl_eax_cl-rip
  (equal (rip (shl_eax_cl x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shl_eax_cl-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shl_eax_cl x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; If the masked count is 0, no flags are affected at all (Intel SDM Vol 2B
;; SHL/SAL entry: "If the count is 0, the flags are not affected.").
(defthm shl_eax_cl-flags-unaffected-when-count-zero
  (implies (equal (bvchop 5 (cl x86)) 0)
           (equal (get-flag flag (shl_eax_cl x86))
                  (get-flag flag x86))))

;; For a masked count strictly between 0 and the operand size, CF is set to
;; the last bit shifted out, i.e., bit (32 - count) of the original
;; operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_eax_cl-cf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 32))
           (equal (get-flag :cf (shl_eax_cl x86))
                  (getbit (+ 32 (- (bvchop 5 (cl x86)))) (eax x86)))))

;; Bridge lemma: the top bit of a 1-bit left shift is the next-to-top bit of
;; the original operand.  Purely a fact about bvshl/getbit, not the x86 model.
(local (defthm getbit-31-of-bvshl-32-by-1
  (equal (getbit 31 (bvshl 32 x 1))
         (getbit 30 x))
  :hints (("Goal" :in-theory (enable bvshl)))))

;; For a masked count of exactly 1, OF is set to CF XOR the most-significant
;; bit of the result (Intel SDM Vol 2B SHL/SAL entry: OF affected only on
;; 1-bit shifts; for left shifts, OF = CF XOR MSB of the result).
(defthm shl_eax_cl-of
  (implies (equal (bvchop 5 (cl x86)) 1)
           (equal (get-flag :of (shl_eax_cl x86))
                  (bitxor (getbit 31 (eax x86))
                          (getbit 31 (bvshl 32 (eax x86) 1))))))

;; For any nonzero masked count, the zero flag is 1 iff the result is 0.
(defthm shl_eax_cl-zf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :zf (shl_eax_cl x86))
                  (if (equal 0 (bvshl 32 (eax x86) (bvchop 5 (cl x86))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; For any nonzero masked count, the sign flag is the sign bit (bit 31)
;; of the 32-bit result.
(defthm shl_eax_cl-sf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :sf (shl_eax_cl x86))
                  (getbit 31 (bvshl 32 (eax x86) (bvchop 5 (cl x86))))))
  :hints (("Goal" :in-theory (enable bvshl))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; For any nonzero masked count, the parity flag considers only the 8 least
;; significant bits of the result and is 1 iff they contain an even number
;; of 1s.
(defthm shl_eax_cl-pf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :pf (shl_eax_cl x86))
                  (if (evenp (bvcount 8 (bvshl 32 (eax x86) (bvchop 5 (cl x86)))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvshl pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm shl_eax_cl-memory-unchanged
  (equal (memi address (shl_eax_cl x86))
         (memi address x86)))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags,
;; which SHL never touches regardless of the count.
(defthm shl_eax_cl-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_eax_cl x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
