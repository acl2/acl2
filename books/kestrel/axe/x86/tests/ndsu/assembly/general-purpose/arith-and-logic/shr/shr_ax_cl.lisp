; Proofs about a 1-instruction binary that shifts a register (16-bit) right by CL (logical)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shr_ax_cl.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shr_ax_cl.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))
;; Rewrite cl to bvchop-of-rcx so proofs reduce to the existing rcx form.
(local (defthm cl-rewrite
  (equal (cl x86) (bvchop 8 (rcx x86)))
  :hints (("Goal" :in-theory (enable cl rcx)))))

;; Lifts the subroutine into logic: Creates the function shr_ax_cl, which
;; represents the effect of the program on the x86 state.
;; SHR AX, CL is encoded as 66 D3 E8 (3 bytes), so stop PC = #x401003.
(def-unrolled shr_ax_cl
  :executable "shr_ax_cl.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Since the destination is not 64 bits, the count in CL is masked to
;; 5 bits (Intel SDM Vol 2B SHR entry: "tempCOUNT <- (COUNT AND 1FH)"
;; when the operand size is not 64 bits).

;; RAX after the operation: only AX (bits 0-15) is updated to the shifted result; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm shr_ax_cl-rax
  (equal (rax (shr_ax_cl x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvshr 16 (ax x86) (bvchop 5 (cl x86)))))
  :hints (("Goal" :in-theory (enable bvshr))))

;; AX after the operation: DEST is shifted right by the masked count in CL,
;; filling with 0 on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHR entry:
;; logical right shift).
(defthm shr_ax_cl-ax
  (equal (ax (shr_ax_cl x86))
         (bvshr 16 (ax x86) (bvchop 5 (cl x86))))
  :hints (("Goal" :in-theory (enable bvshr))))

;; The RIP is advanced by 3 (SHR AX, CL is encoded as 66 D3 E8 (3 bytes), so stop PC = #x401003.)
(defthm shr_ax_cl-rip
  (equal (rip (shr_ax_cl x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shr_ax_cl-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shr_ax_cl x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; If the masked count is 0, no flags are affected at all (Intel SDM Vol 2B
;; SHR entry: "If the count is 0, the flags are not affected.").
(defthm shr_ax_cl-flags-unaffected-when-count-zero
  (implies (equal (bvchop 5 (cl x86)) 0)
           (equal (get-flag flag (shr_ax_cl x86))
                  (get-flag flag x86))))

;; For a masked count strictly between 0 and the operand size, CF is set to
;; the last bit shifted out, i.e., bit (count - 1) of the original operand
;; (Intel SDM Vol 2B SHR entry: for masked counts at or beyond the operand
;; size, CF is undefined).
(defthm shr_ax_cl-cf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 16))
           (equal (get-flag :cf (shr_ax_cl x86))
                  (getbit (+ (bvchop 5 (cl x86)) -1) (ax x86)))))

;; For a masked count of exactly 1, OF is set to the most-significant bit of
;; the original operand (Intel SDM Vol 2B SHR entry: OF affected only on
;; 1-bit shifts).
(defthm shr_ax_cl-of
  (implies (equal (bvchop 5 (cl x86)) 1)
           (equal (get-flag :of (shr_ax_cl x86))
                  (getbit 15 (ax x86)))))

;; For any nonzero masked count, the zero flag is 1 iff the result is 0.
(defthm shr_ax_cl-zf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :zf (shr_ax_cl x86))
                  (if (equal 0 (bvshr 16 (ax x86) (bvchop 5 (cl x86))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvshr zf-spec))))

;; For any nonzero masked count, the sign flag is the sign bit (bit 15)
;; of the 16-bit result.
(defthm shr_ax_cl-sf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :sf (shr_ax_cl x86))
                  (getbit 15 (bvshr 16 (ax x86) (bvchop 5 (cl x86))))))
  :hints (("Goal" :in-theory (enable bvshr))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; For any nonzero masked count, the parity flag considers only the 8 least
;; significant bits of the result and is 1 iff they contain an even number
;; of 1s.
(defthm shr_ax_cl-pf
  (implies (not (equal (bvchop 5 (cl x86)) 0))
           (equal (get-flag :pf (shr_ax_cl x86))
                  (if (evenp (bvcount 8 (bvshr 16 (ax x86) (bvchop 5 (cl x86)))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvshr pf-spec16-alt-def))))

;; All memory addresses are unchanged.
(defthm shr_ax_cl-memory-unchanged
  (equal (memi address (shr_ax_cl x86))
         (memi address x86)))

;; AF is undefined for SHR (Intel SDM Vol 2B SHR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags,
;; which SHR never touches regardless of the count.
(defthm shr_ax_cl-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shr_ax_cl x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
