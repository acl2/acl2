; Proofs about a 1-instruction binary that shifts an extended 8-bit register (R8B) right by CL (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_r8b_cl.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_r8b_cl.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite cl to bvchop-of-rcx so proofs reduce to the existing rcx form.
(local (defthm cl-rewrite
  (equal (cl x86) (bvchop 8 (rcx x86)))
  :hints (("Goal" :in-theory (enable cl rcx)))))

;; Lifts the subroutine into logic: Creates the function sar_r8b_cl, which
;; represents the effect of the program on the x86 state.
;; SAR R8B, CL is encoded as 41 D2 F8 (3 bytes), so stop PC = #x401003.
(def-unrolled sar_r8b_cl
  :executable "sar_r8b_cl.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Since the destination is not 64 bits, the count in CL is masked to 5 bits
;; (Intel SDM Vol 2B SAR entry: "tempCOUNT <- (COUNT AND 1FH)" when the
;; operand size is not 64 bits).

;; The Axe-based bvashr operator is defined only for shift amounts strictly
;; less than the operand width; per the Intel SDM, a masked count greater
;; than or equal to the operand size leaves the result and flags undefined,
;; so we state the value only for masked counts in [0, 8).
;; R8B (the low 8 bits of R8) after the operation: DEST is shifted right by
;; the masked count in CL, with the sign bit replicated into the vacated
;; bits on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SAR entry: arithmetic
;; right shift, fills with the original sign bit).
(defthm sar_r8b_cl-r8b
  (implies (bvlt 5 (bvchop 5 (cl x86)) 8)
           (equal (bvchop 8 (r8 (sar_r8b_cl x86)))
                  (bvashr 8 (bvchop 8 (r8 x86)) (bvchop 5 (cl x86)))))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; The RIP is advanced by 3 (SAR R8B, CL is encoded as 41 D2 F8 (3 bytes), so stop PC = #x401003.)
(defthm sar_r8b_cl-rip
  (equal (rip (sar_r8b_cl x86))
         (+ 3 #x401000)))

;; Registers other than R8 are unchanged.
(defthm sar_r8b_cl-other-registers
  (implies (not (equal *r8* reg))
           (equal (rgfi reg (sar_r8b_cl x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-r8))))

;; If the masked count is 0, no flags are affected at all (Intel SDM Vol 2B
;; SAR entry: "If the count is 0, the flags are not affected.").
(defthm sar_r8b_cl-flags-unaffected-when-count-zero
  (implies (equal (bvchop 5 (cl x86)) 0)
           (equal (get-flag flag (sar_r8b_cl x86))
                  (get-flag flag x86))))

;; For a masked count strictly between 0 and the operand size, CF is set to
;; the last bit shifted out, i.e., bit (count - 1) of the original operand
;; (Intel SDM Vol 2B SAR entry).
(defthm sar_r8b_cl-cf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 8))
           (equal (get-flag :cf (sar_r8b_cl x86))
                  (getbit (+ (bvchop 5 (cl x86)) -1) (bvchop 8 (r8 x86))))))

;; For a masked count of exactly 1, OF is cleared to 0 (Intel SDM Vol 2B SAR
;; entry: OF is affected only on 1-bit shifts, and for SAR is always cleared
;; to 0 on a 1-bit shift since the sign bit never changes).
(defthm sar_r8b_cl-of
  (implies (equal (bvchop 5 (cl x86)) 1)
           (equal (get-flag :of (sar_r8b_cl x86))
                  0)))

;; For any nonzero masked count, the zero flag is 1 iff the result is 0.
(defthm sar_r8b_cl-zf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 8))
           (equal (get-flag :zf (sar_r8b_cl x86))
                  (if (equal 0 (bvashr 8 (bvchop 8 (r8 x86)) (bvchop 5 (cl x86))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvashr bvshr zf-spec))))

;; For any nonzero masked count, the sign flag is the sign bit (bit 7) of
;; the 8-bit result.
(defthm sar_r8b_cl-sf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 8))
           (equal (get-flag :sf (sar_r8b_cl x86))
                  (getbit 7 (bvashr 8 (bvchop 8 (r8 x86)) (bvchop 5 (cl x86))))))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; For any nonzero masked count, the parity flag considers only the 8 least
;; significant bits of the result and is 1 iff they contain an even number
;; of 1s.
(defthm sar_r8b_cl-pf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 8))
           (equal (get-flag :pf (sar_r8b_cl x86))
                  (if (evenp (bvcount 8 (bvashr 8 (bvchop 8 (r8 x86)) (bvchop 5 (cl x86)))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvashr bvshr pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged.
(defthm sar_r8b_cl-memory-unchanged
  (equal (memi address (sar_r8b_cl x86))
         (memi address x86)))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags,
;; which SAR never touches regardless of the count.
(defthm sar_r8b_cl-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_r8b_cl x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
