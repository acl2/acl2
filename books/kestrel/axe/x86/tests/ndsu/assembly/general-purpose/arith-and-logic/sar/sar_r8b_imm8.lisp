; Proofs about a 1-instruction binary that shifts an extended 8-bit register (R8B) right by 3 (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_r8b_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_r8b_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function sar_r8b_imm8, which
;; represents the effect of the program on the x86 state.
;; SAR R8B, 3 is encoded as 41 C0 F8 03 (4 bytes), so stop PC = #x401004.
(def-unrolled sar_r8b_imm8
  :executable "sar_r8b_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; R8B (the low 8 bits of R8) after the operation: DEST is shifted right by
;; 3, with the sign bit replicated into the vacated bits on the left (Intel
;; SDM Vol 1 3.4.3.1 and Vol 2B SAR entry: arithmetic right shift, fills with
;; the original sign bit).
(defthm sar_r8b_imm8-r8b
  (equal (bvchop 8 (r8 (sar_r8b_imm8 x86)))
         (bvashr 8 (bvchop 8 (r8 x86)) 3))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; The RIP is advanced by 4 (SAR R8B, 3 is encoded as 41 C0 F8 03 (4 bytes), so stop PC = #x401004.)
(defthm sar_r8b_imm8-rip
  (equal (rip (sar_r8b_imm8 x86))
         (+ 4 #x401000)))

;; Registers other than R8 are unchanged.
(defthm sar_r8b_imm8-other-registers
  (implies (not (equal *r8* reg))
           (equal (rgfi reg (sar_r8b_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-r8))))

;; CF is set to the last bit shifted out, i.e., bit 2 of the original
;; operand (Intel SDM Vol 2B SAR entry).
(defthm sar_r8b_imm8-cf
  (equal (get-flag :cf (sar_r8b_imm8 x86))
         (getbit 2 (bvchop 8 (r8 x86)))))

;; OF is affected only on 1-bit shifts (Intel SDM Vol 2B SAR entry), so no
;; theorem is stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm sar_r8b_imm8-zf
  (equal (get-flag :zf (sar_r8b_imm8 x86))
         (if (equal 0 (bvashr 8 (bvchop 8 (r8 x86)) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm sar_r8b_imm8-sf
  (equal (get-flag :sf (sar_r8b_imm8 x86))
         (getbit 7 (bvashr 8 (bvchop 8 (r8 x86)) 3)))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm sar_r8b_imm8-pf
  (equal (get-flag :pf (sar_r8b_imm8 x86))
         (if (evenp (bvcount 8 (bvashr 8 (bvchop 8 (r8 x86)) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged.
(defthm sar_r8b_imm8-memory-unchanged
  (equal (memi address (sar_r8b_imm8 x86))
         (memi address x86)))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm sar_r8b_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_r8b_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
