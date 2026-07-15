; Proofs about a 1-instruction binary that shifts a register (16-bit) right by 1 (logical)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shr_ax_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shr_ax_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function shr_ax_1, which
;; represents the effect of the program on the x86 state.
;; SHR AX, 1 is encoded as 66 D1 E8 (3 bytes), so stop PC = #x401003.
(def-unrolled shr_ax_1
  :executable "shr_ax_1.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the shifted result; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm shr_ax_1-rax
  (equal (rax (shr_ax_1 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvshr 16 (ax x86) 1)))
  :hints (("Goal" :in-theory (enable bvshr))))

;; AX after the operation: DEST is shifted right by 1, filling with 0 on
;; the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHR entry: logical right shift).
(defthm shr_ax_1-ax
  (equal (ax (shr_ax_1 x86))
         (bvshr 16 (ax x86) 1))
  :hints (("Goal" :in-theory (enable bvshr))))

;; The RIP is advanced by 3 (SHR AX, 1 is encoded as 66 D1 E8 (3 bytes), so stop PC = #x401003.)
(defthm shr_ax_1-rip
  (equal (rip (shr_ax_1 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shr_ax_1-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shr_ax_1 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit 0 (the original LSB) of the
;; original operand (Intel SDM Vol 2B SHR entry).
(defthm shr_ax_1-cf
  (equal (get-flag :cf (shr_ax_1 x86))
         (getbit 0 (ax x86))))

;; For a 1-bit shift, OF is set to the most-significant bit of the original
;; operand (Intel SDM Vol 2B SHR entry: OF affected only on 1-bit shifts; for
;; SHR, OF is set to the MSB of the original operand before shifting).
(defthm shr_ax_1-of
  (equal (get-flag :of (shr_ax_1 x86))
         (getbit 15 (ax x86))))

;; The zero flag is 1 iff the result is 0.
(defthm shr_ax_1-zf
  (equal (get-flag :zf (shr_ax_1 x86))
         (if (equal 0 (bvshr 16 (ax x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr zf-spec))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm shr_ax_1-sf
  (equal (get-flag :sf (shr_ax_1 x86))
         (getbit 15 (bvshr 16 (ax x86) 1)))
  :hints (("Goal" :in-theory (enable bvshr))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shr_ax_1-pf
  (equal (get-flag :pf (shr_ax_1 x86))
         (if (evenp (bvcount 8 (bvshr 16 (ax x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr pf-spec16-alt-def))))

;; All memory addresses are unchanged.
(defthm shr_ax_1-memory-unchanged
  (equal (memi address (shr_ax_1 x86))
         (memi address x86)))

;; AF is undefined for SHR (Intel SDM Vol 2B SHR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shr_ax_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shr_ax_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
