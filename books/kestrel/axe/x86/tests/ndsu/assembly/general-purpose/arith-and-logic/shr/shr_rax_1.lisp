; Proofs about a 1-instruction binary that shifts a register (64-bit) right by 1 (logical)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shr_rax_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shr_rax_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function shr_rax_1, which
;; represents the effect of the program on the x86 state.
;; SHR RAX, 1 is encoded as 48 D1 E8 (3 bytes), so stop PC = #x401003.
(def-unrolled shr_rax_1
  :executable "shr_rax_1.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: DEST is shifted right by 1, filling with 0 on
;; the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SHR entry: logical right shift).
(defthm shr_rax_1-rax
  (equal (rax (shr_rax_1 x86))
         (bvshr 64 (rax x86) 1))
  :hints (("Goal" :in-theory (enable bvshr))))

;; The RIP is advanced by 3 (SHR RAX, 1 is encoded as 48 D1 E8 (3 bytes), so stop PC = #x401003.)
(defthm shr_rax_1-rip
  (equal (rip (shr_rax_1 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm shr_rax_1-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (shr_rax_1 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit 0 (the original LSB) of the
;; original operand (Intel SDM Vol 2B SHR entry).
(defthm shr_rax_1-cf
  (equal (get-flag :cf (shr_rax_1 x86))
         (getbit 0 (rax x86))))

;; For a 1-bit shift, OF is set to the most-significant bit of the original
;; operand (Intel SDM Vol 2B SHR entry: OF affected only on 1-bit shifts; for
;; SHR, OF is set to the MSB of the original operand before shifting).
(defthm shr_rax_1-of
  (equal (get-flag :of (shr_rax_1 x86))
         (getbit 63 (rax x86))))

;; The zero flag is 1 iff the result is 0.
(defthm shr_rax_1-zf
  (equal (get-flag :zf (shr_rax_1 x86))
         (if (equal 0 (bvshr 64 (rax x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr zf-spec))))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm shr_rax_1-sf
  (equal (get-flag :sf (shr_rax_1 x86))
         (getbit 63 (bvshr 64 (rax x86) 1)))
  :hints (("Goal" :in-theory (enable bvshr))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shr_rax_1-pf
  (equal (get-flag :pf (shr_rax_1 x86))
         (if (evenp (bvcount 8 (bvshr 64 (rax x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr pf-spec64-alt-def))))

;; All memory addresses are unchanged.
(defthm shr_rax_1-memory-unchanged
  (equal (memi address (shr_rax_1 x86))
         (memi address x86)))

;; AF is undefined for SHR (Intel SDM Vol 2B SHR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shr_rax_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shr_rax_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
