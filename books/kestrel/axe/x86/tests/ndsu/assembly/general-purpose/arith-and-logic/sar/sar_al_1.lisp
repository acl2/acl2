; Proofs about a 1-instruction binary that shifts a register (8-bit) right by 1 (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_al_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_al_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function sar_al_1, which
;; represents the effect of the program on the x86 state.
;; SAR AL, 1 is encoded as D0 F8 (2 bytes), so stop PC = #x401002.
(def-unrolled sar_al_1
  :executable "sar_al_1.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: DEST is shifted right by 1, with the sign bit
;; replicated into the vacated bit on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B
;; SAR entry: arithmetic right shift, fills with the original sign bit).
(defthm sar_al_1-al
  (equal (al (sar_al_1 x86))
         (bvashr 8 (al x86) 1))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; The RIP is advanced by 2 (SAR AL, 1 is encoded as D0 F8 (2 bytes), so stop PC = #x401002.)
(defthm sar_al_1-rip
  (equal (rip (sar_al_1 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm sar_al_1-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (sar_al_1 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; CF is set to the last bit shifted out, i.e., bit 0 (the original LSB) of the
;; original operand (Intel SDM Vol 2B SAR entry).
(defthm sar_al_1-cf
  (equal (get-flag :cf (sar_al_1 x86))
         (getbit 0 (al x86))))

;; OF is cleared to 0 for all 1-bit shifts of SAR, since the sign bit never
;; changes (Intel SDM Vol 2B SAR entry).
(defthm sar_al_1-of
  (equal (get-flag :of (sar_al_1 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm sar_al_1-zf
  (equal (get-flag :zf (sar_al_1 x86))
         (if (equal 0 (bvashr 8 (al x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm sar_al_1-sf
  (equal (get-flag :sf (sar_al_1 x86))
         (getbit 7 (bvashr 8 (al x86) 1)))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm sar_al_1-pf
  (equal (get-flag :pf (sar_al_1 x86))
         (if (evenp (bvcount 8 (bvashr 8 (al x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged.
(defthm sar_al_1-memory-unchanged
  (equal (memi address (sar_al_1 x86))
         (memi address x86)))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm sar_al_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_al_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
