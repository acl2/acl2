; Proofs about a 1-instruction binary that compares AX to an immediate (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_ax_imm16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_ax_imm16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function cmp_ax_imm16, which
;; represents the effect of the program on the x86 state.
;; CMP AX, 300 is encoded as 66 3D 2C 01 (4 bytes), so stop PC = 0x401004.
(def-unrolled cmp_ax_imm16
  :executable "cmp_ax_imm16.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 4 (CMP AX, imm16 is 4 bytes: 66 3D 2C 01)
(defthm cmp_ax_imm16-rip
  (equal (rip (cmp_ax_imm16 x86))
         (+ 4 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST is not updated, so all
;; registers are unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_ax_imm16-registers
  (equal (rgfi reg (cmp_ax_imm16 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 300 > AX unsigned:
(defthm cmp_ax_imm16-cf
  (equal (get-flag :cf (cmp_ax_imm16 x86))
         (if (bvlt 16 (ax x86) 300) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_ax_imm16-zf
  (equal (get-flag :zf (cmp_ax_imm16 x86))
         (if (equal 0 (bvminus 16 (ax x86) 300)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec16 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 15) of the 16-bit difference:
(defthm cmp_ax_imm16-sf
  (equal (get-flag :sf (cmp_ax_imm16 x86))
         (getbit 15 (bvminus 16 (ax x86) 300)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec16 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff there is a borrow from bit 4 into bit 3
;; (i.e., the low nibble of AX is less than the low nibble of 300):
(defthm cmp_ax_imm16-af
  (equal (get-flag :af (cmp_ax_imm16 x86))
         (if (< (bvchop 4 (ax x86))
                (bvchop 4 300))
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 16-bit difference overflows:
(defthm cmp_ax_imm16-of
  (equal (get-flag :of (cmp_ax_imm16 x86))
         (let ((diff (- (logext 16 (ax x86)) 300)))
           (if (or (< diff (- (expt 2 15)))
                   (<= (expt 2 15) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec16 of-spec16 signed-byte-p))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_ax_imm16-pf
  (equal (get-flag :pf (cmp_ax_imm16 x86))
         (let ((diff (bvminus 16 (ax x86) 300)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec16 pf-spec16-alt-def bvminus acl2::bvchop-of-sum-cases))))

;; All memory addresses are unchanged:
(defthm cmp_ax_imm16-memory-unchanged
  (equal (memi address (cmp_ax_imm16 x86))
         (memi address x86)))

(defthm cmp_ax_imm16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_ax_imm16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
