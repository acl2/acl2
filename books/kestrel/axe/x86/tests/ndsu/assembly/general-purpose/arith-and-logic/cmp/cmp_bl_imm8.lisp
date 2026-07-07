; Proofs about a 1-instruction binary that compares BL to an 8-bit immediate
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_bl_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_bl_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

(local (defthm bl-rewrite
  (equal (bl x86) (bvchop 8 (rbx x86)))
  :hints (("Goal" :in-theory (enable bl rbx)))))

;; Lifts the subroutine into logic: Creates the function cmp_bl_imm8, which
;; represents the effect of the program on the x86 state.
;; CMP BL, 5 is encoded as 80 FB 05 (3 bytes), so stop PC = 0x401003.
(def-unrolled cmp_bl_imm8
  :executable "cmp_bl_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 3 (CMP BL, 5 is 3 bytes: 80 FB 05)
(defthm cmp_bl_imm8-rip
  (equal (rip (cmp_bl_imm8 x86))
         (+ 3 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST is not updated, so all
;; registers are unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_bl_imm8-registers
  (equal (rgfi reg (cmp_bl_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 5 > BL unsigned (borrow):
(defthm cmp_bl_imm8-cf
  (equal (get-flag :cf (cmp_bl_imm8 x86))
         (if (bvlt 8 (bl x86) 5) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_bl_imm8-zf
  (equal (get-flag :zf (cmp_bl_imm8 x86))
         (if (equal 0 (bvminus 8 (bl x86) 5)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec8 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 7) of the 8-bit difference:
(defthm cmp_bl_imm8-sf
  (equal (get-flag :sf (cmp_bl_imm8 x86))
         (getbit 7 (bvminus 8 (bl x86) 5)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of BL < 5:
(defthm cmp_bl_imm8-af
  (equal (get-flag :af (cmp_bl_imm8 x86))
         (if (< (bvchop 4 (bl x86)) 5) 1 0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 8-bit difference overflows:
(defthm cmp_bl_imm8-of
  (equal (get-flag :of (cmp_bl_imm8 x86))
         (let ((diff (- (logext 8 (bl x86)) 5)))
           (if (or (< diff (- (expt 2 7)))
                   (<= (expt 2 7) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_bl_imm8-pf
  (equal (get-flag :pf (cmp_bl_imm8 x86))
         (let ((diff (bvminus 8 (bl x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Memory is unchanged (this instruction does not access memory):
(defthm cmp_bl_imm8-memory-unchanged
  (equal (memi address (cmp_bl_imm8 x86))
         (memi address x86)))

(defthm cmp_bl_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_bl_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
