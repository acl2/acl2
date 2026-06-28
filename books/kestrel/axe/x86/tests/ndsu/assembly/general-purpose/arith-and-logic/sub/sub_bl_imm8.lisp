; Proofs about a 1-instruction binary that subtracts an 8-bit immediate from BL
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_bl_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_bl_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

(local (defthm bl-rewrite
  (equal (bl x86) (bvchop 8 (rbx x86)))
  :hints (("Goal" :in-theory (enable bl rbx)))))

;; Lifts the subroutine into logic: Creates the function sub_bl_imm8, which
;; represents the effect of the program on the x86 state.
;; SUB BL, 5 is encoded as 80 EB 05 (3 bytes), so stop PC = 0x401003.
(def-unrolled sub_bl_imm8
  :executable "sub_bl_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The BL register is updated to the 8-bit difference of BL minus 5
;; (Intel SDM Vol 2A: DEST <- DEST - SRC).
(defthm sub_bl_imm8-bl
  (equal (bl (sub_bl_imm8 x86))
         (bvminus 8 (bl x86) 5)))

;; The RIP is advanced by 3 (SUB BL, 5 is 3 bytes: 80 EB 05)
(defthm sub_bl_imm8-rip
  (equal (rip (sub_bl_imm8 x86))
         (+ 3 #x401000)))

;; All other (non-RBX) registers are unchanged:
(defthm sub_bl_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (sub_bl_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is 1 iff 5 > BL unsigned (borrow):
(defthm sub_bl_imm8-cf
  (equal (get-flag :cf (sub_bl_imm8 x86))
         (if (bvlt 8 (bl x86) 5) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_bl_imm8-zf
  (equal (get-flag :zf (sub_bl_imm8 x86))
         (if (equal 0 (bvminus 8 (bl x86) 5)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec8 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result:
(defthm sub_bl_imm8-sf
  (equal (get-flag :sf (sub_bl_imm8 x86))
         (getbit 7 (bvminus 8 (bl x86) 5)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of BL < 5:
(defthm sub_bl_imm8-af
  (equal (get-flag :af (sub_bl_imm8 x86))
         (if (< (bvchop 4 (bl x86)) 5) 1 0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 8-bit result overflows:
(defthm sub_bl_imm8-of
  (equal (get-flag :of (sub_bl_imm8 x86))
         (let ((diff (- (logext 8 (bl x86)) 5)))
           (if (or (< diff (- (expt 2 7)))
                   (<= (expt 2 7) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_bl_imm8-pf
  (equal (get-flag :pf (sub_bl_imm8 x86))
         (let ((diff (bvminus 8 (bl x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Memory is unchanged (this instruction does not access memory):
(defthm sub_bl_imm8-memory-unchanged
  (equal (memi address (sub_bl_imm8 x86))
         (memi address x86)))

(defthm sub_bl_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_bl_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
