; Proofs about a 1-instruction binary that subtracts a sign-extended 8-bit immediate from RBX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_rbx_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_rbx_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sub_rbx_imm8, which
;; represents the effect of the program on the x86 state.
;; SUB RBX, 5 is encoded as 48 83 EB 05 (4 bytes), so stop PC = 0x401004.
;; The immediate 5 is sign-extended from 8 to 64 bits before the subtraction;
;; since 5 > 0 and 5 < 128, sign extension leaves its value unchanged.
(def-unrolled sub_rbx_imm8
  :executable "sub_rbx_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RBX register is updated to the 64-bit difference of RBX minus 5
;; (Intel SDM Vol 2A: DEST <- DEST - SignExtend(SRC), size = qword).
(defthm sub_rbx_imm8-rbx
  (equal (rbx (sub_rbx_imm8 x86))
         (bvminus 64 (rbx x86) 5)))

;; The RIP is advanced by 4 (SUB RBX, 5 is 4 bytes: REX.W 83 EB 05)
(defthm sub_rbx_imm8-rip
  (equal (rip (sub_rbx_imm8 x86))
         (+ 4 #x401000)))

;; All other (non-RBX) registers are unchanged:
(defthm sub_rbx_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (sub_rbx_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is 1 iff 5 > RBX unsigned (borrow):
(defthm sub_rbx_imm8-cf
  (equal (get-flag :cf (sub_rbx_imm8 x86))
         (if (bvlt 64 (rbx x86) 5) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_rbx_imm8-zf
  (equal (get-flag :zf (sub_rbx_imm8 x86))
         (if (equal 0 (bvminus 64 (rbx x86) 5)) 1 0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result:
(defthm sub_rbx_imm8-sf
  (equal (get-flag :sf (sub_rbx_imm8 x86))
         (getbit 63 (bvminus 64 (rbx x86) 5)))
  :hints (("Goal" :in-theory (enable bvminus))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of RBX < 5:
(defthm sub_rbx_imm8-af
  (equal (get-flag :af (sub_rbx_imm8 x86))
         (if (< (bvchop 4 (rbx x86)) 5) 1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 64-bit result overflows:
(defthm sub_rbx_imm8-of
  (equal (get-flag :of (sub_rbx_imm8 x86))
         (let ((diff (- (logext 64 (rbx x86)) 5)))
           (if (or (< diff (- (expt 2 63)))
                   (<= (expt 2 63) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec64 of-spec64 signed-byte-p))))

(defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_rbx_imm8-pf
  (equal (get-flag :pf (sub_rbx_imm8 x86))
         (let ((diff (bvminus 64 (rbx x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def bvminus))))

;; Memory is unchanged (this instruction does not access memory):
(defthm sub_rbx_imm8-memory-unchanged
  (equal (memi address (sub_rbx_imm8 x86))
         (memi address x86)))

(defthm sub_rbx_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_rbx_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
