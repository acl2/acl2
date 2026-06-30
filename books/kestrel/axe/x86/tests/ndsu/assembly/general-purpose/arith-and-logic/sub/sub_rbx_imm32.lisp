; Proofs about a 1-instruction binary that subtracts a sign-extended 32-bit immediate from RBX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_rbx_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_rbx_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sub_rbx_imm32, which
;; represents the effect of the program on the x86 state.
;; SUB RBX, 1000 is encoded as 48 81 EB E8 03 00 00 (7 bytes), so stop PC = 0x401007.
;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, its value is unchanged.
(def-unrolled sub_rbx_imm32
  :executable "sub_rbx_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401007))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RBX register is updated to the 64-bit difference of RBX minus 1000
;; (Intel SDM Vol 2A: DEST <- DEST - SignExtend(SRC), size = qword).
(defthm sub_rbx_imm32-rbx
  (equal (rbx (sub_rbx_imm32 x86))
         (bvminus 64 (rbx x86) 1000)))

;; The RIP is advanced by 7 (SUB RBX, 1000 is 7 bytes: REX.W 81 EB E8 03 00 00)
(defthm sub_rbx_imm32-rip
  (equal (rip (sub_rbx_imm32 x86))
         (+ 7 #x401000)))

;; All other (non-RBX) registers are unchanged:
(defthm sub_rbx_imm32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (sub_rbx_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is 1 iff 1000 > RBX unsigned (borrow):
(defthm sub_rbx_imm32-cf
  (equal (get-flag :cf (sub_rbx_imm32 x86))
         (if (bvlt 64 (rbx x86) 1000) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_rbx_imm32-zf
  (equal (get-flag :zf (sub_rbx_imm32 x86))
         (if (equal 0 (bvminus 64 (rbx x86) 1000)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec64 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 63) of the 64-bit result:
(defthm sub_rbx_imm32-sf
  (equal (get-flag :sf (sub_rbx_imm32 x86))
         (getbit 63 (bvminus 64 (rbx x86) 1000)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec64 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of RBX < low nibble of 1000:
(defthm sub_rbx_imm32-af
  (equal (get-flag :af (sub_rbx_imm32 x86))
         (if (< (bvchop 4 (rbx x86)) (bvchop 4 1000)) 1 0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 64-bit result overflows:
(defthm sub_rbx_imm32-of
  (equal (get-flag :of (sub_rbx_imm32 x86))
         (let ((diff (- (logext 64 (rbx x86)) 1000)))
           (if (or (< diff (- (expt 2 63)))
                   (<= (expt 2 63) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec64 of-spec64 signed-byte-p))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_rbx_imm32-pf
  (equal (get-flag :pf (sub_rbx_imm32 x86))
         (let ((diff (bvminus 64 (rbx x86) 1000)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec64 pf-spec64-alt-def bvminus acl2::bvchop-of-sum-cases))))

;; Memory is unchanged (this instruction does not access memory):
(defthm sub_rbx_imm32-memory-unchanged
  (equal (memi address (sub_rbx_imm32 x86))
         (memi address x86)))

(defthm sub_rbx_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_rbx_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
