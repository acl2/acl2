; Proofs about a 1-instruction binary that subtracts a 32-bit immediate from EBX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_ebx_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_ebx_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function sub_ebx_imm32, which
;; represents the effect of the program on the x86 state.
;; SUB EBX, 1000 is encoded as 81 EB E8 03 00 00 (6 bytes), so stop PC = 0x401006.
;; 32-bit operations zero-extend into the upper 32 bits of RBX.
(def-unrolled sub_ebx_imm32
  :executable "sub_ebx_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401006))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RBX register is updated to the 32-bit difference of EBX minus 1000, zero-extended to 64 bits.
;; 32-bit results are zero-extended into the full 64-bit register
;; (Intel SDM Vol 1 Section 3.4.1.1: 32-bit operands zero-extend to 64 bits).
(defthm sub_ebx_imm32-rbx
  (equal (rbx (sub_ebx_imm32 x86))
         (bvminus 32 (ebx x86) 1000)))

(defthm sub_ebx_imm32-ebx
  (equal (ebx (sub_ebx_imm32 x86))
         (bvminus 32 (ebx x86) 1000)))

;; The RIP is advanced by 6 (SUB EBX, 1000 is 6 bytes: 81 EB E8 03 00 00)
(defthm sub_ebx_imm32-rip
  (equal (rip (sub_ebx_imm32 x86))
         (+ 6 #x401000)))

;; All other (non-RBX) registers are unchanged:
(defthm sub_ebx_imm32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (sub_ebx_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is 1 iff 1000 > EBX unsigned (borrow):
(defthm sub_ebx_imm32-cf
  (equal (get-flag :cf (sub_ebx_imm32 x86))
         (if (bvlt 32 (ebx x86) 1000) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_ebx_imm32-zf
  (equal (get-flag :zf (sub_ebx_imm32 x86))
         (if (equal 0 (bvminus 32 (ebx x86) 1000)) 1 0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result:
(defthm sub_ebx_imm32-sf
  (equal (get-flag :sf (sub_ebx_imm32 x86))
         (getbit 31 (bvminus 32 (ebx x86) 1000)))
  :hints (("Goal" :in-theory (enable bvminus))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of EBX < low nibble of 1000:
(defthm sub_ebx_imm32-af
  (equal (get-flag :af (sub_ebx_imm32 x86))
         (if (< (bvchop 4 (ebx x86)) (bvchop 4 1000)) 1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 32-bit result overflows:
(defthm sub_ebx_imm32-of
  (equal (get-flag :of (sub_ebx_imm32 x86))
         (let ((diff (- (logext 32 (ebx x86)) 1000)))
           (if (or (< diff (- (expt 2 31)))
                   (<= (expt 2 31) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec32 of-spec32 signed-byte-p))))

(defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_ebx_imm32-pf
  (equal (get-flag :pf (sub_ebx_imm32 x86))
         (if (evenp (bvcount 8 (bvminus 32 (ebx x86) 1000))) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvminus))))

;; Memory is unchanged (this instruction does not access memory):
(defthm sub_ebx_imm32-memory-unchanged
  (equal (memi address (sub_ebx_imm32 x86))
         (memi address x86)))

(defthm sub_ebx_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_ebx_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
