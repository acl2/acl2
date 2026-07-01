; Proofs about a 1-instruction binary that subtracts a sign-extended 8-bit immediate from a memory word
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_mem16_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_mem16_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sub_mem16_imm8, which
;; represents the effect of the program on the x86 state.
;; SUB [RBX], 5 is encoded as 66 83 2B 05 (4 bytes), so stop PC = 0x401004.
;; The immediate 5 is sign-extended from 8 to 16 bits before the subtraction;
;; since 5 > 0 and 5 < 128, sign extension leaves its value unchanged.
;; Both the base address and +1 must be canonical for the 16-bit write.
(def-unrolled sub_mem16_imm8
  :executable "sub_mem16_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The word at memory address [RBX] is updated to the 16-bit difference of the original
;; word at [RBX] minus SignExtend(5) = 5
;; (Intel SDM Vol 2A: DEST <- DEST - SignExtend(SRC), size = word).
(defthm sub_mem16_imm8-memory-at-rbx
  (equal (read 2 (rbx x86) (sub_mem16_imm8 x86))
         (bvminus 16 (read 2 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the 2 bytes at [RBX] and [RBX+1] are written).
(defthm sub_mem16_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 2))
           (equal (read 1 address (sub_mem16_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 4 (SUB [RBX], 5 is 4 bytes: 66 83 2B 05)
(defthm sub_mem16_imm8-rip
  (equal (rip (sub_mem16_imm8 x86))
         (+ 4 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sub_mem16_imm8-registers
  (equal (rgfi reg (sub_mem16_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 5 > mem[RBX] unsigned (borrow):
(defthm sub_mem16_imm8-cf
  (equal (get-flag :cf (sub_mem16_imm8 x86))
         (if (bvlt 16 (read 2 (rbx x86) x86) 5) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_mem16_imm8-zf
  (equal (get-flag :zf (sub_mem16_imm8 x86))
         (if (equal 0 (bvminus 16 (read 2 (rbx x86) x86) 5)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec16 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result:
(defthm sub_mem16_imm8-sf
  (equal (get-flag :sf (sub_mem16_imm8 x86))
         (getbit 15 (bvminus 16 (read 2 (rbx x86) x86) 5)))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec16 bvminus acl2::bvchop-of-sum-cases) (read-2-blast acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < 5:
(defthm sub_mem16_imm8-af
  (equal (get-flag :af (sub_mem16_imm8 x86))
         (if (< (bvchop 4 (read 2 (rbx x86) x86))
                5)
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (read-2-blast acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 16-bit result overflows:
(defthm sub_mem16_imm8-of
  (equal (get-flag :of (sub_mem16_imm8 x86))
         (let ((diff (- (logext 16 (read 2 (rbx x86) x86)) 5)))
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

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_mem16_imm8-pf
  (equal (get-flag :pf (sub_mem16_imm8 x86))
         (let ((diff (bvminus 16 (read 2 (rbx x86) x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (e/d (sub-pf-spec16 pf-spec16-alt-def bvminus acl2::bvchop-of-sum-cases) (read-2-blast)))))

(defthm sub_mem16_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_mem16_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
