; Proofs about a 1-instruction binary that compares a memory word to a 16-bit immediate
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_mem16_imm16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_mem16_imm16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function cmp_mem16_imm16, which
;; represents the effect of the program on the x86 state.
;; CMP [RBX], 300 is encoded as 66 81 3B 2C 01 (5 bytes), so stop PC = 0x401005.
;; Both the base address and +1 must be canonical for the 16-bit read.
(def-unrolled cmp_mem16_imm16
  :executable "cmp_mem16_imm16.elf64"
  :target #x401000
  :stop-pcs '(#x401005)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 5 (CMP [RBX], 300 is 5 bytes: 66 81 3B 2C 01)
(defthm cmp_mem16_imm16-rip
  (equal (rip (cmp_mem16_imm16 x86))
         (+ 5 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST (memory) is not updated, so
;; all memory is unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_mem16_imm16-memory-unchanged
  (equal (memi address (cmp_mem16_imm16 x86))
         (memi address x86)))

;; All registers are unchanged (CMP does not write to any register either).
(defthm cmp_mem16_imm16-registers
  (equal (rgfi reg (cmp_mem16_imm16 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 300 > mem[RBX] unsigned (borrow):
(defthm cmp_mem16_imm16-cf
  (equal (get-flag :cf (cmp_mem16_imm16 x86))
         (if (bvlt 16 (read 2 (rbx x86) x86) 300) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_mem16_imm16-zf
  (equal (get-flag :zf (cmp_mem16_imm16 x86))
         (if (equal 0 (bvminus 16 (read 2 (rbx x86) x86) 300)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec16 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 15) of the 16-bit difference:
(defthm cmp_mem16_imm16-sf
  (equal (get-flag :sf (cmp_mem16_imm16 x86))
         (getbit 15 (bvminus 16 (read 2 (rbx x86) x86) 300)))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec16 bvminus acl2::bvchop-of-sum-cases) (read-2-blast acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < low nibble of 300:
(defthm cmp_mem16_imm16-af
  (equal (get-flag :af (cmp_mem16_imm16 x86))
         (if (< (bvchop 4 (read 2 (rbx x86) x86))
                (bvchop 4 300))
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (read-2-blast acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 16-bit difference overflows:
(defthm cmp_mem16_imm16-of
  (equal (get-flag :of (cmp_mem16_imm16 x86))
         (let ((diff (- (logext 16 (read 2 (rbx x86) x86)) 300)))
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
(defthm cmp_mem16_imm16-pf
  (equal (get-flag :pf (cmp_mem16_imm16 x86))
         (let ((diff (bvminus 16 (read 2 (rbx x86) x86) 300)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (e/d (sub-pf-spec16 pf-spec16-alt-def bvminus acl2::bvchop-of-sum-cases) (read-2-blast)))))

(defthm cmp_mem16_imm16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_mem16_imm16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
