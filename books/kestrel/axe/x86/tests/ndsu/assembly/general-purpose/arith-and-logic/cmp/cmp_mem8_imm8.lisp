; Proofs about a 1-instruction binary that compares a memory byte to an 8-bit immediate
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_mem8_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_mem8_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function cmp_mem8_imm8, which
;; represents the effect of the program on the x86 state.
;; CMP [RBX], 5 is encoded as 80 3B 05 (3 bytes), so stop PC = 0x401003.
;; The base address must be canonical for the x86 model to perform the memory
;; read at [RBX] without an error branch.
(def-unrolled cmp_mem8_imm8
  :executable "cmp_mem8_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 3 (CMP [RBX], 5 is 3 bytes: 80 3B 05)
(defthm cmp_mem8_imm8-rip
  (equal (rip (cmp_mem8_imm8 x86))
         (+ 3 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST (memory) is not updated, so
;; all memory is unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_mem8_imm8-memory-unchanged
  (equal (memi address (cmp_mem8_imm8 x86))
         (memi address x86)))

;; All registers are unchanged (CMP does not write to any register either).
(defthm cmp_mem8_imm8-registers
  (equal (rgfi reg (cmp_mem8_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 5 > mem[RBX] unsigned (borrow):
(defthm cmp_mem8_imm8-cf
  (equal (get-flag :cf (cmp_mem8_imm8 x86))
         (if (bvlt 8 (read 1 (rbx x86) x86) 5) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_mem8_imm8-zf
  (equal (get-flag :zf (cmp_mem8_imm8 x86))
         (if (equal 0 (bvminus 8 (read 1 (rbx x86) x86) 5)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec8 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 7) of the 8-bit difference:
(defthm cmp_mem8_imm8-sf
  (equal (get-flag :sf (cmp_mem8_imm8 x86))
         (getbit 7 (bvminus 8 (read 1 (rbx x86) x86) 5)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < 5:
(defthm cmp_mem8_imm8-af
  (equal (get-flag :af (cmp_mem8_imm8 x86))
         (if (< (bvchop 4 (read 1 (rbx x86) x86))
                5)
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 8-bit difference overflows:
(defthm cmp_mem8_imm8-of
  (equal (get-flag :of (cmp_mem8_imm8 x86))
         (let ((diff (- (logext 8 (read 1 (rbx x86) x86)) 5)))
           (if (or (< diff (- (expt 2 7)))
                   (<= (expt 2 7) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

(local (defthm sub-pf-spec8-to-bvcount
  (equal (sub-pf-spec8 dst src)
         (if (evenp (bvcount 8 (bvminus 8 dst src))) 1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvchop-of-logext-same
                                     acl2::bvchop-of-minus-of-logext-gen
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_mem8_imm8-pf
  (equal (get-flag :pf (cmp_mem8_imm8 x86))
         (let ((diff (bvminus 8 (read 1 (rbx x86) x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (e/d (sub-pf-spec8-to-bvcount) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

(defthm cmp_mem8_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_mem8_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
