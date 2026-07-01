; Proofs about a 1-instruction binary that subtracts an 8-bit immediate from a memory byte
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_mem8_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_mem8_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sub_mem8_imm8, which
;; represents the effect of the program on the x86 state.
;; SUB [RBX], 5 is encoded as 80 2B 05 (3 bytes), so stop PC = 0x401003.
;; The base address must be canonical for the x86 model to perform the memory
;; write at [RBX] without an error branch.
(def-unrolled sub_mem8_imm8
  :executable "sub_mem8_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [RBX] is updated to the 8-bit difference of the original
;; byte at [RBX] minus 5 (Intel SDM Vol 2A: DEST <- DEST - SRC, size = byte).
(defthm sub_mem8_imm8-memory-at-rbx
  (equal (read 1 (rbx x86) (sub_mem8_imm8 x86))
         (bvminus 8 (read 1 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the byte at [RBX] is written).
(defthm sub_mem8_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 1))
           (equal (read 1 address (sub_mem8_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (SUB [RBX], 5 is 3 bytes: 80 2B 05)
(defthm sub_mem8_imm8-rip
  (equal (rip (sub_mem8_imm8 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sub_mem8_imm8-registers
  (equal (rgfi reg (sub_mem8_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff 5 > mem[RBX] unsigned (borrow):
(defthm sub_mem8_imm8-cf
  (equal (get-flag :cf (sub_mem8_imm8 x86))
         (if (bvlt 8 (read 1 (rbx x86) x86) 5) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_mem8_imm8-zf
  (equal (get-flag :zf (sub_mem8_imm8 x86))
         (if (equal 0 (bvminus 8 (read 1 (rbx x86) x86) 5)) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec8 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result:
(defthm sub_mem8_imm8-sf
  (equal (get-flag :sf (sub_mem8_imm8 x86))
         (getbit 7 (bvminus 8 (read 1 (rbx x86) x86) 5)))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < 5:
(defthm sub_mem8_imm8-af
  (equal (get-flag :af (sub_mem8_imm8 x86))
         (if (< (bvchop 4 (read 1 (rbx x86) x86))
                5)
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvlt bvminus acl2::bvchop-of-sum-cases) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

;; The overflow flag is 1 iff the signed 8-bit result overflows:
(defthm sub_mem8_imm8-of
  (equal (get-flag :of (sub_mem8_imm8 x86))
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

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_mem8_imm8-pf
  (equal (get-flag :pf (sub_mem8_imm8 x86))
         (let ((diff (bvminus 8 (read 1 (rbx x86) x86) 5)))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (e/d (sub-pf-spec8-to-bvcount) (acl2::bvminus-becomes-bvplus-of-bvuminus-constant-version)))))

(defthm sub_mem8_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_mem8_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
