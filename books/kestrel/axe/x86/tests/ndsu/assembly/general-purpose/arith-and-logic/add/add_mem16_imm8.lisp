; Proofs about a 1-instruction binary that adds a sign-extended 8-bit immediate to a memory word
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_mem16_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_mem16_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add_mem16_imm8, which
;; represents the effect of the program on the x86 state.
;; ADD [RBX], 5 is encoded as 66 83 03 05 (4 bytes), so stop PC = 0x401004.
;; The immediate 5 is sign-extended from 8 to 16 bits before the addition;
;; since 5 > 0 and 5 < 128, sign extension leaves its value unchanged.
;; Both the base address and +1 must be canonical for the 16-bit write.
(def-unrolled add_mem16_imm8
  :executable "add_mem16_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The word at memory address [RBX] is updated to the 16-bit sum of the original
;; word at [RBX] and SignExtend(5) = 5
;; (Intel SDM Vol 2A: DEST <- DEST + SignExtend(SRC), size = word).
(defthm add_mem16_imm8-memory-at-rbx
  (equal (read 2 (rbx x86) (add_mem16_imm8 x86))
         (bvplus 16 (read 2 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the 2 bytes at [RBX] and [RBX+1]
;; are written).
;; Condition: address is not within the 2-byte region starting at [RBX].
(defthm add_mem16_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 2))
           (equal (read 1 address (add_mem16_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 4 (ADD [RBX], 5 is 4 bytes: 66 83 03 05)
(defthm add_mem16_imm8-rip
  (equal (rip (add_mem16_imm8 x86))
         (+ 4 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm add_mem16_imm8-registers
  (equal (rgfi reg (add_mem16_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff the 16-bit unsigned sum overflows (i.e., >= 2^16):
(defthm add_mem16_imm8-cf
  (equal (get-flag :cf (add_mem16_imm8 x86))
         (if (<= (expt 2 16)
                 (+ (read 2 (rbx x86) x86) 5))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 16 bits, is 0
(defthm add_mem16_imm8-zf
  (equal (get-flag :zf (add_mem16_imm8 x86))
         (if (equal 0 (bvplus 16 (read 2 (rbx x86) x86) 5))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm add_mem16_imm8-sf
  (equal (get-flag :sf (add_mem16_imm8 x86))
         (let ((sum (bvplus 16 (read 2 (rbx x86) x86) 5)))
           (getbit 15 sum)))
  :hints (("Goal" :in-theory (disable read-2-blast))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibble of the destination and 5 exceeds 15):
(defthm add_mem16_imm8-af
  (equal (get-flag :af (add_mem16_imm8 x86))
         (if (> (+ (bvchop 4 (read 2 (rbx x86) x86))
                   5)
                15)
             1
           0))
  :hints (("Goal" :in-theory (e/d (bvplus bvlt) (read-2-blast)))))

;; The overflow flag is 1 iff the signed 16-bit result overflows
(defthm add_mem16_imm8-of
  (equal (get-flag :of (add_mem16_imm8 x86))
         (let ((sum (+ (logext 16 (read 2 (rbx x86) x86))
                       5)))
           (if (or (< sum (- (expt 2 15))) ; sum too small
                   (<= (expt 2 15) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec16 signed-byte-p))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_mem16_imm8-pf
  (equal (get-flag :pf (add_mem16_imm8 x86))
         (let ((sum (bvplus 16 (read 2 (rbx x86) x86) 5)))
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (e/d (pf-spec16-alt-def bvplus) (read-2-blast)))))

(defthm add_mem16_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_mem16_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
