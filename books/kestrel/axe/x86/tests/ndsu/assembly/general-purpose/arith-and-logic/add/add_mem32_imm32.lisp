; Proofs about a 1-instruction binary that adds a 32-bit immediate to a memory dword
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_mem32_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_mem32_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add_mem32_imm32, which
;; represents the effect of the program on the x86 state.
;; ADD [RBX], 1000 is encoded as 81 03 E8 03 00 00 (6 bytes), so stop PC = 0x401006.
;; Both the base address and +3 must be canonical for the 32-bit write.
(def-unrolled add_mem32_imm32
  :executable "add_mem32_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401006)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The dword at memory address [RBX] is updated to the 32-bit sum of the original
;; dword at [RBX] and the immediate 1000 (Intel SDM Vol 2A: DEST <- DEST + SRC, size = dword).
(defthm add_mem32_imm32-memory-at-rbx
  (equal (read 4 (rbx x86) (add_mem32_imm32 x86))
         (bvplus 32 (read 4 (rbx x86) x86) 1000)))

;; All other memory bytes are unchanged (only the 4 bytes at [RBX]..[RBX+3] are
;; written).
;; Condition: address is not within the 4-byte region starting at [RBX].
(defthm add_mem32_imm32-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 4))
           (equal (read 1 address (add_mem32_imm32 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 6 (ADD [RBX], 1000 is 6 bytes: 81 03 E8 03 00 00)
(defthm add_mem32_imm32-rip
  (equal (rip (add_mem32_imm32 x86))
         (+ 6 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm add_mem32_imm32-registers
  (equal (rgfi reg (add_mem32_imm32 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff the 32-bit unsigned sum overflows (i.e., >= 2^32):
(defthm add_mem32_imm32-cf
  (equal (get-flag :cf (add_mem32_imm32 x86))
         (if (<= (expt 2 32)
                 (+ (read 4 (rbx x86) x86) 1000))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm add_mem32_imm32-zf
  (equal (get-flag :zf (add_mem32_imm32 x86))
         (if (equal 0 (bvplus 32 (read 4 (rbx x86) x86) 1000))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm add_mem32_imm32-sf
  (equal (get-flag :sf (add_mem32_imm32 x86))
         (getbit 31 (bvplus 32 (read 4 (rbx x86) x86) 1000)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibbles of the destination and 1000 exceeds 15):
(defthm add_mem32_imm32-af
  (equal (get-flag :af (add_mem32_imm32 x86))
         (if (> (+ (bvchop 4 (read 4 (rbx x86) x86))
                   (bvchop 4 1000))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 32-bit result overflows
(defthm add_mem32_imm32-of
  (equal (get-flag :of (add_mem32_imm32 x86))
         (let ((sum (+ (logext 32 (read 4 (rbx x86) x86))
                       1000)))
           (if (or (< sum (- (expt 2 31))) ; sum too small
                   (<= (expt 2 31) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec32 signed-byte-p))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_mem32_imm32-pf
  (equal (get-flag :pf (add_mem32_imm32 x86))
         (if (evenp (bvcount 8 (bvplus 32 (read 4 (rbx x86) x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvplus))))

(defthm add_mem32_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_mem32_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
