; Proofs about a 1-instruction binary that XORs a 32-bit immediate into a memory dword
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_mem32_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_mem32_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function xor_mem32_imm32, which
;; represents the effect of the program on the x86 state.
;; XOR [RBX], 1000 is encoded as 81 33 E8 03 00 00 (6 bytes), so stop PC = 0x401006.
;; Both the base address and +3 must be canonical for the 32-bit write.
(def-unrolled xor_mem32_imm32
  :executable "xor_mem32_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401006)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The dword at memory address [RBX] is updated to the 32-bit XOR of the original
;; dword at [RBX] and the immediate 1000 (Intel SDM Vol 2A: XOR entry: DEST <- DEST XOR SRC, size = dword).
(defthm xor_mem32_imm32-memory-at-rbx
  (equal (read 4 (rbx x86) (xor_mem32_imm32 x86))
         (bvxor 32 (read 4 (rbx x86) x86) 1000)))

;; All other memory bytes are unchanged (only the 4 bytes at [RBX]..[RBX+3] are written).
;; Condition: address is not within the 4-byte region starting at [RBX].
(defthm xor_mem32_imm32-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 4))
           (equal (read 1 address (xor_mem32_imm32 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 6 (XOR [RBX], 1000 is 6 bytes: 81 33 E8 03 00 00)
(defthm xor_mem32_imm32-rip
  (equal (rip (xor_mem32_imm32 x86))
         (+ 6 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm xor_mem32_imm32-registers
  (equal (rgfi reg (xor_mem32_imm32 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A XOR entry: CF is cleared to 0.
(defthm xor_mem32_imm32-cf
  (equal (get-flag :cf (xor_mem32_imm32 x86))
         0))

;; Intel SDM Vol 2A XOR entry: OF is cleared to 0.
(defthm xor_mem32_imm32-of
  (equal (get-flag :of (xor_mem32_imm32 x86))
         0))

;; The zero flag is 1 iff the 32-bit XOR result is 0.
(defthm xor_mem32_imm32-zf
  (equal (get-flag :zf (xor_mem32_imm32 x86))
         (if (equal 0 (bvxor 32 (read 4 (rbx x86) x86) 1000))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm xor_mem32_imm32-sf
  (equal (get-flag :sf (xor_mem32_imm32 x86))
         (getbit 31 (bvxor 32 (read 4 (rbx x86) x86) 1000))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_mem32_imm32-pf
  (equal (get-flag :pf (xor_mem32_imm32 x86))
         (if (evenp (bvcount 8 (bvxor 32 (read 4 (rbx x86) x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec32-alt-def)
                                   (acl2::bvxor-with-smaller-arg-1
                                    acl2::bvxor-with-smaller-arg-2)))))

(defthm xor_mem32_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_mem32_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
