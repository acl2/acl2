; Proofs about a 1-instruction binary that XORs a sign-extended 8-bit immediate to a memory qword
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_mem64_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_mem64_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function xor_mem64_imm8, which
;; represents the effect of the program on the x86 state.
;; XOR [RBX], 5 is encoded as 48 83 33 05 (4 bytes), so stop PC = 0x401004.
;; The immediate 5 is sign-extended from 8 to 64 bits before the XOR;
;; since 5 > 0 and 5 < 128, sign extension leaves its value unchanged.
;; Both the base address and +7 must be canonical for the 64-bit write.
(def-unrolled xor_mem64_imm8
  :executable "xor_mem64_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RBX] is updated to the 64-bit XOR of the original
;; qword at [RBX] and SignExtend(5) = 5
;; (Intel SDM Vol 2A: DEST <- DEST XOR SignExtend(SRC), size = qword).
(defthm xor_mem64_imm8-memory-at-rbx
  (equal (read 8 (rbx x86) (xor_mem64_imm8 x86))
         (bvxor 64 (read 8 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the 8 bytes at [RBX]..[RBX+7] are written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm xor_mem64_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (xor_mem64_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 4 (XOR [RBX], 5 is 4 bytes: REX.W 83 33 05)
(defthm xor_mem64_imm8-rip
  (equal (rip (xor_mem64_imm8 x86))
         (+ 4 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm xor_mem64_imm8-registers
  (equal (rgfi reg (xor_mem64_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: XOR clears CF).
(defthm xor_mem64_imm8-cf
  (equal (get-flag :cf (xor_mem64_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: XOR clears OF).
(defthm xor_mem64_imm8-of
  (equal (get-flag :of (xor_mem64_imm8 x86))
         0))

;; The zero flag is 1 iff the XOR result is 0.
(defthm xor_mem64_imm8-zf
  (equal (get-flag :zf (xor_mem64_imm8 x86))
         (if (equal 0 (bvxor 64 (read 8 (rbx x86) x86) 5))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm xor_mem64_imm8-sf
  (equal (get-flag :sf (xor_mem64_imm8 x86))
         (getbit 63 (bvxor 64 (read 8 (rbx x86) x86) 5))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_mem64_imm8-pf
  (equal (get-flag :pf (xor_mem64_imm8 x86))
         (if (evenp (bvcount 8 (bvxor 64 (read 8 (rbx x86) x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec64-alt-def)
                                   (acl2::bvxor-with-smaller-arg-1
                                    acl2::bvxor-with-smaller-arg-2)))))

(defthm xor_mem64_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_mem64_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
