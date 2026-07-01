; Proofs about a 1-instruction binary that ORs a sign-extended 8-bit immediate to a memory dword
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_mem32_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_mem32_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function or_mem32_imm8, which
;; represents the effect of the program on the x86 state.
;; OR [RBX], 5 is encoded as 83 0B 05 (3 bytes), so stop PC = 0x401003.
;; The immediate 5 is sign-extended from 8 to 32 bits before the OR;
;; since 5 > 0 and 5 < 128, sign extension leaves its value unchanged.
;; Both the base address and +3 must be canonical for the 32-bit write.
(def-unrolled or_mem32_imm8
  :executable "or_mem32_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The dword at memory address [RBX] is updated to the 32-bit OR of the original
;; dword at [RBX] and SignExtend(5) = 5
;; (Intel SDM Vol 2A: DEST <- DEST OR SignExtend(SRC), size = dword).
(defthm or_mem32_imm8-memory-at-rbx
  (equal (read 4 (rbx x86) (or_mem32_imm8 x86))
         (bvor 32 (read 4 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the 4 bytes at [RBX]..[RBX+3] are written).
;; Condition: address is not within the 4-byte region starting at [RBX].
(defthm or_mem32_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 4))
           (equal (read 1 address (or_mem32_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (OR [RBX], 5 is 3 bytes: 83 0B 05)
(defthm or_mem32_imm8-rip
  (equal (rip (or_mem32_imm8 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm or_mem32_imm8-registers
  (equal (rgfi reg (or_mem32_imm8 x86))
         (rgfi reg x86)))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: OR clears CF).
(defthm or_mem32_imm8-cf
  (equal (get-flag :cf (or_mem32_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: OR clears OF).
(defthm or_mem32_imm8-of
  (equal (get-flag :of (or_mem32_imm8 x86))
         0))

;; The zero flag is 1 iff the OR result is 0.
(defthm or_mem32_imm8-zf
  (equal (get-flag :zf (or_mem32_imm8 x86))
         (if (equal 0 (bvor 32 (read 4 (rbx x86) x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm or_mem32_imm8-sf
  (equal (get-flag :sf (or_mem32_imm8 x86))
         (getbit 31 (bvor 32 (read 4 (rbx x86) x86) 5))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_mem32_imm8-pf
  (equal (get-flag :pf (or_mem32_imm8 x86))
         (if (evenp (bvcount 8 (bvor 32 (read 4 (rbx x86) x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

(defthm or_mem32_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_mem32_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
