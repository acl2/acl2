; Proofs about a 1-instruction binary that ORs a sign-extended 32-bit immediate into a memory qword
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_mem64_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_mem64_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function or_mem64_imm32, which
;; represents the effect of the program on the x86 state.
;; OR [RBX], 1000 is encoded as 48 81 0B E8 03 00 00 (7 bytes), so stop PC = 0x401007.
;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.
;; Both the base address and +7 must be canonical for the 64-bit write.
(def-unrolled or_mem64_imm32
  :executable "or_mem64_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401007)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RBX] is updated to the 64-bit OR of the original
;; qword at [RBX] and the sign-extended immediate 1000
;; (Intel SDM Vol 2A: OR entry: DEST <- DEST OR SignExtend(SRC), size = qword).
;; Since 1000 > 0 and 1000 < 2^31, sign extension leaves the value unchanged.
(defthm or_mem64_imm32-memory-at-rbx
  (equal (read 8 (rbx x86) (or_mem64_imm32 x86))
         (bvor 64 (read 8 (rbx x86) x86) 1000)))

;; All other memory bytes are unchanged (only the 8 bytes at [RBX]..[RBX+7] are written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm or_mem64_imm32-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (or_mem64_imm32 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 7 (OR [RBX], imm32 is 7 bytes: REX.W 81 0B E8 03 00 00)
(defthm or_mem64_imm32-rip
  (equal (rip (or_mem64_imm32 x86))
         (+ 7 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm or_mem64_imm32-registers
  (equal (rgfi reg (or_mem64_imm32 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A OR entry: CF is cleared to 0.
(defthm or_mem64_imm32-cf
  (equal (get-flag :cf (or_mem64_imm32 x86))
         0))

;; Intel SDM Vol 2A OR entry: OF is cleared to 0.
(defthm or_mem64_imm32-of
  (equal (get-flag :of (or_mem64_imm32 x86))
         0))

;; The zero flag is 1 iff the 64-bit OR result is 0.
(defthm or_mem64_imm32-zf
  (equal (get-flag :zf (or_mem64_imm32 x86))
         (if (equal 0 (bvor 64 (read 8 (rbx x86) x86) 1000))
             1
           0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm or_mem64_imm32-sf
  (equal (get-flag :sf (or_mem64_imm32 x86))
         (getbit 63 (bvor 64 (read 8 (rbx x86) x86) 1000))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_mem64_imm32-pf
  (equal (get-flag :pf (or_mem64_imm32 x86))
         (if (evenp (bvcount 8 (bvor 64 (read 8 (rbx x86) x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def))))

(defthm or_mem64_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_mem64_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
