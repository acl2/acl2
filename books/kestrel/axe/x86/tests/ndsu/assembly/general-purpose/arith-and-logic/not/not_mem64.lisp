; Proofs about a 1-instruction binary that NOTs a memory qword (64-bit memory)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_mem64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_mem64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function not_mem64, which
;; represents the effect of the program on the x86 state.
;; NOT qword [RBX] is encoded as 48 F7 13 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit write.
(def-unrolled not_mem64
  :executable "not_mem64.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RBX] is updated to the 64-bit NOT of the original
;; qword at [RBX] (Intel SDM Vol 2A: NOT entry: DEST <- NOT DEST, size = qword).
(defthm not_mem64-memory-at-rbx
  (equal (read 8 (rbx x86) (not_mem64 x86))
         (bvnot 64 (read 8 (rbx x86) x86))))

;; All other memory bytes are unchanged (only the 8 bytes at [RBX]..[RBX+7] are written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm not_mem64-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (not_mem64 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (NOT [RBX] is 3 bytes: REX.W F7 13 = 48 F7 13)
(defthm not_mem64-rip
  (equal (rip (not_mem64 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm not_mem64-registers
  (equal (rgfi reg (not_mem64 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_mem64-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_mem64 x86))
                  (get-flag flag x86))))
