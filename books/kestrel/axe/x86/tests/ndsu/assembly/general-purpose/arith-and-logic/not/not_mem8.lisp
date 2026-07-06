; Proofs about a 1-instruction binary that NOTs a memory byte (8-bit memory)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_mem8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_mem8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function not_mem8, which
;; represents the effect of the program on the x86 state.
;; NOT byte [RBX] is encoded as F6 13 (2 bytes), so stop PC = 0x401002.
;; The base address must be canonical for the x86 model to perform the memory
;; write at [RBX] without an error branch.
(def-unrolled not_mem8
  :executable "not_mem8.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [RBX] is updated to the 8-bit NOT of the original
;; byte at [RBX] (Intel SDM Vol 2A: NOT entry: DEST <- NOT DEST, size = byte).
(defthm not_mem8-memory-at-rbx
  (equal (read 1 (rbx x86) (not_mem8 x86))
         (bvnot 8 (read 1 (rbx x86) x86))))

;; All other memory bytes are unchanged (only the byte at [RBX] is written).
;; Condition: address is not within the 1-byte region starting at [RBX].
(defthm not_mem8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 1))
           (equal (read 1 address (not_mem8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 2 (NOT [RBX] is 2 bytes: F6 13)
(defthm not_mem8-rip
  (equal (rip (not_mem8 x86))
         (+ 2 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm not_mem8-registers
  (equal (rgfi reg (not_mem8 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_mem8-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_mem8 x86))
                  (get-flag flag x86))))
