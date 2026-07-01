; Proofs about a 1-instruction binary that ANDs an 8-bit immediate into a memory byte
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_mem8_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_mem8_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function and_mem8_imm8, which
;; represents the effect of the program on the x86 state.
;; AND [RBX], 5 is encoded as 80 23 05 (3 bytes), so stop PC = 0x401003.
;; The base address must be canonical for the x86 model to perform the memory
;; write at [RBX] without an error branch.
(def-unrolled and_mem8_imm8
  :executable "and_mem8_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [RBX] is updated to the 8-bit AND of the original
;; byte at [RBX] and the immediate 5 (Intel SDM Vol 2A: AND entry: DEST <- DEST AND SRC, size = byte).
(defthm and_mem8_imm8-memory-at-rbx
  (equal (read 1 (rbx x86) (and_mem8_imm8 x86))
         (bvand 8 (read 1 (rbx x86) x86) 5)))

;; All other memory bytes are unchanged (only the byte at [RBX] is written).
;; Condition: address is not within the 1-byte region starting at [RBX].
(defthm and_mem8_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 1))
           (equal (read 1 address (and_mem8_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (AND [RBX], 5 is 3 bytes: 80 23 05)
(defthm and_mem8_imm8-rip
  (equal (rip (and_mem8_imm8 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm and_mem8_imm8-registers
  (equal (rgfi reg (and_mem8_imm8 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A AND entry: CF is cleared to 0.
(defthm and_mem8_imm8-cf
  (equal (get-flag :cf (and_mem8_imm8 x86))
         0))

;; Intel SDM Vol 2A AND entry: OF is cleared to 0.
(defthm and_mem8_imm8-of
  (equal (get-flag :of (and_mem8_imm8 x86))
         0))

;; The zero flag is 1 iff the 8-bit AND result is 0.
(defthm and_mem8_imm8-zf
  (equal (get-flag :zf (and_mem8_imm8 x86))
         (if (equal 0 (bvand 8 (read 1 (rbx x86) x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm and_mem8_imm8-sf
  (equal (get-flag :sf (and_mem8_imm8 x86))
         (getbit 7 (bvand 8 (read 1 (rbx x86) x86) 5))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_mem8_imm8-pf
  (equal (get-flag :pf (and_mem8_imm8 x86))
         (if (evenp (bvcount 8 (bvand 8 (read 1 (rbx x86) x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec8
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

(defthm and_mem8_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_mem8_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
