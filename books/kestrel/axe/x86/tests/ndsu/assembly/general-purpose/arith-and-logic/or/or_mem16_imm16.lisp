; Proofs about a 1-instruction binary that ORs a 16-bit immediate into a memory word
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_mem16_imm16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_mem16_imm16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function or_mem16_imm16, which
;; represents the effect of the program on the x86 state.
;; OR [RBX], 300 is encoded as 66 81 0B 2C 01 (5 bytes), so stop PC = 0x401005.
;; Both the base address and +1 must be canonical for the 16-bit write.
(def-unrolled or_mem16_imm16
  :executable "or_mem16_imm16.elf64"
  :target #x401000
  :stop-pcs '(#x401005)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The word at memory address [RBX] is updated to the 16-bit OR of the original
;; word at [RBX] and the immediate 300 (Intel SDM Vol 2A: OR entry: DEST <- DEST OR SRC, size = word).
(defthm or_mem16_imm16-memory-at-rbx
  (equal (read 2 (rbx x86) (or_mem16_imm16 x86))
         (bvor 16 (read 2 (rbx x86) x86) 300)))

;; All other memory bytes are unchanged (only the 2 bytes at [RBX] and [RBX+1] are written).
;; Condition: address is not within the 2-byte region starting at [RBX].
(defthm or_mem16_imm16-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 2))
           (equal (read 1 address (or_mem16_imm16 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 5 (OR [RBX], 300 is 5 bytes: 66 81 0B 2C 01)
(defthm or_mem16_imm16-rip
  (equal (rip (or_mem16_imm16 x86))
         (+ 5 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm or_mem16_imm16-registers
  (equal (rgfi reg (or_mem16_imm16 x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A OR entry: CF is cleared to 0.
(defthm or_mem16_imm16-cf
  (equal (get-flag :cf (or_mem16_imm16 x86))
         0))

;; Intel SDM Vol 2A OR entry: OF is cleared to 0.
(defthm or_mem16_imm16-of
  (equal (get-flag :of (or_mem16_imm16 x86))
         0))

;; The zero flag is 1 iff the 16-bit OR result is 0.
(defthm or_mem16_imm16-zf
  (equal (get-flag :zf (or_mem16_imm16 x86))
         (if (equal 0 (bvor 16 (read 2 (rbx x86) x86) 300))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm or_mem16_imm16-sf
  (equal (get-flag :sf (or_mem16_imm16 x86))
         (getbit 15 (bvor 16 (read 2 (rbx x86) x86) 300)))
  :hints (("Goal" :in-theory (disable read-2-blast))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_mem16_imm16-pf
  (equal (get-flag :pf (or_mem16_imm16 x86))
         (if (evenp (bvcount 8 (bvor 16 (read 2 (rbx x86) x86) 300)))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec16-alt-def) (read-2-blast)))))

(defthm or_mem16_imm16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_mem16_imm16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
