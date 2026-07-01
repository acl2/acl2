; Proofs about a 1-instruction binary that ANDs RAX into a memory qword (64-bit reg-to-mem)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_mem64_rax.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_mem64_rax.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function and_mem64_rax, which
;; represents the effect of the program on the x86 state.
;; AND [RBX], RAX is encoded as 48 21 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit write.
(def-unrolled and_mem64_rax
  :executable "and_mem64_rax.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RBX] is updated to the 64-bit AND of the original
;; qword at [RBX] and RAX (Intel SDM Vol 2A: AND entry: DEST <- DEST AND SRC, size = qword).
(defthm and_mem64_rax-memory-at-rbx
  (equal (read 8 (rbx x86) (and_mem64_rax x86))
         (bvand 64 (read 8 (rbx x86) x86) (rax x86))))

;; All other memory bytes are unchanged (only the 8 bytes at [RBX]..[RBX+7] are written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm and_mem64_rax-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (and_mem64_rax x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (AND [RBX], RAX is 3 bytes: REX.W 21 03 = 48 21 03)
(defthm and_mem64_rax-rip
  (equal (rip (and_mem64_rax x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm and_mem64_rax-registers
  (equal (rgfi reg (and_mem64_rax x86))
         (rgfi reg x86)))

;; Intel SDM Vol 2A AND entry: CF is cleared to 0.
(defthm and_mem64_rax-cf
  (equal (get-flag :cf (and_mem64_rax x86))
         0))

;; Intel SDM Vol 2A AND entry: OF is cleared to 0.
(defthm and_mem64_rax-of
  (equal (get-flag :of (and_mem64_rax x86))
         0))

;; The zero flag is 1 iff the 64-bit AND result is 0.
(defthm and_mem64_rax-zf
  (equal (get-flag :zf (and_mem64_rax x86))
         (if (equal 0 (bvand 64 (read 8 (rbx x86) x86) (rax x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm and_mem64_rax-sf
  (equal (get-flag :sf (and_mem64_rax x86))
         (getbit 63 (bvand 64 (read 8 (rbx x86) x86) (rax x86)))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_mem64_rax-pf
  (equal (get-flag :pf (and_mem64_rax x86))
         (if (evenp (bvcount 8 (bvand 64 (read 8 (rbx x86) x86) (rax x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def))))

(defthm and_mem64_rax-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_mem64_rax x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
