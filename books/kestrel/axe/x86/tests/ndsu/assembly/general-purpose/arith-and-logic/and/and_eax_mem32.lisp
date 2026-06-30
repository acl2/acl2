; Proofs about a 1-instruction binary that ANDs a memory dword into EAX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_eax_mem32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_eax_mem32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function and_eax_mem32, which
;; represents the effect of the program on the x86 state.
;; AND EAX, [RBX] is encoded as 23 03 (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical for the 32-bit read.
(def-unrolled and_eax_mem32
  :executable "and_eax_mem32.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit AND result zero-extended to 64 bits (32-bit ops in 64-bit
;; mode always zero-extend the result to the full 64-bit register).
(defthm and_eax_mem32-rax
  (equal (rax (and_eax_mem32 x86))
         (bvand 32 (eax x86) (read 4 (rbx x86) x86))))

;; EAX contains the 32-bit AND result (the natural statement for this instruction).
(defthm and_eax_mem32-eax
  (equal (eax (and_eax_mem32 x86))
         (bvand 32 (eax x86) (read 4 (rbx x86) x86))))

;; The RIP is advanced by 2 (AND EAX, [RBX] is 2 bytes: 23 03)
(defthm and_eax_mem32-rip
  (equal (rip (and_eax_mem32 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm and_eax_mem32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (and_eax_mem32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; Intel SDM Vol 2A AND entry: CF is cleared to 0.
(defthm and_eax_mem32-cf
  (equal (get-flag :cf (and_eax_mem32 x86))
         0))

;; Intel SDM Vol 2A AND entry: OF is cleared to 0.
(defthm and_eax_mem32-of
  (equal (get-flag :of (and_eax_mem32 x86))
         0))

;; The zero flag is 1 iff the 32-bit AND result is 0.
(defthm and_eax_mem32-zf
  (equal (get-flag :zf (and_eax_mem32 x86))
         (if (equal 0 (bvand 32 (eax x86) (read 4 (rbx x86) x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm and_eax_mem32-sf
  (equal (get-flag :sf (and_eax_mem32 x86))
         (getbit 31 (bvand 32 (eax x86) (read 4 (rbx x86) x86)))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_eax_mem32-pf
  (equal (get-flag :pf (and_eax_mem32 x86))
         (if (evenp (bvcount 8 (bvand 32 (eax x86) (read 4 (rbx x86) x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

;; All memory addresses are unchanged (instruction reads from memory but does not write).
(defthm and_eax_mem32-memory-unchanged
  (equal (memi address (and_eax_mem32 x86))
         (memi address x86)))

(defthm and_eax_mem32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_eax_mem32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
