; Proofs about a 1-instruction binary that ORs a memory dword into EAX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_eax_mem32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_eax_mem32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function or_eax_mem32, which
;; represents the effect of the program on the x86 state.
;; OR EAX, [RBX] is encoded as 0B 03 (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical for the 32-bit read.
(def-unrolled or_eax_mem32
  :executable "or_eax_mem32.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit OR result zero-extended to 64 bits (32-bit ops in 64-bit
;; mode always zero-extend the result to the full 64-bit register).
(defthm or_eax_mem32-rax
  (equal (rax (or_eax_mem32 x86))
         (bvor 32 (eax x86) (read 4 (rbx x86) x86))))

;; EAX contains the 32-bit OR result (the natural statement for this instruction).
(defthm or_eax_mem32-eax
  (equal (eax (or_eax_mem32 x86))
         (bvor 32 (eax x86) (read 4 (rbx x86) x86))))

;; The RIP is advanced by 2 (OR EAX, [RBX] is 2 bytes: 0B 03)
(defthm or_eax_mem32-rip
  (equal (rip (or_eax_mem32 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm or_eax_mem32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (or_eax_mem32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; Intel SDM Vol 2A OR entry: CF is cleared to 0.
(defthm or_eax_mem32-cf
  (equal (get-flag :cf (or_eax_mem32 x86))
         0))

;; Intel SDM Vol 2A OR entry: OF is cleared to 0.
(defthm or_eax_mem32-of
  (equal (get-flag :of (or_eax_mem32 x86))
         0))

;; The zero flag is 1 iff the 32-bit OR result is 0.
(defthm or_eax_mem32-zf
  (equal (get-flag :zf (or_eax_mem32 x86))
         (if (equal 0 (bvor 32 (eax x86) (read 4 (rbx x86) x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm or_eax_mem32-sf
  (equal (get-flag :sf (or_eax_mem32 x86))
         (getbit 31 (bvor 32 (eax x86) (read 4 (rbx x86) x86)))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_eax_mem32-pf
  (equal (get-flag :pf (or_eax_mem32 x86))
         (if (evenp (bvcount 8 (bvor 32 (eax x86) (read 4 (rbx x86) x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

;; All memory addresses are unchanged (instruction reads from memory but does not write).
(defthm or_eax_mem32-memory-unchanged
  (equal (memi address (or_eax_mem32 x86))
         (memi address x86)))

(defthm or_eax_mem32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_eax_mem32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
