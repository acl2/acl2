; Proofs about a 1-instruction binary that NOTs a register (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_eax_32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_eax_32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function not_eax_32, which
;; represents the effect of the program on the x86 state.
;; NOT EAX is encoded as F7 D0 (2 bytes), so stop PC = 0x401002.
(def-unrolled not_eax_32
  :executable "not_eax_32.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit NOT result zero-extended to 64 bits
;; (32-bit ops in 64-bit mode always zero-extend the result).
(defthm not_eax_32-rax
  (equal (rax (not_eax_32 x86))
         (bvnot 32 (eax x86))))

;; EAX contains the 32-bit NOT result (the natural statement for this instruction).
(defthm not_eax_32-eax
  (equal (eax (not_eax_32 x86))
         (bvnot 32 (eax x86))))

;; The RIP is advanced by 2 (NOT EAX is 2 bytes: F7 D0)
(defthm not_eax_32-rip
  (equal (rip (not_eax_32 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm not_eax_32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (not_eax_32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; All memory addresses are unchanged.
(defthm not_eax_32-memory-unchanged
  (equal (memi address (not_eax_32 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_eax_32-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_eax_32 x86))
                  (get-flag flag x86))))
