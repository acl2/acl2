; Proofs about a 1-instruction binary that NOTs a general register (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_ebx_32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_ebx_32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite ebx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function not_ebx_32, which
;; represents the effect of the program on the x86 state.
;; NOT EBX is encoded as F7 D3 (2 bytes), so stop PC = 0x401002.
(def-unrolled not_ebx_32
  :executable "not_ebx_32.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 32-bit NOT result zero-extended to 64 bits
;; (32-bit ops in 64-bit mode always zero-extend the result).
(defthm not_ebx_32-rbx
  (equal (rbx (not_ebx_32 x86))
         (bvnot 32 (ebx x86))))

;; EBX contains the 32-bit NOT result (the natural statement for this instruction).
(defthm not_ebx_32-ebx
  (equal (ebx (not_ebx_32 x86))
         (bvnot 32 (ebx x86))))

;; The RIP is advanced by 2 (NOT EBX is 2 bytes: F7 D3)
(defthm not_ebx_32-rip
  (equal (rip (not_ebx_32 x86))
         (+ 2 #x401000)))

;; Registers other than RBX are unchanged.
(defthm not_ebx_32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (not_ebx_32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; All memory addresses are unchanged.
(defthm not_ebx_32-memory-unchanged
  (equal (memi address (not_ebx_32 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_ebx_32-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_ebx_32 x86))
                  (get-flag flag x86))))
