; Proofs about a 1-instruction binary that NOTs a register (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_ax_16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_ax_16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function not_ax_16, which
;; represents the effect of the program on the x86 state.
;; NOT AX is encoded as 66 F7 D0 (3 bytes), so stop PC = 0x401003.
(def-unrolled not_ax_16
  :executable "not_ax_16.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the NOT result;
;; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm not_ax_16-rax
  (equal (rax (not_ax_16 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvnot 16 (rax x86)))))

;; AX after the operation: the natural 16-bit statement of the result.
(defthm not_ax_16-ax
  (equal (ax (not_ax_16 x86))
         (bvnot 16 (ax x86))))

;; The RIP is advanced by 3 (NOT AX is 3 bytes: 66 F7 D0)
(defthm not_ax_16-rip
  (equal (rip (not_ax_16 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm not_ax_16-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (not_ax_16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; All memory addresses are unchanged.
(defthm not_ax_16-memory-unchanged
  (equal (memi address (not_ax_16 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_ax_16-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_ax_16 x86))
                  (get-flag flag x86))))
