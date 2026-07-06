; Proofs about a 1-instruction binary that NOTs a general register (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_rbx_64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_rbx_64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function not_rbx_64, which
;; represents the effect of the program on the x86 state.
;; NOT RBX is encoded as 48 F7 D3 (3 bytes), so stop PC = 0x401003.
(def-unrolled not_rbx_64
  :executable "not_rbx_64.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX after the operation: the natural 64-bit statement of the result.
(defthm not_rbx_64-rbx
  (equal (rbx (not_rbx_64 x86))
         (bvnot 64 (rbx x86))))

;; The RIP is advanced by 3 (NOT RBX is 3 bytes: REX.W F7 D3 = 48 F7 D3)
(defthm not_rbx_64-rip
  (equal (rip (not_rbx_64 x86))
         (+ 3 #x401000)))

;; Registers other than RBX are unchanged.
(defthm not_rbx_64-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (not_rbx_64 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; All memory addresses are unchanged.
(defthm not_rbx_64-memory-unchanged
  (equal (memi address (not_rbx_64 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_rbx_64-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_rbx_64 x86))
                  (get-flag flag x86))))
