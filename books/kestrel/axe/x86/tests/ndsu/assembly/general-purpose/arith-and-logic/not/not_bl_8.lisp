; Proofs about a 1-instruction binary that NOTs a general register (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_bl_8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_bl_8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite bl to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm bl-rewrite
  (equal (bl x86) (bvchop 8 (rbx x86)))
  :hints (("Goal" :in-theory (enable bl rbx)))))

;; Lifts the subroutine into logic: Creates the function not_bl_8, which
;; represents the effect of the program on the x86 state.
;; NOT BL is encoded as F6 D3 (2 bytes), so stop PC = 0x401002.
(def-unrolled not_bl_8
  :executable "not_bl_8.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; BL after the operation: the natural 8-bit statement of the result.
;; (Intel SDM Vol 2A: DEST <- NOT DEST)
(defthm not_bl_8-bl
  (equal (bl (not_bl_8 x86))
         (bvnot 8 (bl x86))))

;; The RIP is advanced by 2 (NOT BL is 2 bytes: F6 D3)
(defthm not_bl_8-rip
  (equal (rip (not_bl_8 x86))
         (+ 2 #x401000)))

;; Registers other than RBX are unchanged.
(defthm not_bl_8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (not_bl_8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; All memory addresses are unchanged.
(defthm not_bl_8-memory-unchanged
  (equal (memi address (not_bl_8 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_bl_8-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_bl_8 x86))
                  (get-flag flag x86))))
