; Proofs about a 1-instruction binary that NOTs a register (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_al_8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_al_8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the existing rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function not_al_8, which
;; represents the effect of the program on the x86 state.
;; NOT AL is encoded as F6 D0 (2 bytes), so stop PC = 0x401002.
(def-unrolled not_al_8
  :executable "not_al_8.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: DEST <- NOT DEST (Intel SDM Vol 2A: NOT entry).
(defthm not_al_8-al
  (equal (al (not_al_8 x86))
         (bvnot 8 (al x86))))

;; The RIP is advanced by 2 (NOT AL is 2 bytes: F6 D0)
(defthm not_al_8-rip
  (equal (rip (not_al_8 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm not_al_8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (not_al_8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; All memory addresses are unchanged.
(defthm not_al_8-memory-unchanged
  (equal (memi address (not_al_8 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_al_8-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_al_8 x86))
                  (get-flag flag x86))))
