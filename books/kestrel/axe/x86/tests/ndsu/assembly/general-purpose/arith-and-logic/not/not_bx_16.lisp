; Proofs about a 1-instruction binary that NOTs a general register (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of not_bx_16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "not_bx_16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite bx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm bx-rewrite
  (equal (bx x86) (bvchop 16 (rbx x86)))
  :hints (("Goal" :in-theory (enable bx rbx)))))

;; Lifts the subroutine into logic: Creates the function not_bx_16, which
;; represents the effect of the program on the x86 state.
;; NOT BX is encoded as 66 F7 D3 (3 bytes), so stop PC = 0x401003.
(def-unrolled not_bx_16
  :executable "not_bx_16.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX after the operation: only BX (bits 0-15) is updated to the NOT result;
;; bits 16-63 of RBX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm not_bx_16-rbx
  (equal (rbx (not_bx_16 x86))
         (bvcat 48 (slice 63 16 (rbx x86)) 16 (bvnot 16 (rbx x86)))))

;; BX after the operation: the natural 16-bit statement of the result.
(defthm not_bx_16-bx
  (equal (bx (not_bx_16 x86))
         (bvnot 16 (bx x86))))

;; The RIP is advanced by 3 (NOT BX is 3 bytes: 66 F7 D3)
(defthm not_bx_16-rip
  (equal (rip (not_bx_16 x86))
         (+ 3 #x401000)))

;; Registers other than RBX are unchanged.
(defthm not_bx_16-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (not_bx_16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; All memory addresses are unchanged.
(defthm not_bx_16-memory-unchanged
  (equal (memi address (not_bx_16 x86))
         (memi address x86)))

;; Intel SDM Vol 1 Sec 3.4.3.1 / Vol 2A NOT entry: NOT affects no flags.
;; All flags (CF, OF, SF, ZF, AF, PF, and any others) are unchanged.
(defthm not_bx_16-flags-unchanged
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (not_bx_16 x86))
                  (get-flag flag x86))))
