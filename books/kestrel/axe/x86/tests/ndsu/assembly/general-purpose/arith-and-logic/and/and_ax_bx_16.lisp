; Proofs about a 1-instruction binary that ANDs 2 numbers (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_ax_bx_16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_ax_bx_16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax/bx to bvchop-of-rax/rbx so proofs reduce to the existing rax/rbx form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))
(local (defthm bx-rewrite
  (equal (bx x86) (bvchop 16 (rbx x86)))
  :hints (("Goal" :in-theory (enable bx rbx)))))

;; Lifts the subroutine into logic: Creates the function and_ax_bx_16, which
;; represents the effect of the program on the x86 state.
;; AND AX, BX is encoded as 66 21 D8 (3 bytes), so stop PC = 0x401003.
(def-unrolled and_ax_bx_16
  :executable "and_ax_bx_16.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the 16-bit AND result;
;; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm and_ax_bx_16-rax
  (equal (rax (and_ax_bx_16 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvand 16 (rax x86) (rbx x86)))))

;; AX after the operation: the natural 16-bit statement of the result.
(defthm and_ax_bx_16-ax
  (equal (ax (and_ax_bx_16 x86))
         (bvand 16 (ax x86) (bx x86))))

;; The RIP is advanced by 3 (AND AX,BX is 3 bytes: 66 21 D8)
(defthm and_ax_bx_16-rip
  (equal (rip (and_ax_bx_16 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm and_ax_bx_16-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (and_ax_bx_16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: AND clears CF).
(defthm and_ax_bx_16-cf
  (equal (get-flag :cf (and_ax_bx_16 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: AND clears OF).
(defthm and_ax_bx_16-of
  (equal (get-flag :of (and_ax_bx_16 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm and_ax_bx_16-zf
  (equal (get-flag :zf (and_ax_bx_16 x86))
         (if (equal 0 (bvand 16 (ax x86) (bx x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm and_ax_bx_16-sf
  (equal (get-flag :sf (and_ax_bx_16 x86))
         (getbit 15 (bvand 16 (ax x86) (bx x86)))))

(defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_ax_bx_16-pf
  (equal (get-flag :pf (and_ax_bx_16 x86))
         (if (evenp (bvcount 8 (bvand 16 (ax x86) (bx x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16-alt-def))))

;; All memory addresses are unchanged
(defthm and_ax_bx_16-memory-unchanged
  (equal (memi address (and_ax_bx_16 x86))
         (memi address x86)))

(defthm and_ax_bx_16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_ax_bx_16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
