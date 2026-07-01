; Proofs about a 1-instruction binary that subtracts 2 numbers (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_ax_bx_16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_ax_bx_16.elf64")
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

;; Lifts the subroutine into logic: Creates the function sub_ax_bx_16, which
;; represents the effect of the program on the x86 state.
;; SUB AX, BX is encoded as 66 29 D8 (3 bytes), so stop PC = 0x401003.
(def-unrolled sub_ax_bx_16
  :executable "sub_ax_bx_16.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the 16-bit difference;
;; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm sub_ax_bx_16-rax
  (equal (rax (sub_ax_bx_16 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvminus 16 (rax x86) (rbx x86)))))

;; AX after the operation: DEST <- DEST - SRC (Intel SDM Vol 2A).
(defthm sub_ax_bx_16-ax
  (equal (ax (sub_ax_bx_16 x86))
         (bvminus 16 (ax x86) (bx x86))))

;; The RIP is advanced by 3 (SUB AX,BX is 3 bytes: 66 29 D8)
(defthm sub_ax_bx_16-rip
  (equal (rip (sub_ax_bx_16 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm sub_ax_bx_16-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (sub_ax_bx_16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is 1 iff the 16-bit subtraction borrows (unsigned src > unsigned dst):
(defthm sub_ax_bx_16-cf
  (equal (get-flag :cf (sub_ax_bx_16 x86))
         (if (bvlt 16 (ax x86) (bx x86)) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_ax_bx_16-zf
  (equal (get-flag :zf (sub_ax_bx_16 x86))
         (if (equal 0 (bvminus 16 (ax x86) (bx x86))) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec16 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result:
(defthm sub_ax_bx_16-sf
  (equal (get-flag :sf (sub_ax_bx_16 x86))
         (getbit 15 (bvminus 16 (ax x86) (bx x86))))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec16 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff there is a borrow from bit 4 into bit 3:
(defthm sub_ax_bx_16-af
  (equal (get-flag :af (sub_ax_bx_16 x86))
         (if (< (bvchop 4 (ax x86))
                (bvchop 4 (bx x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 16-bit result overflows:
(defthm sub_ax_bx_16-of
  (equal (get-flag :of (sub_ax_bx_16 x86))
         (let ((diff (- (logext 16 (ax x86))
                        (logext 16 (bx x86)))))
           (if (or (< diff (- (expt 2 15)))
                   (<= (expt 2 15) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec16 of-spec16 signed-byte-p))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_ax_bx_16-pf
  (equal (get-flag :pf (sub_ax_bx_16 x86))
         (let ((diff (bvminus 16 (ax x86) (bx x86))))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec16 pf-spec16-alt-def bvminus acl2::bvchop-of-sum-cases))))

;; All memory addresses are unchanged:
(defthm sub_ax_bx_16-memory-unchanged
  (equal (memi address (sub_ax_bx_16 x86))
         (memi address x86)))

(defthm sub_ax_bx_16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_ax_bx_16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
