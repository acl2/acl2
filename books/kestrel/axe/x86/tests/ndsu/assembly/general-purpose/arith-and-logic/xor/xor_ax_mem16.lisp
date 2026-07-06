; Proofs about a 1-instruction binary that XORs AX with a memory word (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_ax_mem16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_ax_mem16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function xor_ax_mem16, which
;; represents the effect of the program on the x86 state.
;; XOR AX, [RBX] is encoded as 66 33 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical for the 16-bit read.
(def-unrolled xor_ax_mem16
  :executable "xor_ax_mem16.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the 16-bit XOR result;
;; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm xor_ax_mem16-rax
  (equal (rax (xor_ax_mem16 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvxor 16 (rax x86) (read 2 (rbx x86) x86)))))

;; AX after the operation: the natural 16-bit statement of the result.
(defthm xor_ax_mem16-ax
  (equal (ax (xor_ax_mem16 x86))
         (bvxor 16 (ax x86) (read 2 (rbx x86) x86))))

;; The RIP is advanced by 3 (XOR AX, [RBX] is 3 bytes: 66 33 03)
(defthm xor_ax_mem16-rip
  (equal (rip (xor_ax_mem16 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm xor_ax_mem16-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (xor_ax_mem16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: XOR clears CF).
(defthm xor_ax_mem16-cf
  (equal (get-flag :cf (xor_ax_mem16 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: XOR clears OF).
(defthm xor_ax_mem16-of
  (equal (get-flag :of (xor_ax_mem16 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm xor_ax_mem16-zf
  (equal (get-flag :zf (xor_ax_mem16 x86))
         (if (equal 0 (bvxor 16 (ax x86) (read 2 (rbx x86) x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm xor_ax_mem16-sf
  (equal (get-flag :sf (xor_ax_mem16 x86))
         (getbit 15 (bvxor 16 (ax x86) (read 2 (rbx x86) x86))))
  :hints (("Goal" :in-theory (disable read-2-blast))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_ax_mem16-pf
  (equal (get-flag :pf (xor_ax_mem16 x86))
         (if (evenp (bvcount 8 (bvxor 16 (ax x86) (read 2 (rbx x86) x86))))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec16-alt-def) (read-2-blast)))))

;; All memory addresses are unchanged (instruction reads from memory but does not write)
(defthm xor_ax_mem16-memory-unchanged
  (equal (memi address (xor_ax_mem16 x86))
         (memi address x86)))

(defthm xor_ax_mem16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_ax_mem16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
