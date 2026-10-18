; Proofs about a 1-instruction binary that executes LEAVE (66H-prefixed,
; 16-bit operand size, executed in 64-bit mode)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of leave_16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "leave_16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; The binary is: push bp; mov bp, sp; db 0x66; db 0xC9 (66H-prefixed LEAVE);
;; ret. (push/mov merely establish a stack frame at runtime; they are not
;; part of the lifted code.)
;; Per objdump, the 66H-prefixed LEAVE (66 C9, 2 bytes) is at 0x401005.
;;
;; Per the Intel SDM Operation pseudocode for LEAVE, the "RSP := RBP" step
;; and the "BP/EBP/RBP := Pop()" step are governed by two *independent*
;; attributes: StackAddressSize and OperandSize, respectively. Here we are
;; executing in 64-bit mode with only the 66H (operand-size) prefix, so
;; StackAddressSize is still 64 (no address-size override, 67H, is present):
;; the first step is "RSP := RBP" using the full 64-bit registers. The 66H
;; prefix sets OperandSize to 16, so the second step is "BP := Pop()": a
;; 2-byte pop, which updates only the low 16 bits of RBP and advances RSP by
;; 2 (not 8).
;; Lifts the subroutine into logic: Creates the function leave_16, which
;; represents the effect of the LEAVE instruction on the x86 state.
(def-unrolled leave_16
  :executable "leave_16.elf64"
  :target #x401005
  :stop-pcs '(#x401007)
  :extra-assumptions '((unsigned-canonical-address-p (rbp x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbp x86)))
                       (unsigned-canonical-address-p (bvplus 64 2 (rbp x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (StackAddressSize = 64, since only the 66H operand-size prefix
;; is present, not the 67H address-size prefix): RSP := RBP (full 64 bits).
;; Intel SDM (OperandSize = 16): BP := Pop(), which pops 2 bytes and thus
;; advances RSP by 2 from the value it just got (the old RBP).
(defthm leave_16-rsp
  (equal (rsp (leave_16 x86))
         (bvplus 64 (rbp x86) 2)))

;; Intel SDM (OperandSize = 16): BP := Pop() reads only 2 bytes, from the
;; address that RSP was just set to (the old RBP), and updates only the low
;; 16 bits of RBP; the upper 48 bits of RBP are left unchanged (stale).
(defthm leave_16-rbp
  (equal (rbp (leave_16 x86))
         (bvcat 48 (slice 63 16 (rbp x86))
                16 (read 2 (rbp x86) x86))))

;; Intel SDM: the 66H-prefixed LEAVE is 2 bytes (66 C9).
(defthm leave_16-rip
  (equal (rip (leave_16 x86))
         (+ 2 #x401005)))

;; Intel SDM: only RSP and RBP are modified; all other general-purpose
;; registers are unchanged.
(defthm leave_16-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (leave_16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;; Intel SDM: No flags are affected by LEAVE.
(defthm leave_16-cf
  (equal (get-flag :cf (leave_16 x86))
         (get-flag :cf x86)))

(defthm leave_16-zf
  (equal (get-flag :zf (leave_16 x86))
         (get-flag :zf x86)))

(defthm leave_16-sf
  (equal (get-flag :sf (leave_16 x86))
         (get-flag :sf x86)))

(defthm leave_16-of
  (equal (get-flag :of (leave_16 x86))
         (get-flag :of x86)))

(defthm leave_16-af
  (equal (get-flag :af (leave_16 x86))
         (get-flag :af x86)))

(defthm leave_16-pf
  (equal (get-flag :pf (leave_16 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm leave_16-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (leave_16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; Intel SDM: LEAVE reads memory (the popped BP) but does not write memory.
(defthm leave_16-memory-unchanged
  (equal (memi address (leave_16 x86))
         (memi address x86)))
