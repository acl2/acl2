; Proofs about a 1-instruction binary that executes LEAVE (64-bit operand size)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of leave_64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "leave_64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; The binary is: push rbp; mov rbp, rsp; leave; ret
;; (push and mov merely establish a stack frame at runtime; they are not part
;; of the lifted code, since LEAVE's Intel-SDM-specified behavior on a stack
;; pointer/frame pointer pair holds regardless of how that pair got there).
;; Per objdump, LEAVE (C9, 1 byte) is at 0x401004.
;; Lifts the subroutine into logic: Creates the function leave_64, which
;; represents the effect of the LEAVE instruction on the x86 state.
(def-unrolled leave_64
  :executable "leave_64.elf64"
  :target #x401004
  :stop-pcs '(#x401005)
  :extra-assumptions '((unsigned-canonical-address-p (rbp x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbp x86)))
                       (unsigned-canonical-address-p (bvplus 64 8 (rbp x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (64-bit mode, StackAddressSize = 64): RSP := RBP.
;; Intel SDM (OperandSize = 64): RBP := Pop(), which pops 8 bytes and thus
;; advances RSP by 8 from the value it just got (the old RBP).
(defthm leave_64-rsp
  (equal (rsp (leave_64 x86))
         (bvplus 64 (rbp x86) 8)))

;; Intel SDM: RBP := Pop() reads 8 bytes from the address that RSP was just
;; set to, namely the old RBP.
(defthm leave_64-rbp
  (equal (rbp (leave_64 x86))
         (read 8 (rbp x86) x86)))

;; Intel SDM: LEAVE is the single-byte opcode C9.
(defthm leave_64-rip
  (equal (rip (leave_64 x86))
         (+ 1 #x401004)))

;; Intel SDM: only RSP and RBP are modified; all other general-purpose
;; registers are unchanged.
(defthm leave_64-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (leave_64 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;; Intel SDM: No flags are affected by LEAVE.
(defthm leave_64-cf
  (equal (get-flag :cf (leave_64 x86))
         (get-flag :cf x86)))

(defthm leave_64-zf
  (equal (get-flag :zf (leave_64 x86))
         (get-flag :zf x86)))

(defthm leave_64-sf
  (equal (get-flag :sf (leave_64 x86))
         (get-flag :sf x86)))

(defthm leave_64-of
  (equal (get-flag :of (leave_64 x86))
         (get-flag :of x86)))

(defthm leave_64-af
  (equal (get-flag :af (leave_64 x86))
         (get-flag :af x86)))

(defthm leave_64-pf
  (equal (get-flag :pf (leave_64 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm leave_64-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (leave_64 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; Intel SDM: LEAVE reads memory (the popped RBP) but does not write memory.
(defthm leave_64-memory-unchanged
  (equal (memi address (leave_64 x86))
         (memi address x86)))
