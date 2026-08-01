; Proofs about a 1-instruction binary that executes ENTER imm16, 0
; (nesting level 0)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of enter_imm16_0.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "enter_imm16_0.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; ENTER 16, 0 is encoded as C8 10 00 00 (4 bytes), so stop PC = 0x401004.
;; Lifts the subroutine into logic: Creates the function enter_imm16_0, which
;; represents the effect of the ENTER instruction on the x86 state.
(def-unrolled enter_imm16_0
  :executable "enter_imm16_0.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-assumptions '((unsigned-canonical-address-p (rsp x86))
                       (unsigned-canonical-address-p (bvplus 64 -8 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -24 (rsp x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (nesting level 0): Push(RBP) decrements RSP by 8; then
;; RSP := RSP - imm16 decrements RSP by 16 more. Net RSP change = -8 - 16 = -24.
(defthm enter_imm16_0-rsp
  (equal (rsp (enter_imm16_0 x86))
         (bvplus 64 (rsp x86) (- 24))))

;; Intel SDM: RBP := FrameTemp, where FrameTemp is RSP right after Push(RBP),
;; i.e., the old RSP minus 8.
(defthm enter_imm16_0-rbp
  (equal (rbp (enter_imm16_0 x86))
         (bvplus 64 (rsp x86) (- 8))))

;; Intel SDM: Push(RBP) writes the old RBP to the stack at (old RSP) - 8.
(defthm enter_imm16_0-stack-has-rbp
  (equal (read 8 (bvplus 64 (rsp x86) (- 8)) (enter_imm16_0 x86))
         (rbp x86)))

;; Intel SDM: ENTER imm16, 0 is 4 bytes (C8 iw 00).
(defthm enter_imm16_0-rip
  (equal (rip (enter_imm16_0 x86))
         (+ 4 #x401000)))

;; Intel SDM: only RSP, RBP, and memory are modified; all other
;; general-purpose registers are unchanged.
(defthm enter_imm16_0-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (enter_imm16_0 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;; Intel SDM: No flags are affected by ENTER.
(defthm enter_imm16_0-cf
  (equal (get-flag :cf (enter_imm16_0 x86))
         (get-flag :cf x86)))

(defthm enter_imm16_0-zf
  (equal (get-flag :zf (enter_imm16_0 x86))
         (get-flag :zf x86)))

(defthm enter_imm16_0-sf
  (equal (get-flag :sf (enter_imm16_0 x86))
         (get-flag :sf x86)))

(defthm enter_imm16_0-of
  (equal (get-flag :of (enter_imm16_0 x86))
         (get-flag :of x86)))

(defthm enter_imm16_0-af
  (equal (get-flag :af (enter_imm16_0 x86))
         (get-flag :af x86)))

(defthm enter_imm16_0-pf
  (equal (get-flag :pf (enter_imm16_0 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm enter_imm16_0-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (enter_imm16_0 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; All memory outside the single written qword (at (old RSP) - 8) is
;; unchanged (Intel SDM: only that stack slot is written).
(defthm enter_imm16_0-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (+ (- 8) (rsp x86))) 8))
           (equal (read 1 address (enter_imm16_0 x86))
                  (read 1 address x86))))
