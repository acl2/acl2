; Proofs about a 1-instruction binary that executes ENTER imm16, imm8
; (nesting level 2, a concrete example of the general N > 1 case)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of enter_imm16_imm8.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "enter_imm16_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; ENTER 16, 2 is encoded as C8 10 00 02 (4 bytes), so stop PC = 0x401004.
;; Lifts the subroutine into logic: Creates the function enter_imm16_imm8,
;; which represents the effect of the ENTER instruction on the x86 state.
(def-unrolled enter_imm16_imm8
  :executable "enter_imm16_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-rules '(x86isa::x86-enter-copy-nested-frame-pointers)
  :extra-assumptions '((unsigned-canonical-address-p (rsp x86))
                       (unsigned-canonical-address-p (bvplus 64 -8 (rsp x86)))
                       (unsigned-canonical-address-p (+ -8 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -16 (rsp x86)))
                       (unsigned-canonical-address-p (+ -16 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -24 (rsp x86)))
                       (unsigned-canonical-address-p (+ -24 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -40 (rsp x86)))
                       (unsigned-canonical-address-p (+ -40 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -8 (rbp x86)))
                       (unsigned-canonical-address-p (+ -8 (rbp x86)))
                       (unsigned-canonical-address-p (+ -1 (rbp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -1 (rbp x86)))
                       (unsigned-canonical-address-p (bvplus 64 7 (bvplus 64 -8 (rbp x86))))
                       (unsigned-canonical-address-p (+ 7 (+ -8 (rbp x86))))
                       (unsigned-canonical-address-p (+ -8 (+ -8 (rsp x86))))
                       (unsigned-canonical-address-p (+ -16 (+ -8 (rsp x86))))
                       (unsigned-canonical-address-p (+ 7 (+ -8 (+ -8 (rsp x86)))))
                       (unsigned-canonical-address-p (+ 7 (+ -8 (rsp x86))))
                       (unsigned-canonical-address-p (+ 7 (+ -16 (+ -8 (rsp x86)))))
                       (unsigned-canonical-address-p (+ -16 (+ -16 (+ -8 (rsp x86)))))
                       (unsigned-canonical-address-p (+ -24 (+ -16 (+ -8 (rsp x86)))))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (nesting level N = 2): Push(RBP) decrements RSP by 8; the loop
;; copies N-1 = 1 nested frame pointer onto the stack, decrementing RSP by 8
;; more; Push(FrameTemp) decrements RSP by 8 more; RSP := RSP - imm16
;; decrements RSP by 16 more.
;; Net RSP change = -8 - 8 - 8 - 16 = -40.
(defthm enter_imm16_imm8-rsp
  (equal (rsp (enter_imm16_imm8 x86))
         (bvplus 64 (rsp x86) (- 40))))

;; Intel SDM: RBP := FrameTemp, where FrameTemp is RSP right after
;; Push(RBP), i.e., the old RSP minus 8.
(defthm enter_imm16_imm8-rbp
  (equal (rbp (enter_imm16_imm8 x86))
         (bvplus 64 (rsp x86) (- 8))))

;; Intel SDM: Push(RBP) writes the old RBP to the stack at (old RSP) - 8.
(defthm enter_imm16_imm8-stack-has-rbp
  (equal (read 8 (bvplus 64 (rsp x86) (- 8)) (enter_imm16_imm8 x86))
         (rbp x86))
  :hints (("Goal" :in-theory (enable read-of-write-irrel-bv bvlt bvminus bvuminus
                                     acl2::bvchop-of-sum-cases))))

;; Intel SDM (nesting level N = 2): the loop (for i = 1 to N-1 = 1) first
;; decrements RBP by 8 (operand size) and then copies (pushes) the qword
;; found at that address, i.e. at (old RBP) - 8, in the ORIGINAL x86 state
;; (this copy happens before RBP is overwritten with FrameTemp).
;; This holds provided the caller's saved-frame-pointer slot, at
;; (old RBP) - 8, does not overlap the slot where ENTER just pushed the old
;; RBP, at (old RSP) - 8 (true for any realistic caller frame, where RBP and
;; RSP point into different regions of the stack).
(defthm enter_imm16_imm8-stack-has-copied-frame-pointer
  (implies (disjoint-regions48p 8 (bvplus 64 (- 8) (rbp x86))
                                8 (bvplus 64 (- 8) (rsp x86)))
           (equal (read 8 (bvplus 64 (rsp x86) (- 16)) (enter_imm16_imm8 x86))
                  (read 8 (bvplus 64 (rbp x86) (- 8)) x86)))
  :hints (("Goal" :in-theory (enable read-of-write-irrel-bv bvlt bvminus bvuminus
                                     disjoint-regions48p
                                     acl2::bvchop-of-sum-cases))))

;; Intel SDM: Push(FrameTemp) writes FrameTemp = (old RSP) - 8 to the stack
;; at (old RSP) - 24 (after the first push and the one-frame-pointer loop).
(defthm enter_imm16_imm8-stack-has-frametemp
  (equal (read 8 (bvplus 64 (rsp x86) (- 24)) (enter_imm16_imm8 x86))
         (bvplus 64 (rsp x86) (- 8)))
  :hints (("Goal" :in-theory (enable read-of-write-irrel-bv bvlt bvminus bvuminus
                                     acl2::bvchop-of-sum-cases))))

;; Intel SDM: ENTER imm16, imm8 is 4 bytes (C8 iw ib).
(defthm enter_imm16_imm8-rip
  (equal (rip (enter_imm16_imm8 x86))
         (+ 4 #x401000)))

;; Intel SDM: only RSP, RBP, and memory are modified; all other
;; general-purpose registers are unchanged.
(defthm enter_imm16_imm8-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (enter_imm16_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;; Intel SDM: No flags are affected by ENTER.
(defthm enter_imm16_imm8-cf
  (equal (get-flag :cf (enter_imm16_imm8 x86))
         (get-flag :cf x86)))

(defthm enter_imm16_imm8-zf
  (equal (get-flag :zf (enter_imm16_imm8 x86))
         (get-flag :zf x86)))

(defthm enter_imm16_imm8-sf
  (equal (get-flag :sf (enter_imm16_imm8 x86))
         (get-flag :sf x86)))

(defthm enter_imm16_imm8-of
  (equal (get-flag :of (enter_imm16_imm8 x86))
         (get-flag :of x86)))

(defthm enter_imm16_imm8-af
  (equal (get-flag :af (enter_imm16_imm8 x86))
         (get-flag :af x86)))

(defthm enter_imm16_imm8-pf
  (equal (get-flag :pf (enter_imm16_imm8 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm enter_imm16_imm8-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (enter_imm16_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; All memory outside the three written qwords (at (old RSP)-8, (old RSP)-16,
;; and (old RSP)-24) is unchanged (Intel SDM: only those stack slots are
;; written).
(defthm enter_imm16_imm8-other-memory
  (implies (and (not (bvlt 48 (bvminus 48 address (+ (- 8) (rsp x86))) 8))
                (not (bvlt 48 (bvminus 48 address (+ (- 16) (rsp x86))) 8))
                (not (bvlt 48 (bvminus 48 address (+ (- 24) (rsp x86))) 8)))
           (equal (read 1 address (enter_imm16_imm8 x86))
                  (read 1 address x86))))
