; Proofs about a 1-instruction binary that executes ENTER imm16, 1
; (nesting level 1)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of enter_imm16_1.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "enter_imm16_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; ENTER 16, 1 is encoded as C8 10 00 01 (4 bytes), so stop PC = 0x401004.
;; Lifts the subroutine into logic: Creates the function enter_imm16_1, which
;; represents the effect of the ENTER instruction on the x86 state.
(def-unrolled enter_imm16_1
  :executable "enter_imm16_1.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-rules '(x86isa::x86-enter-copy-nested-frame-pointers)
  :extra-assumptions '((unsigned-canonical-address-p (rsp x86))
                       (unsigned-canonical-address-p (bvplus 64 -8 (rsp x86)))
                       (unsigned-canonical-address-p (+ -8 (rsp x86)))
                       (unsigned-canonical-address-p (bvplus 64 -16 (rsp x86)))
                       (unsigned-canonical-address-p (+ -16 (rsp x86)))
                       (unsigned-canonical-address-p (+ -8 (+ -8 (rsp x86))))
                       (unsigned-canonical-address-p (+ 7 (+ -8 (+ -8 (rsp x86)))))
                       (unsigned-canonical-address-p (bvplus 64 -32 (rsp x86)))
                       (unsigned-canonical-address-p (+ -32 (rsp x86)))
                       (unsigned-canonical-address-p (+ -16 (+ -8 (+ -8 (rsp x86)))))
                       (unsigned-canonical-address-p (+ 7 (+ -8 (rsp x86))))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (nesting level 1): Push(RBP) decrements RSP by 8;
;; FrameTemp := RSP; Push(FrameTemp) decrements RSP by 8 more;
;; RSP := RSP - imm16 decrements RSP by 16 more.
;; Net RSP change = -8 - 8 - 16 = -32.
(defthm enter_imm16_1-rsp
  (equal (rsp (enter_imm16_1 x86))
         (bvplus 64 (rsp x86) (- 32))))

;; Intel SDM: RBP := FrameTemp, where FrameTemp is RSP right after
;; Push(RBP), i.e., the old RSP minus 8.
(defthm enter_imm16_1-rbp
  (equal (rbp (enter_imm16_1 x86))
         (bvplus 64 (rsp x86) (- 8))))

;; Intel SDM: Push(RBP) writes the old RBP to the stack at (old RSP) - 8.
(defthm enter_imm16_1-stack-has-rbp
  (equal (read 8 (bvplus 64 (rsp x86) (- 8)) (enter_imm16_1 x86))
         (rbp x86))
  :hints (("Goal" :in-theory (enable read-of-write-irrel-bv bvlt bvminus bvuminus
                                     acl2::bvchop-of-sum-cases))))

;; Intel SDM: Push(FrameTemp) writes FrameTemp = (old RSP) - 8 to the stack
;; at (old RSP) - 16.
(defthm enter_imm16_1-stack-has-frametemp
  (equal (read 8 (bvplus 64 (rsp x86) (- 16)) (enter_imm16_1 x86))
         (bvplus 64 (rsp x86) (- 8))))

;; Intel SDM: ENTER imm16, 1 is 4 bytes (C8 iw ib).
(defthm enter_imm16_1-rip
  (equal (rip (enter_imm16_1 x86))
         (+ 4 #x401000)))

;; Intel SDM: only RSP, RBP, and memory are modified; all other
;; general-purpose registers are unchanged.
(defthm enter_imm16_1-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (enter_imm16_1 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsp set-rbp))))

;; Intel SDM: No flags are affected by ENTER.
(defthm enter_imm16_1-cf
  (equal (get-flag :cf (enter_imm16_1 x86))
         (get-flag :cf x86)))

(defthm enter_imm16_1-zf
  (equal (get-flag :zf (enter_imm16_1 x86))
         (get-flag :zf x86)))

(defthm enter_imm16_1-sf
  (equal (get-flag :sf (enter_imm16_1 x86))
         (get-flag :sf x86)))

(defthm enter_imm16_1-of
  (equal (get-flag :of (enter_imm16_1 x86))
         (get-flag :of x86)))

(defthm enter_imm16_1-af
  (equal (get-flag :af (enter_imm16_1 x86))
         (get-flag :af x86)))

(defthm enter_imm16_1-pf
  (equal (get-flag :pf (enter_imm16_1 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm enter_imm16_1-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (enter_imm16_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; All memory outside the two written qwords (at (old RSP)-8 and
;; (old RSP)-16) is unchanged (Intel SDM: only those stack slots are
;; written).
(defthm enter_imm16_1-other-memory
  (implies (and (not (bvlt 48 (bvminus 48 address (+ (- 8) (rsp x86))) 8))
                (not (bvlt 48 (bvminus 48 address (+ (- 16) (rsp x86))) 8)))
           (equal (read 1 address (enter_imm16_1 x86))
                  (read 1 address x86))))
