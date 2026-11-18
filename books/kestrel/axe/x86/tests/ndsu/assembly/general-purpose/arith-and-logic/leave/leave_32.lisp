; Proofs about a 1-instruction binary that executes LEAVE (32-bit operand
; size, in genuine 32-bit protected mode)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of leave_32.elf32 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "leave_32.elf32")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; The binary is: push ebp; mov ebp, esp; leave; ret (an i386 ELF32
;; executable, so LEAVE here is genuine 32-bit-mode ESP/EBP LEAVE, not a
;; 66H-prefixed encoding executed in 64-bit mode). push/mov merely establish
;; a stack frame at runtime; they are not part of the lifted code.
;; Per objdump, LEAVE (C9, 1 byte) is at the "do_leave" label, offset 3 into
;; the .text section. Non-position-independent lifting is used, since this
;; is a statically-linked, non-PIE executable with a fixed load address.
;; Lifts the subroutine into logic: Creates the function leave_32, which
;; represents the effect of the LEAVE instruction on the x86 state.
(def-unrolled leave_32
  :executable "leave_32.elf32"
  :target "do_leave"
  :position-independent nil
  :stop-pcs '(4) ;; offset from the .text section base (do_leave is at offset 3, leave is 1 byte)
  :extra-assumptions '((stack-segment-assumptions32 1 x86)
                       ;; EBP is used as an address by LEAVE (ESP := EBP,
                       ;; then a 4-byte pop from that address): it must be a
                       ;; valid effective address, with room for 4 bytes, in
                       ;; the stack segment.
                       (eff-addrs-okp 4 (bvchop 32 (ebp x86)) *ss* x86)
                       (not (mv-nth 0 (x86isa::add-to-*sp$inline 1 (bvchop 32 (ebp x86)) 4 x86)))
                       (equal (mv-nth 1 (x86isa::add-to-*sp$inline 1 (bvchop 32 (ebp x86)) 4 x86))
                              (bvplus 32 4 (bvchop 32 (ebp x86))))
                       (equal (mv-nth 1 (x86isa::rme-size$inline 1 4 (bvchop 32 (ebp x86)) 2 :r nil x86 nil))
                              (read-from-segment 4 (bvchop 32 (ebp x86)) *ss* x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM (32-bit mode, StackAddressSize = 32): ESP := EBP.
;; Intel SDM (OperandSize = 32): EBP := Pop(), which pops 4 bytes and thus
;; advances ESP by 4 from the value it just got (the old EBP).
(defthm leave_32-esp
  (equal (esp (leave_32 x86))
         (bvplus 32 (ebp x86) 4)))

;; Intel SDM: EBP := Pop() reads 4 bytes from the address that ESP was just
;; set to, namely the old EBP.
(local (defthm read-from-segment-of-bvchop-of-ebp
  (equal (read-from-segment 4 (bvchop 32 (ebp x86)) *ss* x86)
         (read-from-segment 4 (ebp x86) *ss* x86))
  :hints (("Goal" :in-theory (enable ebp)))))

(defthm leave_32-ebp
  (equal (ebp (leave_32 x86))
         (read-from-segment 4 (ebp x86) *ss* x86))
  :hints (("Goal" :in-theory (enable read-from-segment-of-bvchop-of-ebp))))

;; Intel SDM: LEAVE is the single-byte opcode C9.  (do_leave is at offset 3
;; in the .text section, so EIP after LEAVE is 3 + 1 = 4.)
(defthm leave_32-eip
  (equal (eip (leave_32 x86))
         4)
  :hints (("Goal" :in-theory (e/d (eip-of-set-eip) (eip)))))

;; Intel SDM: only ESP and EBP are modified; all other general-purpose
;; registers are unchanged.
(defthm leave_32-other-registers
  (implies (and (not (equal *rsp* reg))
                (not (equal *rbp* reg)))
           (equal (rgfi reg (leave_32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-esp set-ebp))))

;; Intel SDM: No flags are affected by LEAVE.
(defthm leave_32-cf
  (equal (get-flag :cf (leave_32 x86))
         (get-flag :cf x86)))

(defthm leave_32-zf
  (equal (get-flag :zf (leave_32 x86))
         (get-flag :zf x86)))

(defthm leave_32-sf
  (equal (get-flag :sf (leave_32 x86))
         (get-flag :sf x86)))

(defthm leave_32-of
  (equal (get-flag :of (leave_32 x86))
         (get-flag :of x86)))

(defthm leave_32-af
  (equal (get-flag :af (leave_32 x86))
         (get-flag :af x86)))

(defthm leave_32-pf
  (equal (get-flag :pf (leave_32 x86))
         (get-flag :pf x86)))

;; No flags at all (including non-standard ones) are affected.
(defthm leave_32-other-flags
  (implies (member-equal flag *flags*)
           (equal (get-flag flag (leave_32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; Intel SDM: LEAVE reads memory (the popped EBP) but does not write memory.
(defthm leave_32-memory-unchanged
  (equal (memi address (leave_32 x86))
         (memi address x86)))
