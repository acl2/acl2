; Proofs about a 1-instruction binary that ANDs a sign-extended 8-bit immediate to EBX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_ebx_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_ebx_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite ebx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function and_ebx_imm8, which
;; represents the effect of the program on the x86 state.
;; AND EBX, 5 is encoded as 83 E3 05 (3 bytes), so stop PC = 0x401003.
;; The immediate 5 is sign-extended from 8 to 32 bits; since 5 > 0 and 5 < 128, value is unchanged.
(def-unrolled and_ebx_imm8
  :executable "and_ebx_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 32-bit AND result; 32-bit writes zero-extend into the upper 32 bits.
(defthm and_ebx_imm8-rbx
  (equal (rbx (and_ebx_imm8 x86))
         (bvand 32 (ebx x86) 5)))

;; EBX contains the 32-bit AND result (the natural statement for this instruction).
;; (Intel SDM Vol 2A: DEST <- DEST AND SignExtend(SRC); sign-extending 5 gives 5)
(defthm and_ebx_imm8-ebx
  (equal (ebx (and_ebx_imm8 x86))
         (bvand 32 (ebx x86) 5)))

;; The RIP is advanced by 3 (AND EBX, 5 is 3 bytes: 83 E3 05)
(defthm and_ebx_imm8-rip
  (equal (rip (and_ebx_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RBX are unchanged.
(defthm and_ebx_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (and_ebx_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: AND clears CF).
(defthm and_ebx_imm8-cf
  (equal (get-flag :cf (and_ebx_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: AND clears OF).
(defthm and_ebx_imm8-of
  (equal (get-flag :of (and_ebx_imm8 x86))
         0))

;; The zero flag is 1 iff the AND result is 0.
(defthm and_ebx_imm8-zf
  (equal (get-flag :zf (and_ebx_imm8 x86))
         (if (equal 0 (bvand 32 (ebx x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm and_ebx_imm8-sf
  (equal (get-flag :sf (and_ebx_imm8 x86))
         (getbit 31 (bvand 32 (ebx x86) 5))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_ebx_imm8-pf
  (equal (get-flag :pf (and_ebx_imm8 x86))
         (if (evenp (bvcount 8 (bvand 32 (ebx x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def))))

;; All memory addresses are unchanged.
(defthm and_ebx_imm8-memory-unchanged
  (equal (memi address (and_ebx_imm8 x86))
         (memi address x86)))

(defthm and_ebx_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_ebx_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
