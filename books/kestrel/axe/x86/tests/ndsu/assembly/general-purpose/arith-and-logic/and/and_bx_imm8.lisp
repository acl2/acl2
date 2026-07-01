; Proofs about a 1-instruction binary that ANDs a sign-extended 8-bit immediate to BX (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_bx_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_bx_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite bx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm bx-rewrite
  (equal (bx x86) (bvchop 16 (rbx x86)))
  :hints (("Goal" :in-theory (enable bx rbx)))))

;; Lifts the subroutine into logic: Creates the function and_bx_imm8, which
;; represents the effect of the program on the x86 state.
;; AND BX, 5 is encoded as 66 83 E3 05 (4 bytes), so stop PC = 0x401004.
;; The immediate 5 is sign-extended from 8 to 16 bits; since 5 > 0 and 5 < 128, value is unchanged.
(def-unrolled and_bx_imm8
  :executable "and_bx_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX after the operation: only BX (bits 0-15) is updated; bits 16-63 of RBX
;; are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm and_bx_imm8-rbx
  (equal (rbx (and_bx_imm8 x86))
         (bvcat 48 (slice 63 16 (rbx x86)) 16 (bvand 16 (rbx x86) 5))))

;; BX after the operation: the natural 16-bit statement of the result.
;; (Intel SDM Vol 2A: DEST <- DEST AND SignExtend(SRC); sign-extending 5 gives 5)
(defthm and_bx_imm8-bx
  (equal (bx (and_bx_imm8 x86))
         (bvand 16 (bx x86) 5)))

;; The RIP is advanced by 4 (AND BX, 5 is 4 bytes: 66 83 E3 05)
(defthm and_bx_imm8-rip
  (equal (rip (and_bx_imm8 x86))
         (+ 4 #x401000)))

;; Registers other than RBX are unchanged.
(defthm and_bx_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (and_bx_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: AND clears CF).
(defthm and_bx_imm8-cf
  (equal (get-flag :cf (and_bx_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: AND clears OF).
(defthm and_bx_imm8-of
  (equal (get-flag :of (and_bx_imm8 x86))
         0))

;; The zero flag is 1 iff the AND result is 0.
(defthm and_bx_imm8-zf
  (equal (get-flag :zf (and_bx_imm8 x86))
         (if (equal 0 (bvand 16 (bx x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm and_bx_imm8-sf
  (equal (get-flag :sf (and_bx_imm8 x86))
         (getbit 15 (bvand 16 (bx x86) 5))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_bx_imm8-pf
  (equal (get-flag :pf (and_bx_imm8 x86))
         (if (evenp (bvcount 8 (bvand 16 (bx x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16-alt-def))))

;; All memory addresses are unchanged.
(defthm and_bx_imm8-memory-unchanged
  (equal (memi address (and_bx_imm8 x86))
         (memi address x86)))

(defthm and_bx_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_bx_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
