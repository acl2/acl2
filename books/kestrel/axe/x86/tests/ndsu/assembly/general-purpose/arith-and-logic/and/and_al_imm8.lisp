; Proofs about a 1-instruction binary that ANDs AL with an immediate (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_al_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_al_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function and_al_imm8, which
;; represents the effect of the program on the x86 state.
;; AND AL, 5 is encoded as 24 05 (2 bytes), so stop PC = 0x401002.
(def-unrolled and_al_imm8
  :executable "and_al_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: DEST <- DEST AND SRC (Intel SDM Vol 2A: AND entry).
(defthm and_al_imm8-al
  (equal (al (and_al_imm8 x86))
         (bvand 8 (al x86) 5)))

;; The RIP is advanced by 2 (AND AL, imm8 is 2 bytes: 24 05)
(defthm and_al_imm8-rip
  (equal (rip (and_al_imm8 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm and_al_imm8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (and_al_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: AND clears CF).
(defthm and_al_imm8-cf
  (equal (get-flag :cf (and_al_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: AND clears OF).
(defthm and_al_imm8-of
  (equal (get-flag :of (and_al_imm8 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm and_al_imm8-zf
  (equal (get-flag :zf (and_al_imm8 x86))
         (if (equal 0 (bvand 8 (al x86) 5))
             1
           0)))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm and_al_imm8-sf
  (equal (get-flag :sf (and_al_imm8 x86))
         (getbit 7 (bvand 8 (al x86) 5))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_al_imm8-pf
  (equal (get-flag :pf (and_al_imm8 x86))
         (if (evenp (bvcount 8 (bvand 8 (al x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec8
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged
(defthm and_al_imm8-memory-unchanged
  (equal (memi address (and_al_imm8 x86))
         (memi address x86)))

(defthm and_al_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_al_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
