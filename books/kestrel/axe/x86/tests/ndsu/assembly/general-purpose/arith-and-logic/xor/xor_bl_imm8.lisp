; Proofs about a 1-instruction binary that XORs an immediate to BL (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_bl_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_bl_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite bl to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm bl-rewrite
  (equal (bl x86) (bvchop 8 (rbx x86)))
  :hints (("Goal" :in-theory (enable bl rbx)))))

;; Lifts the subroutine into logic: Creates the function xor_bl_imm8, which
;; represents the effect of the program on the x86 state.
;; XOR BL, 5 is encoded as 80 F3 05 (3 bytes), so stop PC = 0x401003.
(def-unrolled xor_bl_imm8
  :executable "xor_bl_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; BL after the operation: the natural 8-bit statement of the result.
;; (Intel SDM Vol 2A: DEST <- DEST XOR SRC)
(defthm xor_bl_imm8-bl
  (equal (bl (xor_bl_imm8 x86))
         (bvxor 8 (bl x86) 5)))

;; The RIP is advanced by 3 (XOR BL, imm8 is 3 bytes: 80 F3 05)
(defthm xor_bl_imm8-rip
  (equal (rip (xor_bl_imm8 x86))
         (+ 3 #x401000)))

;; Registers other than RBX are unchanged.
(defthm xor_bl_imm8-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (xor_bl_imm8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: XOR clears CF).
(defthm xor_bl_imm8-cf
  (equal (get-flag :cf (xor_bl_imm8 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: XOR clears OF).
(defthm xor_bl_imm8-of
  (equal (get-flag :of (xor_bl_imm8 x86))
         0))

;; The zero flag is 1 iff the XOR result is 0.
(defthm xor_bl_imm8-zf
  (equal (get-flag :zf (xor_bl_imm8 x86))
         (if (equal 0 (bvxor 8 (bl x86) 5))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm xor_bl_imm8-sf
  (equal (get-flag :sf (xor_bl_imm8 x86))
         (getbit 7 (bvxor 8 (bl x86) 5))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_bl_imm8-pf
  (equal (get-flag :pf (xor_bl_imm8 x86))
         (if (evenp (bvcount 8 (bvxor 8 (bl x86) 5)))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)
                                   (acl2::bvxor-with-smaller-arg-1
                                    acl2::bvxor-with-smaller-arg-2)))))

;; All memory addresses are unchanged.
(defthm xor_bl_imm8-memory-unchanged
  (equal (memi address (xor_bl_imm8 x86))
         (memi address x86)))

(defthm xor_bl_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_bl_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
