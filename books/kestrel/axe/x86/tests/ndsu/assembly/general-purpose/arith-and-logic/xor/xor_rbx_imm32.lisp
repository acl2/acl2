; Proofs about a 1-instruction binary that XORs a sign-extended immediate to RBX (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_rbx_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_rbx_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function xor_rbx_imm32, which
;; represents the effect of the program on the x86 state.
;; XOR RBX, 1000 is encoded as 48 81 F3 E8 03 00 00 (7 bytes), so stop PC = 0x401007.
;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31, value is unchanged.
(def-unrolled xor_rbx_imm32
  :executable "xor_rbx_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401007))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 64-bit XOR of the initial RBX and the sign-extended immediate.
;; (Intel SDM Vol 2A: DEST <- DEST XOR SignExtend(SRC))
(defthm xor_rbx_imm32-rbx
  (equal (rbx (xor_rbx_imm32 x86))
         (bvxor 64 (rbx x86) 1000)))

;; The RIP is advanced by 7 (XOR RBX, imm32 is 7 bytes: REX.W 81 F3 E8 03 00 00)
(defthm xor_rbx_imm32-rip
  (equal (rip (xor_rbx_imm32 x86))
         (+ 7 #x401000)))

;; Registers other than RBX are unchanged.
(defthm xor_rbx_imm32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (xor_rbx_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: XOR clears CF).
(defthm xor_rbx_imm32-cf
  (equal (get-flag :cf (xor_rbx_imm32 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: XOR clears OF).
(defthm xor_rbx_imm32-of
  (equal (get-flag :of (xor_rbx_imm32 x86))
         0))

;; The zero flag is 1 iff the XOR result is 0.
(defthm xor_rbx_imm32-zf
  (equal (get-flag :zf (xor_rbx_imm32 x86))
         (if (equal 0 (bvxor 64 (rbx x86) 1000))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm xor_rbx_imm32-sf
  (equal (get-flag :sf (xor_rbx_imm32 x86))
         (getbit 63 (bvxor 64 (rbx x86) 1000))))

(defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_rbx_imm32-pf
  (equal (get-flag :pf (xor_rbx_imm32 x86))
         (if (evenp (bvcount 8 (bvxor 64 (rbx x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (e/d (pf-spec64-alt-def)
                                   (acl2::bvxor-with-smaller-arg-1
                                    acl2::bvxor-with-smaller-arg-2)))))

;; All memory addresses are unchanged.
(defthm xor_rbx_imm32-memory-unchanged
  (equal (memi address (xor_rbx_imm32 x86))
         (memi address x86)))

(defthm xor_rbx_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_rbx_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
