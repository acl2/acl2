; Proofs about a 1-instruction binary that ORs RAX with a sign-extended immediate (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_rax_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_rax_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function or_rax_imm32, which
;; represents the effect of the program on the x86 state.
;; OR RAX, 1000 is encoded as 48 0D E8 03 00 00 (6 bytes), so stop PC = 0x401006.
;; The immediate 1000 is sign-extended to 64 bits; since 0 < 1000 < 2^31,
;; its value is unchanged by sign extension.
(def-unrolled or_rax_imm32
  :executable "or_rax_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401006))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 64-bit OR of the initial RAX and the sign-extended immediate.
;; Since 1000 > 0 and 1000 < 2^31, sign-extension leaves it unchanged.
(defthm or_rax_imm32-rax
  (equal (rax (or_rax_imm32 x86))
         (bvor 64 (rax x86) 1000)))

;; The RIP is advanced by 6 (OR RAX, imm32 is 6 bytes: REX.W 0D E8 03 00 00)
(defthm or_rax_imm32-rip
  (equal (rip (or_rax_imm32 x86))
         (+ 6 #x401000)))

;; Registers other than RAX are unchanged.
(defthm or_rax_imm32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (or_rax_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: OR clears CF).
(defthm or_rax_imm32-cf
  (equal (get-flag :cf (or_rax_imm32 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: OR clears OF).
(defthm or_rax_imm32-of
  (equal (get-flag :of (or_rax_imm32 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm or_rax_imm32-zf
  (equal (get-flag :zf (or_rax_imm32 x86))
         (if (equal 0 (bvor 64 (rax x86) 1000))
             1
           0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm or_rax_imm32-sf
  (equal (get-flag :sf (or_rax_imm32 x86))
         (getbit 63 (bvor 64 (rax x86) 1000))))

(defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_rax_imm32-pf
  (equal (get-flag :pf (or_rax_imm32 x86))
         (if (evenp (bvcount 8 (bvor 64 (rax x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def))))

;; All memory addresses are unchanged
(defthm or_rax_imm32-memory-unchanged
  (equal (memi address (or_rax_imm32 x86))
         (memi address x86)))

(defthm or_rax_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_rax_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
