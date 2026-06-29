; Proofs about a 1-instruction binary that adds an immediate to EAX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_eax_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_eax_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function add_eax_imm32, which
;; represents the effect of the program on the x86 state.
;; ADD EAX, 500 is encoded as 05 F4 01 00 00 (5 bytes), so stop PC = 0x401005.
(def-unrolled add_eax_imm32
  :executable "add_eax_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401005))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit sum; 32-bit writes zero-extend into the upper 32 bits.
(defthm add_eax_imm32-rax
  (equal (rax (add_eax_imm32 x86))
         (bvplus 32 (eax x86) 500)))

;; EAX contains the 32-bit sum (the natural statement for this instruction).
(defthm add_eax_imm32-eax
  (equal (eax (add_eax_imm32 x86))
         (bvplus 32 (eax x86) 500)))

;; The RIP is advanced by 5 (ADD EAX, imm32 is 5 bytes: 05 F4 01 00 00)
(defthm add_eax_imm32-rip
  (equal (rip (add_eax_imm32 x86))
         (+ 5 #x401000)))

;; Registers other than RAX are unchanged.
(defthm add_eax_imm32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (add_eax_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the 32-bit unsigned sum overflows (i.e., >= 2^32):
(defthm add_eax_imm32-cf
  (equal (get-flag :cf (add_eax_imm32 x86))
         (if (<= (expt 2 32)
                 (+ (eax x86) 500))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm add_eax_imm32-zf
  (equal (get-flag :zf (add_eax_imm32 x86))
         (if (equal 0 (bvplus 32 500 (eax x86)))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is just the sign bit of the result.
(defthm add_eax_imm32-sf
  (equal (get-flag :sf (add_eax_imm32 x86))
         (getbit 31 (bvplus 32 (eax x86) 500)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibbles exceeds 15):
(defthm add_eax_imm32-af
  (equal (get-flag :af (add_eax_imm32 x86))
         (if (> (+ (bvchop 4 (eax x86))
                   (bvchop 4 500))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 32-bit result overflows
(defthm add_eax_imm32-of
  (equal (get-flag :of (add_eax_imm32 x86))
         (let ((sum (+ (logext 32 (eax x86))
                       500)))
           (if (or (< sum (- (expt 2 31))) ; sum too small
                   (<= (expt 2 31) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec32 signed-byte-p))))

(defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_eax_imm32-pf
  (equal (get-flag :pf (add_eax_imm32 x86))
         ;; note that this only considers 8 bits:
         (if (evenp (bvcount 8 (bvplus 32 (eax x86) 500)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvplus))))

;; All memory addresses are unchanged
(defthm add_eax_imm32-memory-unchanged
  (equal (memi address (add_eax_imm32 x86))
         (memi address x86)))

(defthm add_eax_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_eax_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
