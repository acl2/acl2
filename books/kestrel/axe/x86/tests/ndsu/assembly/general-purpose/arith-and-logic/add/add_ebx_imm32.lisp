; Proofs about a 1-instruction binary that adds an immediate to EBX (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_ebx_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_ebx_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite ebx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function add_ebx_imm32, which
;; represents the effect of the program on the x86 state.
;; ADD EBX, 1000 is encoded as 81 C3 E8 03 00 00 (6 bytes), so stop PC = 0x401006.
(def-unrolled add_ebx_imm32
  :executable "add_ebx_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401006))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 32-bit sum; 32-bit writes zero-extend into the upper 32 bits.
(defthm add_ebx_imm32-rbx
  (equal (rbx (add_ebx_imm32 x86))
         (bvplus 32 (ebx x86) 1000)))

;; EBX contains the 32-bit sum (the natural statement for this instruction).
(defthm add_ebx_imm32-ebx
  (equal (ebx (add_ebx_imm32 x86))
         (bvplus 32 (ebx x86) 1000)))

;; The RIP is advanced by 6 (ADD EBX, imm32 is 6 bytes: 81 C3 E8 03 00 00)
(defthm add_ebx_imm32-rip
  (equal (rip (add_ebx_imm32 x86))
         (+ 6 #x401000)))

;; Registers other than RBX are unchanged.
(defthm add_ebx_imm32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (add_ebx_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx ; todo
                                     ))))

;; The carry flag is 1 iff the 32-bit unsigned sum overflows (i.e., >= 2^32):
(defthm add_ebx_imm32-cf
  (equal (get-flag :cf (add_ebx_imm32 x86))
         (if (<= (expt 2 32)
                 (+ (ebx x86) 1000))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm add_ebx_imm32-zf
  (equal (get-flag :zf (add_ebx_imm32 x86))
         (if (equal 0 (bvplus 32 1000 (ebx x86)))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is just the sign bit of the result.
(defthm add_ebx_imm32-sf
  (equal (get-flag :sf (add_ebx_imm32 x86))
         (getbit 31 (bvplus 32 (ebx x86) 1000)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibbles exceeds 15):
(defthm add_ebx_imm32-af
  (equal (get-flag :af (add_ebx_imm32 x86))
         (if (> (+ (bvchop 4 (ebx x86))
                   (bvchop 4 1000))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 32-bit result overflows
(defthm add_ebx_imm32-of
  (equal (get-flag :of (add_ebx_imm32 x86))
         (let ((sum (+ (logext 32 (ebx x86))
                       1000)))
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
(defthm add_ebx_imm32-pf
  (equal (get-flag :pf (add_ebx_imm32 x86))
         ;; note that this only considers 8 bits:
         (if (evenp (bvcount 8 (bvplus 32 (ebx x86) 1000)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvplus))))

;; All memory addresses are unchanged
(defthm add_ebx_imm32-memory-unchanged
  (equal (memi address (add_ebx_imm32 x86))
         (memi address x86)))

(defthm add_ebx_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_ebx_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
