; Proofs about a 1-instruction binary that adds an immediate to AX (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_ax_imm16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_ax_imm16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers16" :dir :system)

;; Rewrite ax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Lifts the subroutine into logic: Creates the function add_ax_imm16, which
;; represents the effect of the program on the x86 state.
;; ADD AX, 500 is encoded as 66 05 F4 01 (4 bytes), so stop PC = 0x401004.
(def-unrolled add_ax_imm16
  :executable "add_ax_imm16.elf64"
  :target #x401000
  :stop-pcs '(#x401004))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX after the operation: only AX (bits 0-15) is updated to the 16-bit sum;
;; bits 16-63 of RAX are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm add_ax_imm16-rax
  (equal (rax (add_ax_imm16 x86))
         (bvcat 48 (slice 63 16 (rax x86)) 16 (bvplus 16 (rax x86) 500))))

;; AX after the operation: the natural 16-bit statement of the result.
(defthm add_ax_imm16-ax
  (equal (ax (add_ax_imm16 x86))
         (bvplus 16 (ax x86) 500)))

;; The RIP is advanced by 4 (ADD AX, imm16 is 4 bytes: 66 05 F4 01)
(defthm add_ax_imm16-rip
  (equal (rip (add_ax_imm16 x86))
         (+ 4 #x401000)))

;; Registers other than RAX are unchanged.
(defthm add_ax_imm16-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (add_ax_imm16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the 16-bit unsigned sum overflows (i.e., >= 2^16):
(defthm add_ax_imm16-cf
  (equal (get-flag :cf (add_ax_imm16 x86))
         (if (<= (expt 2 16)
                 (+ (ax x86) 500))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 16 bits, is 0
(defthm add_ax_imm16-zf
  (equal (get-flag :zf (add_ax_imm16 x86))
         (if (equal 0 (bvplus 16 500 (ax x86)))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm add_ax_imm16-sf
  (equal (get-flag :sf (add_ax_imm16 x86))
         (let ((sum (bvplus 16 (ax x86) 500)))
           (getbit 15 sum)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibble of AX and the low nibble of 500 exceeds 15):
(defthm add_ax_imm16-af
  (equal (get-flag :af (add_ax_imm16 x86))
         (if (> (+ (bvchop 4 (ax x86))
                   (bvchop 4 500))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 16-bit result overflows
(defthm add_ax_imm16-of
  (equal (get-flag :of (add_ax_imm16 x86))
         (let ((sum (+ (logext 16 (ax x86))
                       500)))
           (if (or (< sum (- (expt 2 15))) ; sum too small
                   (<= (expt 2 15) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec16 signed-byte-p))))

(defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_ax_imm16-pf
  (equal (get-flag :pf (add_ax_imm16 x86))
         (let ((sum (bvplus 16 (ax x86) 500)))
           ;; note that this only considers 8 bits:
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec16-alt-def bvplus))))

;; All memory addresses are unchanged
(defthm add_ax_imm16-memory-unchanged
  (equal (memi address (add_ax_imm16 x86))
         (memi address x86)))

(defthm add_ax_imm16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_ax_imm16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
