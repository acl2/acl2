; Proofs about a 1-instruction binary that adds a sign-extended immediate to RBX (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_rbx_imm32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_rbx_imm32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add_rbx_imm32, which
;; represents the effect of the program on the x86 state.
;; ADD RBX, 1000 is encoded as 48 81 C3 E8 03 00 00 (7 bytes), so stop PC = 0x401007.
(def-unrolled add_rbx_imm32
  :executable "add_rbx_imm32.elf64"
  :target #x401000
  :stop-pcs '(#x401007))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX contains the 64-bit sum of the initial RBX and the sign-extended immediate.
;; Since 1000 > 0 and 1000 < 2^31, sign-extension leaves it unchanged.
(defthm add_rbx_imm32-rbx
  (equal (rbx (add_rbx_imm32 x86))
         (bvplus 64 (rbx x86) 1000)))

;; The RIP is advanced by 7 (ADD RBX, imm32 is 7 bytes: REX.W 81 C3 E8 03 00 00)
(defthm add_rbx_imm32-rip
  (equal (rip (add_rbx_imm32 x86))
         (+ 7 #x401000)))

;; Registers other than RBX are unchanged.
(defthm add_rbx_imm32-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (add_rbx_imm32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx ; todo
                                     ))))

;; The carry flag is 1 iff the 64-bit unsigned sum overflows (i.e., >= 2^64):
(defthm add_rbx_imm32-cf
  (equal (get-flag :cf (add_rbx_imm32 x86))
         (if (<= (expt 2 64)
                 (+ (bvchop 64 (rbx x86)) 1000))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new acl2::getbit-too-high))))

;; The zero flag is 1 iff the sum, chopped down to 64 bits, is 0
(defthm add_rbx_imm32-zf
  (equal (get-flag :zf (add_rbx_imm32 x86))
         (if (equal 0 (bvplus 64 1000 (rbx x86)))
             1
           0))
  :hints (("Goal" :in-theory (disable acl2::equal-of-constant-and-bvplus-of-constant
                                      acl2::equal-of-bvplus-of-constant-and-constant))))

;; The sign flag is just the sign bit of the result.
(defthm add_rbx_imm32-sf
  (equal (get-flag :sf (add_rbx_imm32 x86))
         (let ((sum (bvplus 64 (rbx x86) 1000)))
           (getbit 63 sum)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibbles exceeds 15):
(defthm add_rbx_imm32-af
  (equal (get-flag :af (add_rbx_imm32 x86))
         (if (> (+ (bvchop 4 (rbx x86))
                   (bvchop 4 1000))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 64-bit result overflows
(defthm add_rbx_imm32-of
  (equal (get-flag :of (add_rbx_imm32 x86))
         (let ((sum (+ (logext 64 (rbx x86))
                       1000)))
           (if (or (< sum (- (expt 2 63))) ; sum too small
                   (<= (expt 2 63) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec64 signed-byte-p))))

(defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
          (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_rbx_imm32-pf
  (equal (get-flag :pf (add_rbx_imm32 x86))
         (let ((sum (+ (rbx x86) 1000)))
           ;; note that this only considers 8 bits:
            (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def bvplus))))

;; All memory addresses are unchanged
(defthm add_rbx_imm32-memory-unchanged
  (equal (memi address (add_rbx_imm32 x86))
         (memi address x86)))

(defthm add_rbx_imm32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_rbx_imm32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
