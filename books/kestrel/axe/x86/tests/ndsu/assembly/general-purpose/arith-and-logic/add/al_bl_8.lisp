; Proofs about a 1-instruction binary that adds 2 numbers (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of al_bl_8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "al_bl_8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers8" :dir :system)

;; Rewrite al/bl to bvchop-of-rax/rbx so proofs reduce to the existing rax/rbx form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))
(local (defthm bl-rewrite
  (equal (bl x86) (bvchop 8 (rbx x86)))
  :hints (("Goal" :in-theory (enable bl rbx)))))

;; Lifts the subroutine into logic: Creates the function al_bl_8, which
;; represents the effect of the program on the x86 state.
;; ADD AL, BL is encoded as 00 D8 (2 bytes), so stop PC = 0x401002.
(def-unrolled al_bl_8
  :executable "al_bl_8.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.


;; AL after the operation: the natural 8-bit statement of the result.
(defthm al_bl_8-al
  (equal (al (al_bl_8 x86))
         (bvplus 8 (al x86) (bl x86))))

;; The RIP is advanced by 2 (ADD AL,BL is 2 bytes: 00 D8)
(defthm al_bl_8-rip
  (equal (rip (al_bl_8 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm al_bl_8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (al_bl_8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the 8-bit unsigned sum overflows (i.e., >= 2^8):
(defthm al_bl_8-cf
  (equal (get-flag :cf (al_bl_8 x86))
         (if (<= (expt 2 8)
                 (+ (al x86) (bl x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 8 bits, is 0
(defthm al_bl_8-zf
  (equal (get-flag :zf (al_bl_8 x86))
         (if (equal 0 (bvplus 8 (al x86) (bl x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm al_bl_8-sf
  (equal (get-flag :sf (al_bl_8 x86))
         (let ((sum (+ (al x86)
                       (bl x86))))
           (getbit 7 sum)))
  :hints (("Goal" :in-theory (enable bvplus acl2::getbit-of-+-new))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the two low nibbles is greater than 15):
(defthm al_bl_8-af
  (equal (get-flag :af (al_bl_8 x86))
         (if (> (+ (bvchop 4 (al x86))
                   (bvchop 4 (bl x86)))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 8-bit result overflows
(defthm al_bl_8-of
  (equal (get-flag :of (al_bl_8 x86))
         (let ((sum (+ (logext 8 (al x86))
                       (logext 8 (bl x86)))))
           (if (or (< sum (- (expt 2 7))) ; sum too small
                   (<= (expt 2 7) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec8 signed-byte-p))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
;; Note: pf-spec8 uses the 8-bit result directly, so we expand it inline.
(defthm al_bl_8-pf
  (equal (get-flag :pf (al_bl_8 x86))
         (let ((sum (+ (al x86)
                       (bl x86))))
           ;; note that this only considers 8 bits:
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec8 bvplus
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged
(defthm al_bl_8-memory-unchanged
  (equal (memi address (al_bl_8 x86))
         (memi address x86)))

(defthm al_bl_8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (al_bl_8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
