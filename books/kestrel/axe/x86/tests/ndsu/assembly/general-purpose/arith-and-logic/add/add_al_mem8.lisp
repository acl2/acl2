; Proofs about a 1-instruction binary that adds a memory byte to AL (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add_al_mem8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add_al_mem8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function add_al_mem8, which
;; represents the effect of the program on the x86 state.
;; ADD AL, [RBX] is encoded as 02 03 (2 bytes), so stop PC = 0x401002.
;; The canonical-address-p assumption is required for the x86 model to perform
;; the memory read at [RBX] without an error branch.
(def-unrolled add_al_mem8
  :executable "add_al_mem8.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: the natural 8-bit statement of the result.
(defthm add_al_mem8-al
  (equal (al (add_al_mem8 x86))
         (bvplus 8 (al x86) (read 1 (rbx x86) x86))))

;; The RIP is advanced by 2 (ADD AL, [RBX] is 2 bytes: 02 03)
(defthm add_al_mem8-rip
  (equal (rip (add_al_mem8 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm add_al_mem8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (add_al_mem8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the 8-bit unsigned sum overflows (i.e., >= 2^8):
(defthm add_al_mem8-cf
  (equal (get-flag :cf (add_al_mem8 x86))
         (if (<= (expt 2 8)
                 (+ (al x86) (read 1 (rbx x86) x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 8 bits, is 0
(defthm add_al_mem8-zf
  (equal (get-flag :zf (add_al_mem8 x86))
         (if (equal 0 (bvplus 8 (al x86) (read 1 (rbx x86) x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm add_al_mem8-sf
  (equal (get-flag :sf (add_al_mem8 x86))
         (let ((sum (+ (al x86) (read 1 (rbx x86) x86))))
           (getbit 7 sum)))
  :hints (("Goal" :in-theory (enable bvplus acl2::getbit-of-+-new))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the low nibble of AL and the low nibble of the memory
;; byte exceeds 15):
(defthm add_al_mem8-af
  (equal (get-flag :af (add_al_mem8 x86))
         (if (> (+ (bvchop 4 (al x86))
                   (bvchop 4 (read 1 (rbx x86) x86)))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

;; The overflow flag is 1 iff the signed 8-bit result overflows
(defthm add_al_mem8-of
  (equal (get-flag :of (add_al_mem8 x86))
         (let ((sum (+ (logext 8 (al x86))
                       (logext 8 (read 1 (rbx x86) x86)))))
           (if (or (< sum (- (expt 2 7))) ; sum too small
                   (<= (expt 2 7) sum)    ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec8 signed-byte-p))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add_al_mem8-pf
  (equal (get-flag :pf (add_al_mem8 x86))
         (let ((sum (+ (al x86) (read 1 (rbx x86) x86))))
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec8 bvplus
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged (instruction reads from memory but does not write)
(defthm add_al_mem8-memory-unchanged
  (equal (memi address (add_al_mem8 x86))
         (memi address x86)))

(defthm add_al_mem8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add_al_mem8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
