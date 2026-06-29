; Proofs about a 1-instruction binary that adds 2 numbers
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of add.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "add.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function add, which
;; represents the effect of the program on the x86 state.
(def-unrolled add
  :executable "add.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit sum of the initial RAX and  RBX
(defthm add-rax
  (equal (rax (add x86))
         (bvplus 32 (rax x86) (rbx x86))))

;; The RIP is advanced by 2
(defthm add-rip
  (equal (rip (add x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm add-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (add x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the sum of the 32-bit value is >= 2^32:
(defthm add-cf
  (equal (get-flag :cf (add x86))
         (if (<= (expt 2 32)
                 (+ (bvchop 32 (rax x86)) (bvchop 32 (rbx x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm add-zf
  (equal (get-flag :zf (add x86))
         (if (equal 0 (bvplus 32 (rax x86) (rbx x86)))
             1
           0)))

;; The overflow flag is 1 iff the sum doesn't fit in the destination
(defthm add-of
  (equal (get-flag :of (add x86))
         (let ((sum (+ (logext 32 (rax x86))
                       (logext 32 (rbx x86)))))
           (if (or (< sum (- (expt 2 31))) ; sum too small
                   (<= (expt 2 31) sum) ; sum too big
                   )
               1 ; overflow
             0   ; no overflow
             )))
  :hints (("Goal" :in-theory (enable of-spec32 signed-byte-p))))

;; todo: move
(defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm add-pf
  (equal (get-flag :pf (add x86))
         (let ((sum (+ (rax x86)
                       (rbx x86))))
           ;; note that this only considers 8 bits:
           (if (evenp (bvcount 8 sum))
               1
             0)))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvplus))))

;; The sign flag is just the sign bit of the result.
(defthm add-sf
  (equal (get-flag :sf (add x86))
         (let ((sum (+ (rax x86)
                       (rbx x86))))
           (getbit 31 sum)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the two low nibbles is greater than 15):
(defthm add-af
  (equal (get-flag :af (add x86))
         (if (> (+ (bvchop 4 (rax x86))
                   (bvchop 4 (rbx x86)))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))

(defthm add-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (add x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))

;; All memory addresses are unchanged
(defthm add-memory-unchanged
  (equal (memi address (add x86))
         (memi address x86)))

;; todo: more properties...
