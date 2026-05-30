; Proofs about a 1-instruction binary that adds 2 numbers
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
;         Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of eax_ebx_32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "eax_ebx_32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax/ebx to bvchop-of-rax/rbx so proofs reduce to the existing rax/rbx form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))
(local (defthm ebx-rewrite
  (equal (ebx x86) (bvchop 32 (rbx x86)))
  :hints (("Goal" :in-theory (enable ebx rbx)))))

;; Lifts the subroutine into logic: Creates the function eax_ebx_32, which
;; represents the effect of the program on the x86 state.
(def-unrolled eax_ebx_32
  :executable "eax_ebx_32.elf64"
  :target #x401000
  :stop-pcs '(#x401002))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 32-bit sum of the initial EAX and EBX

(defthm eax_ebx_32-rax
  (equal (rax (eax_ebx_32 x86))
         (bvplus 32 (eax x86) (ebx x86))))

;; EAX contains the 32-bit sum of EAX and EBX (the natural statement for this instruction)
(defthm eax_ebx_32-eax
  (equal (eax (eax_ebx_32 x86))
         (bvplus 32 (eax x86) (ebx x86))))

;; The RIP is advanced by 2
(defthm eax_ebx_32-rip
  (equal (rip (eax_ebx_32 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm eax_ebx_32-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (eax_ebx_32 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; The carry flag is 1 iff the sum of the 32-bit value is >= 2^32:
(defthm eax_ebx_32-cf
  (equal (get-flag :cf (eax_ebx_32 x86))
         (if (<= (expt 2 32)
                 (+ (eax x86) (ebx x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable acl2::getbit-of-+-new))))

;; The zero flag is 1 iff the sum, chopped down to 32 bits, is 0
(defthm eax_ebx_32-zf
  (equal (get-flag :zf (eax_ebx_32 x86))
         (if (equal 0 (bvplus 32 (eax x86) (ebx x86)))
             1
           0)))

;; The sign flag is just the sign bit of the result.
(defthm eax_ebx_32-sf
  (equal (get-flag :sf (eax_ebx_32 x86))
         (getbit 31 (bvplus 32 (eax x86) (ebx x86))))
  :hints (("Goal" :in-theory (enable bvplus))))


;; The auxiliary carry flag is 1 iff there is a carry from bit 3 into bit 4
;; (that is, the sum of the two low nibbles is greater than 15):
(defthm eax_ebx_32-af
  (equal (get-flag :af (eax_ebx_32 x86))
         (if (> (+ (bvchop 4 (eax x86))
                   (bvchop 4 (ebx x86)))
                15)
             1
           0))
  :hints (("Goal" :in-theory (enable bvplus bvlt))))


;; The overflow flag is 1 iff the sum doesn't fit in the destination
(defthm eax_ebx_32-of
  (equal (get-flag :of (eax_ebx_32 x86))
         (let ((sum (+ (logext 32 (eax x86))
                       (logext 32 (ebx x86)))))
           (if (or (< sum (- (expt 2 31))) ; sum too small
                   (<= (expt 2 31) sum) ; sum too big
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
(defthm eax_ebx_32-pf
  (equal (get-flag :pf (eax_ebx_32 x86))
         ;; note that this only considers 8 bits:
         (if (evenp (bvcount 8 (bvplus 32 (eax x86) (ebx x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32-alt-def bvplus))))



;; All memory addresses are unchanged
(defthm eax_ebx_32-memory-unchanged
  (equal (memi address (eax_ebx_32 x86))
         (memi address x86)))

(defconst *standard-flags* '(:cf :pf :af :zf :sf :of))

(defthm eax_ebx_32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (eax_ebx_32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))


