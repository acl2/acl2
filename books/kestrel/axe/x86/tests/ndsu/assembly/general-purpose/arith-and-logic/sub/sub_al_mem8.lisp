; Proofs about a 1-instruction binary that subtracts a memory byte from AL (8-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_al_mem8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_al_mem8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite al to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function sub_al_mem8, which
;; represents the effect of the program on the x86 state.
;; SUB AL, [RBX] is encoded as 2A 03 (2 bytes), so stop PC = 0x401002.
;; The canonical-address-p assumption is required for the x86 model to perform
;; the memory read at [RBX] without an error branch.
(def-unrolled sub_al_mem8
  :executable "sub_al_mem8.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL after the operation: DEST <- DEST - SRC (Intel SDM Vol 2A: SUB entry).
(defthm sub_al_mem8-al
  (equal (al (sub_al_mem8 x86))
         (bvminus 8 (al x86) (read 1 (rbx x86) x86))))

;; The RIP is advanced by 2 (SUB AL, [RBX] is 2 bytes: 2A 03)
(defthm sub_al_mem8-rip
  (equal (rip (sub_al_mem8 x86))
         (+ 2 #x401000)))

;; Registers other than RAX are unchanged.
(defthm sub_al_mem8-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (sub_al_mem8 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is 1 iff mem[RBX] > AL unsigned (borrow):
(defthm sub_al_mem8-cf
  (equal (get-flag :cf (sub_al_mem8 x86))
         (if (bvlt 8 (al x86) (read 1 (rbx x86) x86)) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_al_mem8-zf
  (equal (get-flag :zf (sub_al_mem8 x86))
         (if (equal 0 (bvminus 8 (al x86) (read 1 (rbx x86) x86))) 1 0)))

;; The sign flag is the sign bit (bit 7) of the 8-bit result:
(defthm sub_al_mem8-sf
  (equal (get-flag :sf (sub_al_mem8 x86))
         (getbit 7 (bvminus 8 (al x86) (read 1 (rbx x86) x86))))
  :hints (("Goal" :in-theory (enable bvminus))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of AL < low nibble of mem[RBX]:
(defthm sub_al_mem8-af
  (equal (get-flag :af (sub_al_mem8 x86))
         (if (< (bvchop 4 (al x86))
                (bvchop 4 (read 1 (rbx x86) x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 8-bit result overflows:
(defthm sub_al_mem8-of
  (equal (get-flag :of (sub_al_mem8 x86))
         (let ((diff (- (logext 8 (al x86))
                        (logext 8 (read 1 (rbx x86) x86)))))
           (if (or (< diff (- (expt 2 7)))
                   (<= (expt 2 7) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_al_mem8-pf
  (equal (get-flag :pf (sub_al_mem8 x86))
         (let ((diff (bvminus 8 (al x86) (read 1 (rbx x86) x86))))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; All memory addresses are unchanged (instruction reads from memory but does not write):
(defthm sub_al_mem8-memory-unchanged
  (equal (memi address (sub_al_mem8 x86))
         (memi address x86)))

(defthm sub_al_mem8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_al_mem8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
