; Proofs about a 1-instruction binary that compares a memory byte to AL (8-bit mem-to-reg)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_mem8_al.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_mem8_al.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge: connect al to bvchop-of-rax so Axe proofs reduce to the rax form.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function cmp_mem8_al, which
;; represents the effect of the program on the x86 state.
;; CMP [RBX], AL is encoded as 38 03 (2 bytes), so stop PC = 0x401002.
;; The base address must be canonical for the x86 model to perform the memory
;; read at [RBX] without an error branch.
(def-unrolled cmp_mem8_al
  :executable "cmp_mem8_al.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 2 (CMP [RBX], AL is 2 bytes: 38 03)
(defthm cmp_mem8_al-rip
  (equal (rip (cmp_mem8_al x86))
         (+ 2 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST (memory) is not updated, so
;; all memory is unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_mem8_al-memory-unchanged
  (equal (memi address (cmp_mem8_al x86))
         (memi address x86)))

;; All registers are unchanged (CMP does not write to any register either).
(defthm cmp_mem8_al-registers
  (equal (rgfi reg (cmp_mem8_al x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff AL > mem[RBX] unsigned (borrow):
(defthm cmp_mem8_al-cf
  (equal (get-flag :cf (cmp_mem8_al x86))
         (if (bvlt 8 (read 1 (rbx x86) x86) (al x86)) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_mem8_al-zf
  (equal (get-flag :zf (cmp_mem8_al x86))
         (if (equal 0 (bvminus 8 (read 1 (rbx x86) x86) (al x86))) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec8 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 7) of the 8-bit difference:
(defthm cmp_mem8_al-sf
  (equal (get-flag :sf (cmp_mem8_al x86))
         (getbit 7 (bvminus 8 (read 1 (rbx x86) x86) (al x86))))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < low nibble of AL:
(defthm cmp_mem8_al-af
  (equal (get-flag :af (cmp_mem8_al x86))
         (if (< (bvchop 4 (read 1 (rbx x86) x86))
                (bvchop 4 (al x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 8-bit difference overflows:
(defthm cmp_mem8_al-of
  (equal (get-flag :of (cmp_mem8_al x86))
         (let ((diff (- (logext 8 (read 1 (rbx x86) x86))
                        (logext 8 (al x86)))))
           (if (or (< diff (- (expt 2 7)))
                   (<= (expt 2 7) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

(local (defthm sub-pf-spec8-to-bvcount
  (equal (sub-pf-spec8 dst src)
         (if (evenp (bvcount 8 (bvminus 8 dst src))) 1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvchop-of-logext-same
                                     acl2::bvchop-of-minus-of-logext-gen
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_mem8_al-pf
  (equal (get-flag :pf (cmp_mem8_al x86))
         (let ((diff (bvminus 8 (read 1 (rbx x86) x86) (al x86))))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec8-to-bvcount bvminus acl2::bvchop-of-sum-cases))))

(defthm cmp_mem8_al-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_mem8_al x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
