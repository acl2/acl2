; Proofs about a 1-instruction binary that compares a memory qword to RAX (64-bit mem-to-reg)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_mem64_rax.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_mem64_rax.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function cmp_mem64_rax, which
;; represents the effect of the program on the x86 state.
;; CMP [RBX], RAX is encoded as 48 39 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit read.
(def-unrolled cmp_mem64_rax
  :executable "cmp_mem64_rax.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 3 (CMP [RBX], RAX is 3 bytes: REX.W 39 03 = 48 39 03)
(defthm cmp_mem64_rax-rip
  (equal (rip (cmp_mem64_rax x86))
         (+ 3 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST (memory) is not updated, so
;; all memory is unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_mem64_rax-memory-unchanged
  (equal (memi address (cmp_mem64_rax x86))
         (memi address x86)))

;; All registers are unchanged (CMP does not write to any register either).
(defthm cmp_mem64_rax-registers
  (equal (rgfi reg (cmp_mem64_rax x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff RAX > mem[RBX] unsigned (borrow):
(defthm cmp_mem64_rax-cf
  (equal (get-flag :cf (cmp_mem64_rax x86))
         (if (bvlt 64 (read 8 (rbx x86) x86) (rax x86)) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_mem64_rax-zf
  (equal (get-flag :zf (cmp_mem64_rax x86))
         (if (equal 0 (bvminus 64 (read 8 (rbx x86) x86) (rax x86))) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec64 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 63) of the 64-bit difference:
(defthm cmp_mem64_rax-sf
  (equal (get-flag :sf (cmp_mem64_rax x86))
         (getbit 63 (bvminus 64 (read 8 (rbx x86) x86) (rax x86))))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec64 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of mem[RBX] < low nibble of RAX:
(defthm cmp_mem64_rax-af
  (equal (get-flag :af (cmp_mem64_rax x86))
         (if (< (bvchop 4 (read 8 (rbx x86) x86))
                (bvchop 4 (rax x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 64-bit difference overflows:
(defthm cmp_mem64_rax-of
  (equal (get-flag :of (cmp_mem64_rax x86))
         (let ((diff (- (logext 64 (read 8 (rbx x86) x86))
                        (logext 64 (rax x86)))))
           (if (or (< diff (- (expt 2 63)))
                   (<= (expt 2 63) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec64 of-spec64 signed-byte-p))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

(local (defthm sub-pf-spec64-to-bvcount
  (equal (sub-pf-spec64 dst src)
         (if (evenp (bvcount 8 (bvminus 64 dst src))) 1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec64 pf-spec64-alt-def bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvchop-of-logext-same
                                     acl2::bvchop-of-minus-of-logext-gen)))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_mem64_rax-pf
  (equal (get-flag :pf (cmp_mem64_rax x86))
         (let ((diff (bvminus 64 (read 8 (rbx x86) x86) (rax x86))))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable sub-pf-spec64-to-bvcount bvminus acl2::bvchop-of-sum-cases))))

(defthm cmp_mem64_rax-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_mem64_rax x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
