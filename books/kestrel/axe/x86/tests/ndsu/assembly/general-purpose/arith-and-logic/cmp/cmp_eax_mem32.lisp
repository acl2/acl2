; Proofs about a 1-instruction binary that compares EAX to a memory dword (32-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of cmp_eax_mem32.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "cmp_eax_mem32.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Rewrite eax to bvchop-of-rax so proofs reduce to the rax form.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

;; Lifts the subroutine into logic: Creates the function cmp_eax_mem32, which
;; represents the effect of the program on the x86 state.
;; CMP EAX, [RBX] is encoded as 3B 03 (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical for the 32-bit read.
(def-unrolled cmp_eax_mem32
  :executable "cmp_eax_mem32.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The RIP is advanced by 2 (CMP EAX, [RBX] is 2 bytes: 3B 03)
(defthm cmp_eax_mem32-rip
  (equal (rip (cmp_eax_mem32 x86))
         (+ 2 #x401000)))

;; CMP computes DEST - SRC only to set flags; DEST is not updated, so all
;; registers are unchanged (Intel SDM Vol 2A: CMP entry).
(defthm cmp_eax_mem32-registers
  (equal (rgfi reg (cmp_eax_mem32 x86))
         (rgfi reg x86)))

;; The carry flag is 1 iff mem[RBX] > EAX unsigned (borrow):
(defthm cmp_eax_mem32-cf
  (equal (get-flag :cf (cmp_eax_mem32 x86))
         (if (bvlt 32 (eax x86) (read 4 (rbx x86) x86)) 1 0)))

;; The zero flag is 1 iff the (uncommitted) difference is zero:
(defthm cmp_eax_mem32-zf
  (equal (get-flag :zf (cmp_eax_mem32 x86))
         (if (equal 0 (bvminus 32 (eax x86) (read 4 (rbx x86) x86))) 1 0))
  :hints (("Goal" :in-theory (enable sub-zf-spec32 acl2::equal-of-0-and-bvminus))))

;; The sign flag is the sign bit (bit 31) of the 32-bit difference:
(defthm cmp_eax_mem32-sf
  (equal (get-flag :sf (cmp_eax_mem32 x86))
         (getbit 31 (bvminus 32 (eax x86) (read 4 (rbx x86) x86))))
  :hints (("Goal" :in-theory ( e/d (sub-sf-spec32 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of EAX < low nibble of mem[RBX]:
(defthm cmp_eax_mem32-af
  (equal (get-flag :af (cmp_eax_mem32 x86))
         (if (< (bvchop 4 (eax x86))
                (bvchop 4 (read 4 (rbx x86) x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 32-bit difference overflows:
(defthm cmp_eax_mem32-of
  (equal (get-flag :of (cmp_eax_mem32 x86))
         (let ((diff (- (logext 32 (eax x86))
                        (logext 32 (read 4 (rbx x86) x86)))))
           (if (or (< diff (- (expt 2 31)))
                   (<= (expt 2 31) diff))
               1
             0)))
  :hints (("Goal" :in-theory (enable sub-of-spec32 of-spec32 signed-byte-p))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res)) 1 0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the difference and
;; is 1 iff they contain an even number of 1s.
(defthm cmp_eax_mem32-pf
  (equal (get-flag :pf (cmp_eax_mem32 x86))
         (if (evenp (bvcount 8 (bvminus 32 (eax x86) (read 4 (rbx x86) x86)))) 1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec32 pf-spec32-alt-def bvminus acl2::bvchop-of-sum-cases))))

;; All memory addresses are unchanged (instruction reads from memory but does not write):
(defthm cmp_eax_mem32-memory-unchanged
  (equal (memi address (cmp_eax_mem32 x86))
         (memi address x86)))

(defthm cmp_eax_mem32-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (cmp_eax_mem32 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
