; Proofs about a 1-instruction binary that subtracts a memory qword from RAX (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sub_rax_mem64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sub_rax_mem64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sub_rax_mem64, which
;; represents the effect of the program on the x86 state.
;; SUB RAX, [RBX] is encoded as 48 2B 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit read.
(def-unrolled sub_rax_mem64
  :executable "sub_rax_mem64.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 64-bit difference: DEST <- DEST - SRC (Intel SDM Vol 2A).
(defthm sub_rax_mem64-rax
  (equal (rax (sub_rax_mem64 x86))
         (bvminus 64 (rax x86) (read 8 (rbx x86) x86))))

;; The RIP is advanced by 3 (SUB RAX, [RBX] is 3 bytes: REX.W 2B 03 = 48 2B 03)
(defthm sub_rax_mem64-rip
  (equal (rip (sub_rax_mem64 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm sub_rax_mem64-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (sub_rax_mem64 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is 1 iff mem[RBX] > RAX unsigned (borrow):
(defthm sub_rax_mem64-cf
  (equal (get-flag :cf (sub_rax_mem64 x86))
         (if (bvlt 64 (rax x86) (read 8 (rbx x86) x86)) 1 0)))

;; The zero flag is 1 iff the result is zero:
(defthm sub_rax_mem64-zf
  (equal (get-flag :zf (sub_rax_mem64 x86))
         (if (equal 0 (bvminus 64 (rax x86) (read 8 (rbx x86) x86))) 1 0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result:
(defthm sub_rax_mem64-sf
  (equal (get-flag :sf (sub_rax_mem64 x86))
         (getbit 63 (bvminus 64 (rax x86) (read 8 (rbx x86) x86))))
  :hints (("Goal" :in-theory (enable bvminus))))

;; The auxiliary carry (borrow) flag is 1 iff the low nibble of RAX < low nibble of mem[RBX]:
(defthm sub_rax_mem64-af
  (equal (get-flag :af (sub_rax_mem64 x86))
         (if (< (bvchop 4 (rax x86))
                (bvchop 4 (read 8 (rbx x86) x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; The overflow flag is 1 iff the signed 64-bit result overflows:
(defthm sub_rax_mem64-of
  (equal (get-flag :of (sub_rax_mem64 x86))
         (let ((diff (- (logext 64 (rax x86))
                        (logext 64 (read 8 (rbx x86) x86)))))
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

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm sub_rax_mem64-pf
  (equal (get-flag :pf (sub_rax_mem64 x86))
         (let ((diff (bvminus 64 (rax x86) (read 8 (rbx x86) x86))))
           (if (evenp (bvcount 8 diff)) 1 0)))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def bvminus))))

;; All memory addresses are unchanged (instruction reads from memory but does not write):
(defthm sub_rax_mem64-memory-unchanged
  (equal (memi address (sub_rax_mem64 x86))
         (memi address x86)))

(defthm sub_rax_mem64-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sub_rax_mem64 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
