; Proofs about a 1-instruction binary that ANDs a memory qword into RAX (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of and_rax_mem64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "and_rax_mem64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function and_rax_mem64, which
;; represents the effect of the program on the x86 state.
;; AND RAX, [RBX] is encoded as 48 23 03 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical for the 64-bit read.
(def-unrolled and_rax_mem64
  :executable "and_rax_mem64.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 64-bit AND of the initial RAX and the memory qword at [RBX].
(defthm and_rax_mem64-rax
  (equal (rax (and_rax_mem64 x86))
         (bvand 64 (rax x86) (read 8 (rbx x86) x86))))

;; The RIP is advanced by 3 (AND RAX, [RBX] is 3 bytes: REX.W 23 03 = 48 23 03)
(defthm and_rax_mem64-rip
  (equal (rip (and_rax_mem64 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm and_rax_mem64-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (and_rax_mem64 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax ; todo
                                     ))))

;; Intel SDM Vol 2A AND entry: CF is cleared to 0.
(defthm and_rax_mem64-cf
  (equal (get-flag :cf (and_rax_mem64 x86))
         0))

;; Intel SDM Vol 2A AND entry: OF is cleared to 0.
(defthm and_rax_mem64-of
  (equal (get-flag :of (and_rax_mem64 x86))
         0))

;; The zero flag is 1 iff the 64-bit AND result is 0.
(defthm and_rax_mem64-zf
  (equal (get-flag :zf (and_rax_mem64 x86))
         (if (equal 0 (bvand 64 (rax x86) (read 8 (rbx x86) x86)))
             1
           0)))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm and_rax_mem64-sf
  (equal (get-flag :sf (and_rax_mem64 x86))
         (getbit 63 (bvand 64 (rax x86) (read 8 (rbx x86) x86)))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm and_rax_mem64-pf
  (equal (get-flag :pf (and_rax_mem64 x86))
         (if (evenp (bvcount 8 (bvand 64 (rax x86) (read 8 (rbx x86) x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def))))

;; All memory addresses are unchanged (instruction reads from memory but does not write).
(defthm and_rax_mem64-memory-unchanged
  (equal (memi address (and_rax_mem64 x86))
         (memi address x86)))

(defthm and_rax_mem64-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (and_rax_mem64 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
