; Proofs about a 1-instruction binary that XORs 2 numbers (64-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of xor_rax_rbx_64.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "xor_rax_rbx_64.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function xor_rax_rbx_64, which
;; represents the effect of the program on the x86 state.
;; XOR RAX, RBX is encoded as 48 31 D8 (3 bytes), so stop PC = 0x401003.
(def-unrolled xor_rax_rbx_64
  :executable "xor_rax_rbx_64.elf64"
  :target #x401000
  :stop-pcs '(#x401003))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX contains the 64-bit XOR of the initial RAX and RBX.
(defthm xor_rax_rbx_64-rax
  (equal (rax (xor_rax_rbx_64 x86))
         (bvxor 64 (rax x86) (rbx x86))))

;; The RIP is advanced by 3 (XOR RAX,RBX is 3 bytes: REX.W 31 D8 = 48 31 D8)
(defthm xor_rax_rbx_64-rip
  (equal (rip (xor_rax_rbx_64 x86))
         (+ 3 #x401000)))

;; Registers other than RAX are unchanged.
(defthm xor_rax_rbx_64-other-registers
  (implies (not (equal *rax* reg))
           (equal (rgfi reg (xor_rax_rbx_64 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: XOR clears CF).
(defthm xor_rax_rbx_64-cf
  (equal (get-flag :cf (xor_rax_rbx_64 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: XOR clears OF).
(defthm xor_rax_rbx_64-of
  (equal (get-flag :of (xor_rax_rbx_64 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm xor_rax_rbx_64-zf
  (equal (get-flag :zf (xor_rax_rbx_64 x86))
         (if (equal 0 (bvxor 64 (rax x86) (rbx x86)))
             1
           0))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; The sign flag is the sign bit (bit 63) of the 64-bit result.
(defthm xor_rax_rbx_64-sf
  (equal (get-flag :sf (xor_rax_rbx_64 x86))
         (getbit 63 (bvxor 64 (rax x86) (rbx x86)))))

(defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm xor_rax_rbx_64-pf
  (equal (get-flag :pf (xor_rax_rbx_64 x86))
         (if (evenp (bvcount 8 (bvxor 64 (rax x86) (rbx x86))))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64-alt-def))))

;; All memory addresses are unchanged
(defthm xor_rax_rbx_64-memory-unchanged
  (equal (memi address (xor_rax_rbx_64 x86))
         (memi address x86)))

(defthm xor_rax_rbx_64-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (xor_rax_rbx_64 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
