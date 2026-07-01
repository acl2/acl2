; Proofs about a 1-instruction binary that ORs an immediate to BX (16-bit)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of or_bx_imm16.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "or_bx_imm16.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite bx to bvchop-of-rbx so proofs reduce to the rbx form.
(local (defthm bx-rewrite
  (equal (bx x86) (bvchop 16 (rbx x86)))
  :hints (("Goal" :in-theory (enable bx rbx)))))

;; Lifts the subroutine into logic: Creates the function or_bx_imm16, which
;; represents the effect of the program on the x86 state.
;; OR BX, 300 is encoded as 66 81 CB 2C 01 (5 bytes), so stop PC = 0x401005.
(def-unrolled or_bx_imm16
  :executable "or_bx_imm16.elf64"
  :target #x401000
  :stop-pcs '(#x401005))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RBX after the operation: only BX (bits 0-15) is updated; bits 16-63 of RBX
;; are preserved (16-bit ops do not zero-extend in 64-bit mode).
(defthm or_bx_imm16-rbx
  (equal (rbx (or_bx_imm16 x86))
         (bvcat 48 (slice 63 16 (rbx x86)) 16 (bvor 16 (rbx x86) 300))))

;; BX after the operation: the natural 16-bit statement of the result.
;; (Intel SDM Vol 2A: DEST <- DEST OR SRC)
(defthm or_bx_imm16-bx
  (equal (bx (or_bx_imm16 x86))
         (bvor 16 (bx x86) 300)))

;; The RIP is advanced by 5 (OR BX, imm16 is 5 bytes: 66 81 CB 2C 01)
(defthm or_bx_imm16-rip
  (equal (rip (or_bx_imm16 x86))
         (+ 5 #x401000)))

;; Registers other than RBX are unchanged.
(defthm or_bx_imm16-other-registers
  (implies (not (equal *rbx* reg))
           (equal (rgfi reg (or_bx_imm16 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rbx))))

;; The carry flag is cleared to 0 (Intel SDM Vol 2A: OR clears CF).
(defthm or_bx_imm16-cf
  (equal (get-flag :cf (or_bx_imm16 x86))
         0))

;; The overflow flag is cleared to 0 (Intel SDM Vol 2A: OR clears OF).
(defthm or_bx_imm16-of
  (equal (get-flag :of (or_bx_imm16 x86))
         0))

;; The zero flag is 1 iff the OR result is 0.
(defthm or_bx_imm16-zf
  (equal (get-flag :zf (or_bx_imm16 x86))
         (if (equal 0 (bvor 16 (bx x86) 300))
             1
           0)))

;; The sign flag is the sign bit (bit 15) of the 16-bit result.
(defthm or_bx_imm16-sf
  (equal (get-flag :sf (or_bx_imm16 x86))
         (getbit 15 (bvor 16 (bx x86) 300))))

(defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; The parity flag considers only the 8 least significant bits and is 1 iff
;; they contain an even number of 1s.
(defthm or_bx_imm16-pf
  (equal (get-flag :pf (or_bx_imm16 x86))
         (if (evenp (bvcount 8 (bvor 16 (bx x86) 300)))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16-alt-def))))

;; All memory addresses are unchanged.
(defthm or_bx_imm16-memory-unchanged
  (equal (memi address (or_bx_imm16 x86))
         (memi address x86)))

(defthm or_bx_imm16-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (or_bx_imm16 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
