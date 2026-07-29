; Proofs about a 1-instruction binary that shifts a memory byte left by 3
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shl_mem8_r8_imm8.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shl_mem8_r8_imm8.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function shl_mem8_r8_imm8, which
;; represents the effect of the program on the x86 state.
;; SHL byte [R8], 3 is encoded as 41 C0 20 03 (4 bytes), so stop PC = 0x401004.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [R8] without an error branch.
(def-unrolled shl_mem8_r8_imm8
  :executable "shl_mem8_r8_imm8.elf64"
  :target #x401000
  :stop-pcs '(#x401004)
  :extra-assumptions '((unsigned-canonical-address-p (r8 x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [R8] is updated to the original
;; byte shifted left by 3, filling with 0 on the right (Intel
;; SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift, size =
;; byte).
(defthm shl_mem8_r8_imm8-memory-at-r8
  (equal (read 1 (r8 x86) (shl_mem8_r8_imm8 x86))
         (bvshl 8 (read 1 (r8 x86) x86) 3))
  :hints (("Goal" :in-theory (enable bvshl))))

;; All other memory bytes are unchanged (only the 1 byte(s) at
;; [R8]..[R8+0] are written).
;; Condition: address is not within the 1-byte region starting at [R8].
(defthm shl_mem8_r8_imm8-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (r8 x86)) 1))
           (equal (read 1 address (shl_mem8_r8_imm8 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 4 (SHL byte [R8], 3 is encoded as 41 C0 20 03 (4 bytes), so stop PC = 0x401004.)
(defthm shl_mem8_r8_imm8-rip
  (equal (rip (shl_mem8_r8_imm8 x86))
         (+ 4 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm shl_mem8_r8_imm8-registers
  (equal (rgfi reg (shl_mem8_r8_imm8 x86))
         (rgfi reg x86)))

;; CF is set to the last bit shifted out, i.e., bit (8 - 3) = bit 5
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm shl_mem8_r8_imm8-cf
  (equal (get-flag :cf (shl_mem8_r8_imm8 x86))
         (getbit 5 (read 1 (r8 x86) x86))))

;; OF is undefined for shifts other than by 1 (Intel SDM Vol 2B SHL/SAL
;; entry: "The OF flag is affected only on 1-bit shifts."), so no theorem is
;; stated for it here.

;; The zero flag is 1 iff the result is 0.
(defthm shl_mem8_r8_imm8-zf
  (equal (get-flag :zf (shl_mem8_r8_imm8 x86))
         (if (equal 0 (bvshl 8 (read 1 (r8 x86) x86) 3))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm shl_mem8_r8_imm8-sf
  (equal (get-flag :sf (shl_mem8_r8_imm8 x86))
         (getbit 7 (bvshl 8 (read 1 (r8 x86) x86) 3)))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shl_mem8_r8_imm8-pf
  (equal (get-flag :pf (shl_mem8_r8_imm8 x86))
         (if (evenp (bvcount 8 (bvshl 8 (read 1 (r8 x86) x86) 3)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; AF is undefined for SHL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shl_mem8_r8_imm8-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shl_mem8_r8_imm8 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
