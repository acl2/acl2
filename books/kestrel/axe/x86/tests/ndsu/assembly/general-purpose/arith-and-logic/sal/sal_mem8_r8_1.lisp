; Proofs about a 1-instruction binary that shifts a memory byte left by 1
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sal_mem8_r8_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sal_mem8_r8_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function sal_mem8_r8_1, which
;; represents the effect of the program on the x86 state.
;; SAL byte [R8], 1 is encoded as 41 D0 20 (3 bytes), so stop PC = 0x401003.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [R8] without an error branch.
(def-unrolled sal_mem8_r8_1
  :executable "sal_mem8_r8_1.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (r8 x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [R8] is updated to the original
;; byte shifted left by 1, filling with 0 on the right (Intel
;; SDM Vol 1 3.4.3.1 and Vol 2B SHL/SAL entry: logical left shift, size =
;; byte).
(defthm sal_mem8_r8_1-memory-at-r8
  (equal (read 1 (r8 x86) (sal_mem8_r8_1 x86))
         (bvshl 8 (read 1 (r8 x86) x86) 1))
  :hints (("Goal" :in-theory (enable bvshl))))

;; All other memory bytes are unchanged (only the 1 byte(s) at
;; [R8]..[R8+0] are written).
;; Condition: address is not within the 1-byte region starting at [R8].
(defthm sal_mem8_r8_1-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (r8 x86)) 1))
           (equal (read 1 address (sal_mem8_r8_1 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (SAL byte [R8], 1 is encoded as 41 D0 20 (3 bytes), so stop PC = 0x401003.)
(defthm sal_mem8_r8_1-rip
  (equal (rip (sal_mem8_r8_1 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sal_mem8_r8_1-registers
  (equal (rgfi reg (sal_mem8_r8_1 x86))
         (rgfi reg x86)))

;; CF is set to the last bit shifted out, i.e., bit (8 - 1) = bit 7
;; of the original operand (Intel SDM Vol 2B SHL/SAL entry).
(defthm sal_mem8_r8_1-cf
  (equal (get-flag :cf (sal_mem8_r8_1 x86))
         (getbit 7 (read 1 (r8 x86) x86))))

;; Bridge lemma: the top bit of a 1-bit left shift is the next-to-top bit of
;; the original operand.  Purely a fact about bvshl/getbit, not the x86 model.
(local (defthm getbit-7-of-bvshl-8-by-1
  (equal (getbit 7 (bvshl 8 x 1))
         (getbit 6 x))
  :hints (("Goal" :in-theory (enable bvshl)))))

;; For a 1-bit shift, OF is set to CF XOR the most-significant bit of the
;; result (Intel SDM Vol 2B SHL/SAL entry: OF affected only on 1-bit shifts;
;; for left shifts, OF = CF XOR MSB of the result).
(defthm sal_mem8_r8_1-of
  (equal (get-flag :of (sal_mem8_r8_1 x86))
         (bitxor (getbit 7 (read 1 (r8 x86) x86))
                 (getbit 7 (bvshl 8 (read 1 (r8 x86) x86) 1)))))

;; The zero flag is 1 iff the result is 0.
(defthm sal_mem8_r8_1-zf
  (equal (get-flag :zf (sal_mem8_r8_1 x86))
         (if (equal 0 (bvshl 8 (read 1 (r8 x86) x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm sal_mem8_r8_1-sf
  (equal (get-flag :sf (sal_mem8_r8_1 x86))
         (getbit 7 (bvshl 8 (read 1 (r8 x86) x86) 1)))
  :hints (("Goal" :in-theory (enable bvshl))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm sal_mem8_r8_1-pf
  (equal (get-flag :pf (sal_mem8_r8_1 x86))
         (if (evenp (bvcount 8 (bvshl 8 (read 1 (r8 x86) x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshl pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; AF is undefined for SAL (Intel SDM Vol 2B SHL/SAL entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm sal_mem8_r8_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sal_mem8_r8_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
