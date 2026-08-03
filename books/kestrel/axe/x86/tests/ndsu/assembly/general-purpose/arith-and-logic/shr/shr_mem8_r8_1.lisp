; Proofs about a 1-instruction binary that shifts a memory byte right by 1 (logical)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of shr_mem8_r8_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "shr_mem8_r8_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function shr_mem8_r8_1, which
;; represents the effect of the program on the x86 state.
;; SHR byte [R8], 1 is encoded as 41 D0 28 (3 bytes), so stop PC = #x401003.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [R8] without an error branch.
(def-unrolled shr_mem8_r8_1
  :executable "shr_mem8_r8_1.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (r8 x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [R8] is updated to the original
;; byte shifted right by 1, filling with 0 on the left (Intel SDM Vol 1 3.4.3.1
;; and Vol 2B SHR entry: logical right shift, size = byte).
(defthm shr_mem8_r8_1-memory-at-r8
  (equal (read 1 (r8 x86) (shr_mem8_r8_1 x86))
         (bvshr 8 (read 1 (r8 x86) x86) 1))
  :hints (("Goal" :in-theory (enable bvshr))))

;; All other memory bytes are unchanged (only the 1 byte(s) at
;; [R8]..[R8+0] are written).
;; Condition: address is not within the 1-byte region starting at [R8].
(defthm shr_mem8_r8_1-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (r8 x86)) 1))
           (equal (read 1 address (shr_mem8_r8_1 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (SHR byte [R8], 1 is encoded as 41 D0 28 (3 bytes), so stop PC = #x401003.)
(defthm shr_mem8_r8_1-rip
  (equal (rip (shr_mem8_r8_1 x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm shr_mem8_r8_1-registers
  (equal (rgfi reg (shr_mem8_r8_1 x86))
         (rgfi reg x86)))

;; CF is set to the last bit shifted out, i.e., bit 0 (the original LSB) of
;; the original operand (Intel SDM Vol 2B SHR entry).
(defthm shr_mem8_r8_1-cf
  (equal (get-flag :cf (shr_mem8_r8_1 x86))
         (getbit 0 (read 1 (r8 x86) x86))))

;; For a 1-bit shift, OF is set to the most-significant bit of the original
;; operand (Intel SDM Vol 2B SHR entry: OF affected only on 1-bit shifts).
(defthm shr_mem8_r8_1-of
  (equal (get-flag :of (shr_mem8_r8_1 x86))
         (getbit 7 (read 1 (r8 x86) x86))))

;; The zero flag is 1 iff the result is 0.
(defthm shr_mem8_r8_1-zf
  (equal (get-flag :zf (shr_mem8_r8_1 x86))
         (if (equal 0 (bvshr 8 (read 1 (r8 x86) x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr zf-spec))))

;; The sign flag is the sign bit (bit 7) of the 8-bit result.
(defthm shr_mem8_r8_1-sf
  (equal (get-flag :sf (shr_mem8_r8_1 x86))
         (getbit 7 (bvshr 8 (read 1 (r8 x86) x86) 1)))
  :hints (("Goal" :in-theory (enable bvshr))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm shr_mem8_r8_1-pf
  (equal (get-flag :pf (shr_mem8_r8_1 x86))
         (if (evenp (bvcount 8 (bvshr 8 (read 1 (r8 x86) x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvshr pf-spec8 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; AF is undefined for SHR (Intel SDM Vol 2B SHR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm shr_mem8_r8_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (shr_mem8_r8_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
