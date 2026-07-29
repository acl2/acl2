; Proofs about a 1-instruction binary that shifts a memory dword right by 1 (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_mem32_1.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_mem32_1.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function sar_mem32_1, which
;; represents the effect of the program on the x86 state.
;; SAR dword [RBX], 1 is encoded as D1 3B (2 bytes), so stop PC = #x401002.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [RBX] without an error branch.
(def-unrolled sar_mem32_1
  :executable "sar_mem32_1.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The dword at memory address [RBX] is updated to the original
;; dword shifted right by 1, with the sign bit replicated into the vacated bit
;; on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SAR entry: arithmetic right
;; shift, size = dword).
(defthm sar_mem32_1-memory-at-rbx
  (equal (read 4 (rbx x86) (sar_mem32_1 x86))
         (bvashr 32 (read 4 (rbx x86) x86) 1))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; All other memory bytes are unchanged (only the 4 byte(s) at
;; [RBX]..[RBX+3] are written).
;; Condition: address is not within the 4-byte region starting at [RBX].
(defthm sar_mem32_1-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 4))
           (equal (read 1 address (sar_mem32_1 x86))
                  (read 1 address x86))))

;; The RIP is advanced by 2 (SAR dword [RBX], 1 is encoded as D1 3B (2 bytes), so stop PC = #x401002.)
(defthm sar_mem32_1-rip
  (equal (rip (sar_mem32_1 x86))
         (+ 2 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sar_mem32_1-registers
  (equal (rgfi reg (sar_mem32_1 x86))
         (rgfi reg x86)))

;; CF is set to the last bit shifted out, i.e., bit 0 (the original LSB) of
;; the original operand (Intel SDM Vol 2B SAR entry).
(defthm sar_mem32_1-cf
  (equal (get-flag :cf (sar_mem32_1 x86))
         (getbit 0 (read 4 (rbx x86) x86))))

;; OF is cleared to 0 for all 1-bit shifts of SAR, since the sign bit never
;; changes (Intel SDM Vol 2B SAR entry).
(defthm sar_mem32_1-of
  (equal (get-flag :of (sar_mem32_1 x86))
         0))

;; The zero flag is 1 iff the result is 0.
(defthm sar_mem32_1-zf
  (equal (get-flag :zf (sar_mem32_1 x86))
         (if (equal 0 (bvashr 32 (read 4 (rbx x86) x86) 1))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr zf-spec))))

;; The sign flag is the sign bit (bit 31) of the 32-bit result.
(defthm sar_mem32_1-sf
  (equal (get-flag :sf (sar_mem32_1 x86))
         (getbit 31 (bvashr 32 (read 4 (rbx x86) x86) 1)))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

(local (defthm pf-spec32-alt-def
  (equal (pf-spec32 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec32 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; The parity flag considers only the 8 least significant bits of the result
;; and is 1 iff they contain an even number of 1s.
(defthm sar_mem32_1-pf
  (equal (get-flag :pf (sar_mem32_1 x86))
         (if (evenp (bvcount 8 (bvashr 32 (read 4 (rbx x86) x86) 1)))
             1
           0))
  :hints (("Goal" :in-theory (enable bvashr bvshr pf-spec32-alt-def))))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags.
(defthm sar_mem32_1-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_mem32_1 x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
