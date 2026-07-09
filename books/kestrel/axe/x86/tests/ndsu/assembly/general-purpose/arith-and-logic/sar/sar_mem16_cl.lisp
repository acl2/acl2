; Proofs about a 1-instruction binary that shifts a memory word right by CL (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_mem16_cl.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_mem16_cl.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Rewrite cl to bvchop-of-rcx so proofs reduce to the existing rcx form.
(local (defthm cl-rewrite
  (equal (cl x86) (bvchop 8 (rcx x86)))
  :hints (("Goal" :in-theory (enable cl rcx)))))

;; Lifts the subroutine into logic: Creates the function sar_mem16_cl, which
;; represents the effect of the program on the x86 state.
;; SAR word [RBX], CL is encoded as 66 D3 3B (3 bytes), so stop PC = #x401003.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [RBX] without an error branch.
(def-unrolled sar_mem16_cl
  :executable "sar_mem16_cl.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Since the destination is not 64 bits, the count in CL is masked to
;; 5 bits (Intel SDM Vol 2B SAR entry: "tempCOUNT <- (COUNT AND 1FH)"
;; when the operand size is not 64 bits).

;; The Axe-based bvashr operator is defined only for shift amounts strictly
;; less than the operand width; per the Intel SDM, a masked count greater
;; than or equal to the operand size leaves the result and flags undefined,
;; so we state the value only for masked counts in [0, 16).
;; The word at memory address [RBX] is updated to the original
;; word shifted right by the masked count in CL, with the sign bit replicated
;; into the vacated bits on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SAR
;; entry: arithmetic right shift, size = word).
(defthm sar_mem16_cl-memory-at-rbx
  (implies (bvlt 5 (bvchop 5 (cl x86)) 16)
           (equal (read 2 (rbx x86) (sar_mem16_cl x86))
                  (bvashr 16 (read 2 (rbx x86) x86) (bvchop 5 (cl x86)))))
  :hints (("Goal" :in-theory (e/d (bvashr bvshr) (read-2-blast)))))

;; All other memory bytes are unchanged (only the 2 byte(s) at
;; [RBX]..[RBX+1] are written).
;; Condition: address is not within the 2-byte region starting at [RBX].
(defthm sar_mem16_cl-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 2))
           (equal (read 1 address (sar_mem16_cl x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (SAR word [RBX], CL is encoded as 66 D3 3B (3 bytes), so stop PC = #x401003.)
(defthm sar_mem16_cl-rip
  (equal (rip (sar_mem16_cl x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sar_mem16_cl-registers
  (equal (rgfi reg (sar_mem16_cl x86))
         (rgfi reg x86)))

;; If the masked count is 0, no flags are affected at all (Intel SDM Vol 2B
;; SAR entry: "If the count is 0, the flags are not affected.").
(defthm sar_mem16_cl-flags-unaffected-when-count-zero
  (implies (equal (bvchop 5 (cl x86)) 0)
           (equal (get-flag flag (sar_mem16_cl x86))
                  (get-flag flag x86))))

;; For a masked count strictly between 0 and the operand size, CF is set to
;; the last bit shifted out, i.e., bit (count - 1) of the original operand
;; (Intel SDM Vol 2B SAR entry).
(defthm sar_mem16_cl-cf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 16))
           (equal (get-flag :cf (sar_mem16_cl x86))
                  (getbit (+ (bvchop 5 (cl x86)) -1) (read 2 (rbx x86) x86))))
  :hints (("Goal" :in-theory (disable read-2-blast))))

;; For a masked count of exactly 1, OF is cleared to 0 (Intel SDM Vol 2B SAR
;; entry: OF is affected only on 1-bit shifts, and for SAR is always cleared
;; to 0 on a 1-bit shift since the sign bit never changes).
(defthm sar_mem16_cl-of
  (implies (equal (bvchop 5 (cl x86)) 1)
           (equal (get-flag :of (sar_mem16_cl x86))
                  0)))

;; For any nonzero masked count, the zero flag is 1 iff the result is 0.
(defthm sar_mem16_cl-zf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 16))
           (equal (get-flag :zf (sar_mem16_cl x86))
                  (if (equal 0 (bvashr 16 (read 2 (rbx x86) x86) (bvchop 5 (cl x86))))
                      1
                    0)))
  :hints (("Goal" :in-theory (e/d (bvashr bvshr zf-spec) (read-2-blast)))))

;; For any nonzero masked count, the sign flag is the sign bit (bit 15)
;; of the 16-bit result.
(defthm sar_mem16_cl-sf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 16))
           (equal (get-flag :sf (sar_mem16_cl x86))
                  (getbit 15 (bvashr 16 (read 2 (rbx x86) x86) (bvchop 5 (cl x86))))))
  :hints (("Goal" :in-theory (e/d (bvashr bvshr) (read-2-blast)))))

(local (defthm pf-spec16-alt-def
  (equal (pf-spec16 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec16 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; For any nonzero masked count, the parity flag considers only the 8 least
;; significant bits of the result and is 1 iff they contain an even number
;; of 1s.
(defthm sar_mem16_cl-pf
  (implies (and (not (equal (bvchop 5 (cl x86)) 0))
                (bvlt 5 (bvchop 5 (cl x86)) 16))
           (equal (get-flag :pf (sar_mem16_cl x86))
                  (if (evenp (bvcount 8 (bvashr 16 (read 2 (rbx x86) x86) (bvchop 5 (cl x86)))))
                      1
                    0)))
  :hints (("Goal" :in-theory (e/d (bvashr bvshr pf-spec16-alt-def) (read-2-blast)))))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags,
;; which SAR never touches regardless of the count.
(defthm sar_mem16_cl-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_mem16_cl x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
