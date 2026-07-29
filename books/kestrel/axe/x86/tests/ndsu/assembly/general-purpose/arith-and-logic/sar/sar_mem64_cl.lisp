; Proofs about a 1-instruction binary that shifts a memory qword right by CL (arithmetic)
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of sar_mem64_cl.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "sar_mem64_cl.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Rewrite cl to bvchop-of-rcx so proofs reduce to the existing rcx form.
(local (defthm cl-rewrite
  (equal (cl x86) (bvchop 8 (rcx x86)))
  :hints (("Goal" :in-theory (enable cl rcx)))))

;; Lifts the subroutine into logic: Creates the function sar_mem64_cl, which
;; represents the effect of the program on the x86 state.
;; SAR qword [RBX], CL is encoded as 48 D3 3B (3 bytes), so stop PC = #x401003.
;; The relevant address(es) must be canonical for the x86 model to perform
;; the memory read/write at [RBX] without an error branch.
(def-unrolled sar_mem64_cl
  :executable "sar_mem64_cl.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rbx x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rbx x86)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Since the destination is 64 bits (REX.W is used), the count in CL is masked to
;; 6 bits (Intel SDM Vol 2B SAR entry: "tempCOUNT <- (COUNT AND 3FH)"
;; when the operand size is 64 bits).

;; The qword at memory address [RBX] is updated to the original
;; qword shifted right by the masked count in CL, with the sign bit replicated
;; into the vacated bits on the left (Intel SDM Vol 1 3.4.3.1 and Vol 2B SAR
;; entry: arithmetic right shift, size = qword).
(defthm sar_mem64_cl-memory-at-rbx
  (equal (read 8 (rbx x86) (sar_mem64_cl x86))
         (bvashr 64 (read 8 (rbx x86) x86) (bvchop 6 (cl x86))))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

;; All other memory bytes are unchanged (only the 8 byte(s) at
;; [RBX]..[RBX+7] are written).
;; Condition: address is not within the 8-byte region starting at [RBX].
(defthm sar_mem64_cl-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rbx x86)) 8))
           (equal (read 1 address (sar_mem64_cl x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (SAR qword [RBX], CL is encoded as 48 D3 3B (3 bytes), so stop PC = #x401003.)
(defthm sar_mem64_cl-rip
  (equal (rip (sar_mem64_cl x86))
         (+ 3 #x401000)))

;; All registers are unchanged (the destination is memory, not a register).
(defthm sar_mem64_cl-registers
  (equal (rgfi reg (sar_mem64_cl x86))
         (rgfi reg x86)))

;; If the masked count is 0, no flags are affected at all (Intel SDM Vol 2B
;; SAR entry: "If the count is 0, the flags are not affected.").
(defthm sar_mem64_cl-flags-unaffected-when-count-zero
  (implies (equal (bvchop 6 (cl x86)) 0)
           (equal (get-flag flag (sar_mem64_cl x86))
                  (get-flag flag x86))))

;; For a masked count strictly between 0 and the operand size, CF is set to
;; the last bit shifted out, i.e., bit (count - 1) of the original operand
;; (Intel SDM Vol 2B SAR entry).
(defthm sar_mem64_cl-cf
  (implies (and (not (equal (bvchop 6 (cl x86)) 0))
                (bvlt 6 (bvchop 6 (cl x86)) 64))
           (equal (get-flag :cf (sar_mem64_cl x86))
                  (getbit (+ (bvchop 6 (cl x86)) -1) (read 8 (rbx x86) x86)))))

;; For a masked count of exactly 1, OF is cleared to 0 (Intel SDM Vol 2B SAR
;; entry: OF is affected only on 1-bit shifts, and for SAR is always cleared
;; to 0 on a 1-bit shift since the sign bit never changes).
(defthm sar_mem64_cl-of
  (implies (equal (bvchop 6 (cl x86)) 1)
           (equal (get-flag :of (sar_mem64_cl x86))
                  0)))

;; For any nonzero masked count, the zero flag is 1 iff the result is 0.
(defthm sar_mem64_cl-zf
  (implies (not (equal (bvchop 6 (cl x86)) 0))
           (equal (get-flag :zf (sar_mem64_cl x86))
                  (if (equal 0 (bvashr 64 (read 8 (rbx x86) x86) (bvchop 6 (cl x86))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvashr bvshr zf-spec))))

;; For any nonzero masked count, the sign flag is the sign bit (bit 63)
;; of the 64-bit result.
(defthm sar_mem64_cl-sf
  (implies (not (equal (bvchop 6 (cl x86)) 0))
           (equal (get-flag :sf (sar_mem64_cl x86))
                  (getbit 63 (bvashr 64 (read 8 (rbx x86) x86) (bvchop 6 (cl x86))))))
  :hints (("Goal" :in-theory (enable bvashr bvshr))))

(local (defthm pf-spec64-alt-def
  (equal (pf-spec64 res)
         (if (evenp (bvcount 8 res))
             1
           0))
  :hints (("Goal" :in-theory (enable pf-spec64 acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0)))))

;; For any nonzero masked count, the parity flag considers only the 8 least
;; significant bits of the result and is 1 iff they contain an even number
;; of 1s.
(defthm sar_mem64_cl-pf
  (implies (not (equal (bvchop 6 (cl x86)) 0))
           (equal (get-flag :pf (sar_mem64_cl x86))
                  (if (evenp (bvcount 8 (bvashr 64 (read 8 (rbx x86) x86) (bvchop 6 (cl x86)))))
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bvashr bvshr pf-spec64-alt-def))))

;; AF is undefined for SAR (Intel SDM Vol 2B SAR entry), so no theorem is
;; stated for it here. The theorem below covers only the non-standard flags,
;; which SAR never touches regardless of the count.
(defthm sar_mem64_cl-other-flags
  (implies (and (member-equal flag *flags*)
                (not (member-eq flag *standard-flags*)))
           (equal (get-flag flag (sar_mem64_cl x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant))))
