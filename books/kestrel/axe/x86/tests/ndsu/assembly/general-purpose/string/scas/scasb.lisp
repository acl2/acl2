; Proofs about a 1-instruction binary that compares AL with [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of scasb.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "scasb.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function scasb, which
;; represents the effect of the program on the x86 state.
;; CLD; SCASB is encoded as FC AE (2 bytes), so stop PC = 0x401002.
;; The base address of the byte being scanned must be canonical for the x86
;; model to perform the memory read without an error branch.
(def-unrolled scasb
  :executable "scasb.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM SCAS/SCASB entry: temp := AL - [RDI]; CF is set if an unsigned
;; borrow occurred, i.e., if AL < [RDI].
(defthm scasb-cf
  (equal (get-flag :cf (scasb x86))
         (if (acl2::bvlt 8
               (bvchop 8 (rax x86))
               (read 1 (rdi x86) x86))
             1 0)))

;; Intel SDM: ZF is set iff the comparison result is zero, i.e., AL = [RDI].
(defthm scasb-zf
  (equal (get-flag :zf (scasb x86))
         (if (equal (bvchop 8 (rax x86))
                    (read 1 (rdi x86) x86))
             1 0))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec8))))

;; Intel SDM: SF is set to the high-order (sign) bit of the result (AL - [RDI]).
(defthm scasb-sf
  (equal (get-flag :sf (scasb x86))
         (acl2::getbit 7
           (bvminus 8
             (bvchop 8 (rax x86))
             (read 1 (rdi x86) x86))))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec8 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; Intel SDM: OF is set if the signed result does not fit in the destination.
(defthm scasb-of
  (equal (get-flag :of (scasb x86))
         (let ((sum (+ (logext 8 (bvchop 8 (rax x86)))
                       (- (logext 8 (read 1 (rdi x86) x86))))))
           (if (or (< sum (- (expt 2 7)))
                   (<= (expt 2 7) sum))
               1 0)))
  :hints (("Goal" :in-theory (enable sub-of-spec8 of-spec8 signed-byte-p))))

;; Intel SDM: AF is set if there is a borrow from bit 4 into bit 3 (i.e., the
;; low nibble of AL is less than the low nibble of [RDI]).
(defthm scasb-af
  (equal (get-flag :af (scasb x86))
         (if (< (bvchop 4 (bvchop 8 (rax x86)))
                (bvchop 4 (read 1 (rdi x86) x86)))
             1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; Intel SDM: PF is set iff the low-order 8 bits of the result have an even
;; number of 1s.
(defthm scasb-pf
  (equal (get-flag :pf (scasb x86))
         (if (evenp (acl2::logcount
                      (bvminus 8
                        (bvchop 8 (rax x86))
                        (read 1 (rdi x86) x86))))
             1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec8 pf-spec8 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Intel SDM: RDI advances by 1 (the operand size), since DF=0 after CLD
;; (Intel SDM SCAS/SCASB entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 1). This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; SCASB; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm scasb-rdi
  (equal (rdi (scasb x86))
         (bvplus 64 (rdi x86) 1))
  :hints (("Goal" :in-theory (enable get-flag))))

;; Intel SDM SCAS/SCASB entry: RSI is not used by SCAS/SCASB.
(defthm scasb-rsi-unchanged
  (equal (rsi (scasb x86))
         (rsi x86)))

;; Intel SDM SCAS/SCASB entry: SCASB reads AL as its source, it does not
;; write RAX (the comparison does not modify the accumulator).
(defthm scasb-rax-unchanged
  (equal (rax (scasb x86))
         (rax x86)))

;; Intel SDM SCAS/SCASB entry: SCASB reads memory but never writes it, so
;; memory is unchanged at every address.
(defthm scasb-memory-unchanged
  (equal (read 1 address (scasb x86))
         (read 1 address x86)))

;; Intel SDM CLD entry: CLD clears DF (DF <- 0); Intel SDM SCAS/SCASB entry
;; (Flags Affected): SCASB itself does not affect DF. Combined, DF is 0 after
;; this configuration runs.
(defthm scasb-df
  (equal (get-flag :df (scasb x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->df
                                     x86isa::!rflagsbits->cf
                                     x86isa::!rflagsbits->pf
                                     x86isa::!rflagsbits->af
                                     x86isa::!rflagsbits->zf
                                     x86isa::!rflagsbits->sf
                                     x86isa::!rflagsbits->of
                                     x86isa::!rflagsbits->df))))

;; Registers other than RDI are unchanged.
(defthm scasb-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (scasb x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; The RIP is advanced by 2 (CLD; SCASB is 2 bytes: FC AE)
(defthm scasb-rip
  (equal (rip (scasb x86))
         (+ 2 #x401000)))
