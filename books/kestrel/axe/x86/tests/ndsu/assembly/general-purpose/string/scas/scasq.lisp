; Proofs about a 1-instruction binary that compares RAX with [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of scasq.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "scasq.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the qword read.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function scasq, which
;; represents the effect of the program on the x86 state.
;; CLD; SCASQ is encoded as FC 48 AF (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical, for the qword being
;; scanned, for the x86 model to perform the memory read without an error
;; branch.
(def-unrolled scasq
  :executable "scasq.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rdi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the qword read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM SCAS/SCASQ entry: temp := RAX - [RDI]; CF is set if an unsigned
;; borrow occurred, i.e., if RAX < [RDI].
(defthm scasq-cf
  (equal (get-flag :cf (scasq x86))
         (if (acl2::bvlt 64
               (rax x86)
               (read 8 (rdi x86) x86))
             1 0)))

;; Intel SDM: ZF is set iff the comparison result is zero, i.e., RAX = [RDI].
(defthm scasq-zf
  (equal (get-flag :zf (scasq x86))
         (if (equal (rax x86)
                    (read 8 (rdi x86) x86))
             1 0))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec64))))

;; Intel SDM: SF is set to the high-order (sign) bit of the result (RAX - [RDI]).
(defthm scasq-sf
  (equal (get-flag :sf (scasq x86))
         (acl2::getbit 63
           (bvminus 64
             (rax x86)
             (read 8 (rdi x86) x86))))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec64 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; Intel SDM: OF is set if the signed result does not fit in the destination.
(defthm scasq-of
  (equal (get-flag :of (scasq x86))
         (let ((sum (+ (logext 64 (rax x86))
                       (- (logext 64 (read 8 (rdi x86) x86))))))
           (if (or (< sum (- (expt 2 63)))
                   (<= (expt 2 63) sum))
               1 0)))
  :hints (("Goal" :in-theory (enable sub-of-spec64 of-spec64 signed-byte-p))))

;; Intel SDM: AF is set if there is a borrow from bit 4 into bit 3 (i.e., the
;; low nibble of RAX is less than the low nibble of [RDI]).
(defthm scasq-af
  (equal (get-flag :af (scasq x86))
         (if (< (bvchop 4 (rax x86))
                (bvchop 4 (read 8 (rdi x86) x86)))
             1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; Intel SDM: PF is set iff the low-order 8 bits of the result have an even
;; number of 1s.
(defthm scasq-pf
  (equal (get-flag :pf (scasq x86))
         (if (evenp (acl2::logcount
                      (bvchop 8
                        (bvminus 64
                          (rax x86)
                          (read 8 (rdi x86) x86)))))
             1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec64 pf-spec64 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Intel SDM: RDI advances by 8 (the operand size), since DF=0 after CLD
;; (Intel SDM SCAS/SCASQ entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 8). This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; SCASQ; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm scasq-rdi
  (equal (rdi (scasq x86))
         (bvplus 64 (rdi x86) 8))
  :hints (("Goal" :in-theory (enable get-flag))))

;; Intel SDM SCAS/SCASQ entry: RSI is not used by SCAS/SCASQ.
(defthm scasq-rsi-unchanged
  (equal (rsi (scasq x86))
         (rsi x86)))

;; Intel SDM SCAS/SCASQ entry: SCASQ reads RAX as its source, it does not
;; write RAX (the comparison does not modify the accumulator).
(defthm scasq-rax-unchanged
  (equal (rax (scasq x86))
         (rax x86)))

;; Intel SDM SCAS/SCASQ entry: SCASQ reads memory but never writes it, so
;; memory is unchanged at every address.
(defthm scasq-memory-unchanged
  (equal (read 1 address (scasq x86))
         (read 1 address x86)))

;; Intel SDM CLD entry: CLD clears DF (DF <- 0); Intel SDM SCAS/SCASQ entry
;; (Flags Affected): SCASQ itself does not affect DF. Combined, DF is 0 after
;; this configuration runs.
(defthm scasq-df
  (equal (get-flag :df (scasq x86))
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
(defthm scasq-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (scasq x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; The RIP is advanced by 3 (CLD; SCASQ is 3 bytes: FC 48 AF)
(defthm scasq-rip
  (equal (rip (scasq x86))
         (+ 3 #x401000)))
