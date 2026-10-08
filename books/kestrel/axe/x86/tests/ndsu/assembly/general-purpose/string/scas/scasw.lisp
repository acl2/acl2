; Proofs about a 1-instruction binary that compares AX with [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of scasw.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "scasw.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the word read.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function scasw, which
;; represents the effect of the program on the x86 state.
;; CLD; SCASW is encoded as FC 66 AF (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical, for the word being
;; scanned, for the x86 model to perform the memory read without an error
;; branch.
(def-unrolled scasw
  :executable "scasw.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rdi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the word read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM SCAS/SCASW entry: temp := AX - [RDI]; CF is set if an unsigned
;; borrow occurred, i.e., if AX < [RDI].
(defthm scasw-cf
  (equal (get-flag :cf (scasw x86))
         (if (acl2::bvlt 16
               (bvchop 16 (rax x86))
               (read 2 (rdi x86) x86))
             1 0)))

;; Intel SDM: ZF is set iff the comparison result is zero, i.e., AX = [RDI].
(defthm scasw-zf
  (equal (get-flag :zf (scasw x86))
         (if (equal (bvchop 16 (rax x86))
                    (read 2 (rdi x86) x86))
             1 0))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec16))))

;; Intel SDM: SF is set to the high-order (sign) bit of the result (AX - [RDI]).
(defthm scasw-sf
  (equal (get-flag :sf (scasw x86))
         (acl2::getbit 15
           (bvminus 16
             (bvchop 16 (rax x86))
             (read 2 (rdi x86) x86))))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec16 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; Intel SDM: OF is set if the signed result does not fit in the destination.
(defthm scasw-of
  (equal (get-flag :of (scasw x86))
         (let ((sum (+ (logext 16 (bvchop 16 (rax x86)))
                       (- (logext 16 (read 2 (rdi x86) x86))))))
           (if (or (< sum (- (expt 2 15)))
                   (<= (expt 2 15) sum))
               1 0)))
  :hints (("Goal" :in-theory (enable sub-of-spec16 of-spec16 signed-byte-p))))

;; Intel SDM: AF is set if there is a borrow from bit 4 into bit 3 (i.e., the
;; low nibble of AX is less than the low nibble of [RDI]).
(defthm scasw-af
  (equal (get-flag :af (scasw x86))
         (if (< (bvchop 4 (bvchop 16 (rax x86)))
                (bvchop 4 (read 2 (rdi x86) x86)))
             1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; Intel SDM: PF is set iff the low-order 8 bits of the result have an even
;; number of 1s.
(defthm scasw-pf
  (equal (get-flag :pf (scasw x86))
         (if (evenp (acl2::logcount
                      (bvchop 8
                        (bvminus 16
                          (bvchop 16 (rax x86))
                          (read 2 (rdi x86) x86)))))
             1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec16 pf-spec16 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Intel SDM: RDI advances by 2 (the operand size), since DF=0 after CLD
;; (Intel SDM SCAS/SCASW entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 2). This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; SCASW; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm scasw-rdi
  (equal (rdi (scasw x86))
         (bvplus 64 (rdi x86) 2))
  :hints (("Goal" :in-theory (enable get-flag))))

;; Intel SDM SCAS/SCASW entry: RSI is not used by SCAS/SCASW.
(defthm scasw-rsi-unchanged
  (equal (rsi (scasw x86))
         (rsi x86)))

;; Intel SDM SCAS/SCASW entry: SCASW reads AX as its source, it does not
;; write RAX (the comparison does not modify the accumulator).
(defthm scasw-rax-unchanged
  (equal (rax (scasw x86))
         (rax x86)))

;; Intel SDM SCAS/SCASW entry: SCASW reads memory but never writes it, so
;; memory is unchanged at every address.
(defthm scasw-memory-unchanged
  (equal (read 1 address (scasw x86))
         (read 1 address x86)))

;; Intel SDM CLD entry: CLD clears DF (DF <- 0); Intel SDM SCAS/SCASW entry
;; (Flags Affected): SCASW itself does not affect DF. Combined, DF is 0 after
;; this configuration runs.
(defthm scasw-df
  (equal (get-flag :df (scasw x86))
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
(defthm scasw-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (scasw x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; The RIP is advanced by 3 (CLD; SCASW is 3 bytes: FC 66 AF)
(defthm scasw-rip
  (equal (rip (scasw x86))
         (+ 3 #x401000)))
