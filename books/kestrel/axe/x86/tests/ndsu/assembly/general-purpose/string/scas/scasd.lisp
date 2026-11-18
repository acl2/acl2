; Proofs about a 1-instruction binary that compares EAX with [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of scasd.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "scasd.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the dword read.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function scasd, which
;; represents the effect of the program on the x86 state.
;; CLD; SCASD is encoded as FC AF (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical, for the dword being
;; scanned, for the x86 model to perform the memory read without an error
;; branch.
(def-unrolled scasd
  :executable "scasd.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rdi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the dword read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; Intel SDM SCAS/SCASD entry: temp := EAX - [RDI]; CF is set if an unsigned
;; borrow occurred, i.e., if EAX < [RDI].
(defthm scasd-cf
  (equal (get-flag :cf (scasd x86))
         (if (acl2::bvlt 32
               (bvchop 32 (rax x86))
               (read 4 (rdi x86) x86))
             1 0)))

;; Intel SDM: ZF is set iff the comparison result is zero, i.e., EAX = [RDI].
(defthm scasd-zf
  (equal (get-flag :zf (scasd x86))
         (if (equal (bvchop 32 (rax x86))
                    (read 4 (rdi x86) x86))
             1 0))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32))))

;; Intel SDM: SF is set to the high-order (sign) bit of the result (EAX - [RDI]).
(defthm scasd-sf
  (equal (get-flag :sf (scasd x86))
         (acl2::getbit 31
           (bvminus 32
             (bvchop 32 (rax x86))
             (read 4 (rdi x86) x86))))
  :hints (("Goal" :in-theory (e/d (sub-sf-spec32 bvminus acl2::bvchop-of-sum-cases) (acl2::getbit-of-bvchop)))))

;; Intel SDM: OF is set if the signed result does not fit in the destination.
(defthm scasd-of
  (equal (get-flag :of (scasd x86))
         (let ((sum (+ (logext 32 (bvchop 32 (rax x86)))
                       (- (logext 32 (read 4 (rdi x86) x86))))))
           (if (or (< sum (- (expt 2 31)))
                   (<= (expt 2 31) sum))
               1 0)))
  :hints (("Goal" :in-theory (enable sub-of-spec32 of-spec32 signed-byte-p))))

;; Intel SDM: AF is set if there is a borrow from bit 4 into bit 3 (i.e., the
;; low nibble of EAX is less than the low nibble of [RDI]).
(defthm scasd-af
  (equal (get-flag :af (scasd x86))
         (if (< (bvchop 4 (bvchop 32 (rax x86)))
                (bvchop 4 (read 4 (rdi x86) x86)))
             1 0))
  :hints (("Goal" :in-theory (enable bvlt bvminus acl2::bvchop-of-sum-cases))))

;; Intel SDM: PF is set iff the low-order 8 bits of the result have an even
;; number of 1s.
(defthm scasd-pf
  (equal (get-flag :pf (scasd x86))
         (if (evenp (acl2::logcount
                      (bvchop 8
                        (bvminus 32
                          (bvchop 32 (rax x86))
                          (read 4 (rdi x86) x86)))))
             1 0))
  :hints (("Goal" :in-theory (enable sub-pf-spec32 pf-spec32 bvminus
                                     acl2::bvchop-of-sum-cases
                                     acl2::bvcount-becomes-logcount
                                     acl2::evenp-becomes-equal-of-0-and-getbit-0))))

;; Intel SDM: RDI advances by 4 (the operand size), since DF=0 after CLD
;; (Intel SDM SCAS/SCASD entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 4). This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; SCASD; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm scasd-rdi
  (equal (rdi (scasd x86))
         (bvplus 64 (rdi x86) 4))
  :hints (("Goal" :in-theory (enable get-flag))))

;; Intel SDM SCAS/SCASD entry: RSI is not used by SCAS/SCASD.
(defthm scasd-rsi-unchanged
  (equal (rsi (scasd x86))
         (rsi x86)))

;; Intel SDM SCAS/SCASD entry: SCASD reads EAX as its source, it does not
;; write RAX (the comparison does not modify the accumulator).
(defthm scasd-rax-unchanged
  (equal (rax (scasd x86))
         (rax x86)))

;; Intel SDM SCAS/SCASD entry: SCASD reads memory but never writes it, so
;; memory is unchanged at every address.
(defthm scasd-memory-unchanged
  (equal (read 1 address (scasd x86))
         (read 1 address x86)))

;; Intel SDM CLD entry: CLD clears DF (DF <- 0); Intel SDM SCAS/SCASD entry
;; (Flags Affected): SCASD itself does not affect DF. Combined, DF is 0 after
;; this configuration runs.
(defthm scasd-df
  (equal (get-flag :df (scasd x86))
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
(defthm scasd-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (scasd x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; The RIP is advanced by 2 (CLD; SCASD is 2 bytes: FC AF)
(defthm scasd-rip
  (equal (rip (scasd x86))
         (+ 2 #x401000)))
