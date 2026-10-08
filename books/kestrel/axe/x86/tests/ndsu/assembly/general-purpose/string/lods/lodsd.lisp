; Proofs about a 1-instruction binary that loads a dword from [RSI] into EAX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of lodsd.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "lodsd.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers32" :dir :system)

;; Bridge lemma (purely about the model's readable-register machinery, not an
;; SDM-derived fact): rewrites the EAX abbreviation to the low dword of RAX,
;; so that proofs about the lifted function reduce to the rax form used
;; below.
(local (defthm eax-rewrite
  (equal (eax x86) (bvchop 32 (rax x86)))
  :hints (("Goal" :in-theory (enable eax rax)))))

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

;; Lifts the subroutine into logic: Creates the function lodsd, which
;; represents the effect of the program on the x86 state.
;; CLD; LODSD is encoded as FC AD (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical, for the source dword, for
;; the x86 model to perform the memory read without an error branch.
(def-unrolled lodsd
  :executable "lodsd.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rsi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the dword read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Bridge lemma (purely about the model's bit-vector representation, not an
;; SDM-derived fact): a 4-byte memory read always fits in 32 bits.
(local (defthm unsigned-byte-p-32-of-read-4
  (unsigned-byte-p 32 (read 4 addr x86))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-read (n 4) (size 32))
           :in-theory (disable unsigned-byte-p-of-read)))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; EAX is loaded from the dword at [RSI] (Intel SDM LODS/LODSD entry: EAX <-
;; SRC).
(defthm lodsd-eax
  (equal (bvchop 32 (rax (lodsd x86)))
         (read 4 (rsi x86) x86)))

;; Loading EAX zeros the upper 32 bits of RAX (standard x86-64 behavior for a
;; 32-bit register write; Intel SDM Vol 1, 3.4.1.1: "32-bit operands...
;; result is zero-extended to a 64-bit result").
(defthm lodsd-rax-upper-zero
  (equal (slice 63 32 (rax (lodsd x86)))
         0)
  :hints (("Goal" :in-theory (enable acl2::slice-too-high-is-0
                                     unsigned-byte-p-32-of-read-4))))

;; RSI advances by 4 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A LODS/LODSD entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 4).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at
;; the LODSD; the DF=1 (decrement) case of the SDM operation is not
;; reachable here (it would require a separate STD-based configuration).
(defthm lodsd-rsi
  (equal (rsi (lodsd x86))
         (bvplus 64 (rsi x86) 4)))

;; RDI is unchanged: LODS/LODSD does not use RDI (Intel SDM LODS/LODSD
;; entry).
(defthm lodsd-rdi-unchanged
  (equal (rdi (lodsd x86))
         (rdi x86)))

;; No flags are affected (Intel SDM LODS/LODSD entry: Flags Affected: None),
;; and CLD affects only DF, which is not read here.
(defthm lodsd-cf-unchanged
  (equal (get-flag :cf (lodsd x86))
         (get-flag :cf x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

(defthm lodsd-zf-unchanged
  (equal (get-flag :zf (lodsd x86))
         (get-flag :zf x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

(defthm lodsd-sf-unchanged
  (equal (get-flag :sf (lodsd x86))
         (get-flag :sf x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

(defthm lodsd-of-unchanged
  (equal (get-flag :of (lodsd x86))
         (get-flag :of x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

(defthm lodsd-af-unchanged
  (equal (get-flag :af (lodsd x86))
         (get-flag :af x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

(defthm lodsd-pf-unchanged
  (equal (get-flag :pf (lodsd x86))
         (get-flag :pf x86))
  :hints (("Goal" :in-theory (enable get-flag
                                     x86isa::rflagsbits->cf
                                     x86isa::rflagsbits->pf
                                     x86isa::rflagsbits->af
                                     x86isa::rflagsbits->zf
                                     x86isa::rflagsbits->sf
                                     x86isa::rflagsbits->tf
                                     x86isa::rflagsbits->intf
                                     x86isa::rflagsbits->of
                                     x86isa::rflagsbits->iopl
                                     x86isa::rflagsbits->nt
                                     x86isa::rflagsbits->rf
                                     x86isa::rflagsbits->vm
                                     x86isa::rflagsbits->ac
                                     x86isa::rflagsbits->vif
                                     x86isa::rflagsbits->vip
                                     x86isa::rflagsbits->id
                                     x86isa::!rflagsbits->df))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm lodsd-df
  (equal (get-flag :df (lodsd x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; Memory is unchanged: LODS/LODSD only reads memory, it does not write
;; (Intel SDM LODS/LODSD entry: EAX <- SRC).
(defthm lodsd-memory-unchanged
  (equal (read 1 address (lodsd x86))
         (read 1 address x86)))

;; Registers other than RAX and RSI are unchanged.
(defthm lodsd-other-registers
  (implies (and (not (equal *rax* reg))
                (not (equal *rsi* reg)))
           (equal (rgfi reg (lodsd x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax set-rsi))))

;; The RIP is advanced by 2 (CLD; LODSD is 2 bytes: FC AD)
(defthm lodsd-rip
  (equal (rip (lodsd x86))
         (+ 2 #x401000)))
