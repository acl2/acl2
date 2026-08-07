; Proofs about a 1-instruction binary that moves a qword from [RSI] to [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of movsq.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "movsq.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the qword read/write.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function movsq, which
;; represents the effect of the program on the x86 state.
;; CLD; MOVSQ is encoded as FC 48 A5 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical, for the source and
;; destination qwords, for the x86 model to perform the memory read/write
;; without an error branch.
(def-unrolled movsq
  :executable "movsq.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rsi x86)))
                       (unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rdi x86))))
  ;; Needed so the model can see that reading the source qword from memory
  ;; does not change the state, so that the destination address (computed
  ;; from RDI, which the read does not touch) can be checked for
  ;; canonicity, and so that alignment checking (unaffected by CLD) can be
  ;; resolved without exposing the flag reconstruction to later proofs.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RDI] is updated to the original qword at
;; [RSI] (Intel SDM Vol 2A MOVS/MOVSQ entry: DEST <- SRC, size = qword).
(defthm movsq-memory-at-rdi
  (equal (read 8 (rdi x86) (movsq x86))
         (read 8 (rsi x86) x86)))

;; All other memory bytes are unchanged (only the qword at [RDI] is
;; written).  Condition: address is not within the 8-byte region starting
;; at [RDI].
(defthm movsq-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 8))
           (equal (read 1 address (movsq x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (CLD; MOVSQ is 3 bytes: FC 48 A5)
(defthm movsq-rip
  (equal (rip (movsq x86))
         (+ 3 #x401000)))

;; RSI advances by 8 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSQ entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 8).
(defthm movsq-rsi
  (equal (rsi (movsq x86))
         (bvplus 64 (rsi x86) 8)))

;; RDI advances by 8 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSQ entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 8).
(defthm movsq-rdi
  (equal (rdi (movsq x86))
         (bvplus 64 (rdi x86) 8)))

;; Registers other than RSI and RDI are unchanged.
(defthm movsq-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg)))
           (equal (rgfi reg (movsq x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm movsq-df
  (equal (get-flag :df (movsq x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: MOVS/MOVSQ itself affects no flags
;; (Intel SDM Vol 2A MOVS/MOVSQ entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm movsq-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (movsq x86))
                  (get-flag flag x86)))
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
