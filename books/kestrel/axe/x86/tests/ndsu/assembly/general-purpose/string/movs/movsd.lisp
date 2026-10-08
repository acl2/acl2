; Proofs about a 1-instruction binary that moves a dword from [RSI] to [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of movsd.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "movsd.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the dword read/write.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function movsd, which
;; represents the effect of the program on the x86 state.
;; CLD; MOVSD is encoded as FC A5 (2 bytes), so stop PC = 0x401002.
;; Both the base address and +3 must be canonical, for the source and
;; destination dwords, for the x86 model to perform the memory read/write
;; without an error branch.
(def-unrolled movsd
  :executable "movsd.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rsi x86)))
                       (unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 3 (rdi x86))))
  ;; Needed so the model can see that reading the source dword from memory
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

;; The dword at memory address [RDI] is updated to the original dword at
;; [RSI] (Intel SDM Vol 2A MOVS/MOVSD entry: DEST <- SRC, size = dword).
(defthm movsd-memory-at-rdi
  (equal (read 4 (rdi x86) (movsd x86))
         (read 4 (rsi x86) x86)))

;; All other memory bytes are unchanged (only the dword at [RDI] is
;; written).  Condition: address is not within the 4-byte region starting
;; at [RDI].
(defthm movsd-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 4))
           (equal (read 1 address (movsd x86))
                  (read 1 address x86))))

;; The RIP is advanced by 2 (CLD; MOVSD is 2 bytes: FC A5)
(defthm movsd-rip
  (equal (rip (movsd x86))
         (+ 2 #x401000)))

;; RSI advances by 4 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSD entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 4).
(defthm movsd-rsi
  (equal (rsi (movsd x86))
         (bvplus 64 (rsi x86) 4)))

;; RDI advances by 4 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSD entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 4).
(defthm movsd-rdi
  (equal (rdi (movsd x86))
         (bvplus 64 (rdi x86) 4)))

;; Registers other than RSI and RDI are unchanged.
(defthm movsd-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg)))
           (equal (rgfi reg (movsd x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm movsd-df
  (equal (get-flag :df (movsd x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: MOVS/MOVSD itself affects no flags
;; (Intel SDM Vol 2A MOVS/MOVSD entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm movsd-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (movsd x86))
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
