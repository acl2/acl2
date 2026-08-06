; Proofs about a 1-instruction binary that moves a word from [RSI] to [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of movsw.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "movsw.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the word read/write.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function movsw, which
;; represents the effect of the program on the x86 state.
;; CLD; MOVSW is encoded as FC 66 A5 (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical, for the source and
;; destination words, for the x86 model to perform the memory read/write
;; without an error branch.
(def-unrolled movsw
  :executable "movsw.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rsi x86)))
                       (unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rdi x86))))
  ;; Needed so the model can see that reading the source word from memory
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

;; The word at memory address [RDI] is updated to the original word at [RSI]
;; (Intel SDM Vol 2A MOVS/MOVSW entry: DEST <- SRC, size = word).
(defthm movsw-memory-at-rdi
  (equal (read 2 (rdi x86) (movsw x86))
         (read 2 (rsi x86) x86)))

;; All other memory bytes are unchanged (only the word at [RDI] is written).
;; Condition: address is not within the 2-byte region starting at [RDI].
(defthm movsw-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 2))
           (equal (read 1 address (movsw x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (CLD; MOVSW is 3 bytes: FC 66 A5)
(defthm movsw-rip
  (equal (rip (movsw x86))
         (+ 3 #x401000)))

;; RSI advances by 2 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSW entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 2).
(defthm movsw-rsi
  (equal (rsi (movsw x86))
         (bvplus 64 (rsi x86) 2)))

;; RDI advances by 2 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSW entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 2).
(defthm movsw-rdi
  (equal (rdi (movsw x86))
         (bvplus 64 (rdi x86) 2)))

;; Registers other than RSI and RDI are unchanged.
(defthm movsw-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg)))
           (equal (rgfi reg (movsw x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm movsw-df
  (equal (get-flag :df (movsw x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: MOVS/MOVSW itself affects no flags
;; (Intel SDM Vol 2A MOVS/MOVSW entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm movsw-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (movsw x86))
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
