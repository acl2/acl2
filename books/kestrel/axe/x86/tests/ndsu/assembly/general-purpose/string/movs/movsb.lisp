; Proofs about a 1-instruction binary that moves a byte from [RSI] to [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of movsb.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "movsb.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Lifts the subroutine into logic: Creates the function movsb, which
;; represents the effect of the program on the x86 state.
;; CLD; MOVSB is encoded as FC A4 (2 bytes), so stop PC = 0x401002.
;; The base addresses of the source and destination bytes must be canonical
;; for the x86 model to perform the memory read/write without an error
;; branch.
(def-unrolled movsb
  :executable "movsb.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (rdi x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [RDI] is updated to the original byte at [RSI]
;; (Intel SDM Vol 2A MOVS/MOVSB entry: DEST <- SRC).
(defthm movsb-memory-at-rdi
  (equal (read 1 (rdi x86) (movsb x86))
         (read 1 (rsi x86) x86)))

;; All other memory bytes are unchanged (only the byte at [RDI] is written).
;; Condition: address is not within the 1-byte region starting at [RDI].
(defthm movsb-other-memory
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 1))
           (equal (read 1 address (movsb x86))
                  (read 1 address x86))))

;; The RIP is advanced by 2 (CLD; MOVSB is 2 bytes: FC A4)
(defthm movsb-rip
  (equal (rip (movsb x86))
         (+ 2 #x401000)))

;; RSI advances by 1 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSB entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 1).
(defthm movsb-rsi
  (equal (rsi (movsb x86))
         (bvplus 64 (rsi x86) 1)))

;; RDI advances by 1 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A MOVS/MOVSB entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 1).
(defthm movsb-rdi
  (equal (rdi (movsb x86))
         (bvplus 64 (rdi x86) 1)))

;; Registers other than RSI and RDI are unchanged.
(defthm movsb-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg)))
           (equal (rgfi reg (movsb x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm movsb-df
  (equal (get-flag :df (movsb x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: MOVS/MOVSB itself affects no flags
;; (Intel SDM Vol 2A MOVS/MOVSB entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm movsb-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (movsb x86))
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
