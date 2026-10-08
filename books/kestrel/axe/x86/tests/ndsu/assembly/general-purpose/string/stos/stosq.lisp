; Proofs about a 1-instruction binary that stores RAX into [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of stosq.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "stosq.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the qword write.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function stosq, which
;; represents the effect of the program on the x86 state.
;; CLD; STOSQ is encoded as FC 48 AB (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical, for the destination
;; qword, for the x86 model to perform the memory write without an error
;; branch.
(def-unrolled stosq
  :executable "stosq.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rdi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the qword write.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The qword at memory address [RDI] is updated to RAX (Intel SDM Vol 2A
;; STOS/STOSQ entry: DEST <- RAX).
(defthm stosq-memory-destination
  (equal (read 8 (rdi x86) (stosq x86))
         (rax x86)))

;; All other memory bytes are unchanged (only the qword at [RDI] is
;; written).
(defthm stosq-other-memory-unchanged
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 8))
           (equal (read 1 address (stosq x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (CLD; STOSQ is 3 bytes: FC 48 AB)
(defthm stosq-rip
  (equal (rip (stosq x86))
         (+ 3 #x401000)))

;; RDI advances by 8 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A STOS/STOSQ entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 8).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at
;; the STOSQ; the DF=1 (decrement) case of the SDM operation is not
;; reachable here (it would require a separate STD-based configuration).
(defthm stosq-rdi
  (equal (rdi (stosq x86))
         (bvplus 64 (rdi x86) 8)))

;; RSI is unchanged: STOS/STOSQ does not use RSI (Intel SDM STOS/STOSQ
;; entry).
(defthm stosq-rsi-unchanged
  (equal (rsi (stosq x86))
         (rsi x86)))

;; RAX is unchanged: STOS/STOSQ reads RAX as its source, it does not write
;; RAX (Intel SDM STOS/STOSQ entry: DEST <- RAX).
(defthm stosq-rax-unchanged
  (equal (rax (stosq x86))
         (rax x86)))

;; Registers other than RDI are unchanged.
(defthm stosq-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (stosq x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm stosq-df
  (equal (get-flag :df (stosq x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: STOS/STOSQ itself affects no flags
;; (Intel SDM Vol 2A STOS/STOSQ entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm stosq-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (stosq x86))
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
