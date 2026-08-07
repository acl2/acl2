; Proofs about a 1-instruction binary that stores AX into [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of stosw.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "stosw.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the word write.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function stosw, which
;; represents the effect of the program on the x86 state.
;; CLD; STOSW is encoded as FC 66 AB (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical, for the destination word,
;; for the x86 model to perform the memory write without an error branch.
(def-unrolled stosw
  :executable "stosw.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rdi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the word write.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The word at memory address [RDI] is updated to AX (Intel SDM Vol 2A
;; STOS/STOSW entry: DEST <- AX).
(defthm stosw-memory-destination
  (equal (read 2 (rdi x86) (stosw x86))
         (bvchop 16 (rax x86))))

;; All other memory bytes are unchanged (only the word at [RDI] is written).
(defthm stosw-other-memory-unchanged
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 2))
           (equal (read 1 address (stosw x86))
                  (read 1 address x86))))

;; The RIP is advanced by 3 (CLD; STOSW is 3 bytes: FC 66 AB)
(defthm stosw-rip
  (equal (rip (stosw x86))
         (+ 3 #x401000)))

;; RDI advances by 2 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A STOS/STOSW entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 2).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; STOSW; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm stosw-rdi
  (equal (rdi (stosw x86))
         (bvplus 64 (rdi x86) 2)))

;; RSI is unchanged: STOS/STOSW does not use RSI (Intel SDM STOS/STOSW
;; entry).
(defthm stosw-rsi-unchanged
  (equal (rsi (stosw x86))
         (rsi x86)))

;; RAX is unchanged: STOS/STOSW reads AX as its source, it does not write
;; RAX (Intel SDM STOS/STOSW entry: DEST <- AX).
(defthm stosw-rax-unchanged
  (equal (rax (stosw x86))
         (rax x86)))

;; Registers other than RDI are unchanged.
(defthm stosw-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (stosw x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm stosw-df
  (equal (get-flag :df (stosw x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: STOS/STOSW itself affects no flags
;; (Intel SDM Vol 2A STOS/STOSW entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm stosw-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (stosw x86))
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
