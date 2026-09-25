; Proofs about a 1-instruction binary that stores AL into [RDI]
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of stosb.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "stosb.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Lifts the subroutine into logic: Creates the function stosb, which
;; represents the effect of the program on the x86 state.
;; CLD; STOSB is encoded as FC AA (2 bytes), so stop PC = 0x401002.
;; The base address of the destination byte must be canonical for the x86
;; model to perform the memory write without an error branch.
(def-unrolled stosb
  :executable "stosb.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rdi x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The byte at memory address [RDI] is updated to AL (Intel SDM Vol 2A
;; STOS/STOSB entry: DEST <- AL).
(defthm stosb-memory-destination
  (equal (read 1 (rdi x86) (stosb x86))
         (bvchop 8 (rax x86))))

;; All other memory bytes are unchanged (only the byte at [RDI] is written).
(defthm stosb-other-memory-unchanged
  (implies (not (bvlt 48 (bvminus 48 address (rdi x86)) 1))
           (equal (read 1 address (stosb x86))
                  (read 1 address x86))))

;; The RIP is advanced by 2 (CLD; STOSB is 2 bytes: FC AA)
(defthm stosb-rip
  (equal (rip (stosb x86))
         (+ 2 #x401000)))

;; RDI advances by 1 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A STOS/STOSB entry: IF DF = 0 THEN (R|E)DI <- (R|E)DI + 1).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at the
;; STOSB; the DF=1 (decrement) case of the SDM operation is not reachable
;; here (it would require a separate STD-based configuration).
(defthm stosb-rdi
  (equal (rdi (stosb x86))
         (bvplus 64 (rdi x86) 1)))

;; RSI is unchanged: STOS/STOSB does not use RSI (Intel SDM STOS/STOSB
;; entry).
(defthm stosb-rsi-unchanged
  (equal (rsi (stosb x86))
         (rsi x86)))

;; RAX is unchanged: STOS/STOSB reads AL as its source, it does not write RAX
;; (Intel SDM STOS/STOSB entry: DEST <- AL).
(defthm stosb-rax-unchanged
  (equal (rax (stosb x86))
         (rax x86)))

;; Registers other than RDI are unchanged.
(defthm stosb-other-registers
  (implies (not (equal *rdi* reg))
           (equal (rgfi reg (stosb x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm stosb-df
  (equal (get-flag :df (stosb x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: STOS/STOSB itself affects no flags
;; (Intel SDM Vol 2A STOS/STOSB entry: Flags Affected: None), and CLD affects
;; only DF (Intel SDM Vol 2A CLD entry).
(defthm stosb-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (stosb x86))
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
