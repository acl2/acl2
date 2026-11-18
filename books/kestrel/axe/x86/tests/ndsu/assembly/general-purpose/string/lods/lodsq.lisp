; Proofs about a 1-instruction binary that loads a qword from [RSI] into RAX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of lodsq.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "lodsq.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the qword read.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function lodsq, which
;; represents the effect of the program on the x86 state.
;; CLD; LODSQ is encoded as FC 48 AD (3 bytes), so stop PC = 0x401003.
;; Both the base address and +7 must be canonical, for the source qword, for
;; the x86 model to perform the memory read without an error branch.
(def-unrolled lodsq
  :executable "lodsq.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 7 (rsi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the qword read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; RAX is loaded from the qword at [RSI] (Intel SDM LODS/LODSQ entry: RAX <-
;; SRC).
(defthm lodsq-rax
  (equal (rax (lodsq x86))
         (read 8 (rsi x86) x86)))

;; RSI advances by 8 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A LODS/LODSQ entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 8).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at
;; the LODSQ; the DF=1 (decrement) case of the SDM operation is not
;; reachable here (it would require a separate STD-based configuration).
(defthm lodsq-rsi
  (equal (rsi (lodsq x86))
         (bvplus 64 (rsi x86) 8)))

;; RDI is unchanged: LODS/LODSQ does not use RDI (Intel SDM LODS/LODSQ
;; entry).
(defthm lodsq-rdi-unchanged
  (equal (rdi (lodsq x86))
         (rdi x86)))

;; No flags are affected (Intel SDM LODS/LODSQ entry: Flags Affected: None),
;; and CLD affects only DF, which is not read here.
(defthm lodsq-cf-unchanged
  (equal (get-flag :cf (lodsq x86))
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

(defthm lodsq-zf-unchanged
  (equal (get-flag :zf (lodsq x86))
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

(defthm lodsq-sf-unchanged
  (equal (get-flag :sf (lodsq x86))
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

(defthm lodsq-of-unchanged
  (equal (get-flag :of (lodsq x86))
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

(defthm lodsq-af-unchanged
  (equal (get-flag :af (lodsq x86))
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

(defthm lodsq-pf-unchanged
  (equal (get-flag :pf (lodsq x86))
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
(defthm lodsq-df
  (equal (get-flag :df (lodsq x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; Memory is unchanged: LODS/LODSQ only reads memory, it does not write
;; (Intel SDM LODS/LODSQ entry: RAX <- SRC).
(defthm lodsq-memory-unchanged
  (equal (read 1 address (lodsq x86))
         (read 1 address x86)))

;; Registers other than RAX and RSI are unchanged.
(defthm lodsq-other-registers
  (implies (and (not (equal *rax* reg))
                (not (equal *rsi* reg)))
           (equal (rgfi reg (lodsq x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax set-rsi))))

;; The RIP is advanced by 3 (CLD; LODSQ is 3 bytes: FC 48 AD)
(defthm lodsq-rip
  (equal (rip (lodsq x86))
         (+ 3 #x401000)))
