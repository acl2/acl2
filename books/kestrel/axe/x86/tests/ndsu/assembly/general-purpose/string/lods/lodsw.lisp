; Proofs about a 1-instruction binary that loads a word from [RSI] into AX
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of lodsw.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "lodsw.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge lemma (purely about the model's readable-register machinery, not an
;; SDM-derived fact): rewrites the AX abbreviation to the low word of RAX, so
;; that proofs about the lifted function reduce to the rax form used below.
(local (defthm ax-rewrite
  (equal (ax x86) (bvchop 16 (rax x86)))
  :hints (("Goal" :in-theory (enable ax rax)))))

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the word read.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Lifts the subroutine into logic: Creates the function lodsw, which
;; represents the effect of the program on the x86 state.
;; CLD; LODSW is encoded as FC 66 AD (3 bytes), so stop PC = 0x401003.
;; Both the base address and +1 must be canonical, for the source word, for
;; the x86 model to perform the memory read without an error branch.
(def-unrolled lodsw
  :executable "lodsw.elf64"
  :target #x401000
  :stop-pcs '(#x401003)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))
                       (unsigned-canonical-address-p (bvplus 64 1 (rsi x86))))
  ;; Needed so the model can see that alignment checking (unaffected by CLD)
  ;; can be resolved without exposing the flag reconstruction to later
  ;; proofs, when discharging the canonicity checks for the word read.
  :extra-rules '(mv-nth-2-of-rme-size$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AX is loaded from the word at [RSI] (Intel SDM LODS/LODSW entry: AX <-
;; SRC).
(defthm lodsw-ax
  (equal (bvchop 16 (rax (lodsw x86)))
         (read 2 (rsi x86) x86)))

;; Loading AX preserves the upper 48 bits of RAX (only the low word is
;; written).
(defthm lodsw-rax-upper-preserved
  (equal (slice 63 16 (rax (lodsw x86)))
         (slice 63 16 (rax x86))))

;; RSI advances by 2 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A LODS/LODSW entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 2).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at
;; the LODSW; the DF=1 (decrement) case of the SDM operation is not
;; reachable here (it would require a separate STD-based configuration).
(defthm lodsw-rsi
  (equal (rsi (lodsw x86))
         (bvplus 64 (rsi x86) 2)))

;; RDI is unchanged: LODS/LODSW does not use RDI (Intel SDM LODS/LODSW
;; entry).
(defthm lodsw-rdi-unchanged
  (equal (rdi (lodsw x86))
         (rdi x86)))

;; No flags are affected (Intel SDM LODS/LODSW entry: Flags Affected: None),
;; and CLD affects only DF, which is not read here.
(defthm lodsw-cf-unchanged
  (equal (get-flag :cf (lodsw x86))
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

(defthm lodsw-zf-unchanged
  (equal (get-flag :zf (lodsw x86))
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

(defthm lodsw-sf-unchanged
  (equal (get-flag :sf (lodsw x86))
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

(defthm lodsw-of-unchanged
  (equal (get-flag :of (lodsw x86))
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

(defthm lodsw-af-unchanged
  (equal (get-flag :af (lodsw x86))
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

(defthm lodsw-pf-unchanged
  (equal (get-flag :pf (lodsw x86))
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
(defthm lodsw-df
  (equal (get-flag :df (lodsw x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; Memory is unchanged: LODS/LODSW only reads memory, it does not write
;; (Intel SDM LODS/LODSW entry: AX <- SRC).
(defthm lodsw-memory-unchanged
  (equal (read 1 address (lodsw x86))
         (read 1 address x86)))

;; Registers other than RAX and RSI are unchanged.
(defthm lodsw-other-registers
  (implies (and (not (equal *rax* reg))
                (not (equal *rsi* reg)))
           (equal (rgfi reg (lodsw x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax set-rsi))))

;; The RIP is advanced by 3 (CLD; LODSW is 3 bytes: FC 66 AD)
(defthm lodsw-rip
  (equal (rip (lodsw x86))
         (+ 3 #x401000)))
