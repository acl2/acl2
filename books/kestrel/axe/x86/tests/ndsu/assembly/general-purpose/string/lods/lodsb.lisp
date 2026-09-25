; Proofs about a 1-instruction binary that loads a byte from [RSI] into AL
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of lodsb.elf64 into logic using the Axe-based x86
;; lifter and proves various properties.

;; (depends-on "lodsb.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "kestrel/x86/register-readers-and-writers-8-16" :dir :system)

;; Bridge lemma (purely about the model's readable-register machinery, not an
;; SDM-derived fact): rewrites the AL abbreviation to the low byte of RAX, so
;; that proofs about the lifted function reduce to the rax form used below.
(local (defthm al-rewrite
  (equal (al x86) (bvchop 8 (rax x86)))
  :hints (("Goal" :in-theory (enable al rax)))))

;; Lifts the subroutine into logic: Creates the function lodsb, which
;; represents the effect of the program on the x86 state.
;; CLD; LODSB is encoded as FC AC (2 bytes), so stop PC = 0x401002.
;; The address of the source byte must be canonical for the x86 model to
;; perform the memory read without an error branch.
(def-unrolled lodsb
  :executable "lodsb.elf64"
  :target #x401000
  :stop-pcs '(#x401002)
  :extra-assumptions '((unsigned-canonical-address-p (rsi x86))))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; AL is loaded from the byte at [RSI] (Intel SDM LODS/LODSB entry: AL <-
;; SRC).
(defthm lodsb-al
  (equal (bvchop 8 (rax (lodsb x86)))
         (read 1 (rsi x86) x86)))

;; Loading AL preserves the upper 56 bits of RAX (only the low byte is
;; written).
(defthm lodsb-rax-upper-preserved
  (equal (slice 63 8 (rax (lodsb x86)))
         (slice 63 8 (rax x86))))

;; RSI advances by 1 (the operand size), since DF=0 after CLD (Intel SDM Vol
;; 2A LODS/LODSB entry: IF DF = 0 THEN (R|E)SI <- (R|E)SI + 1).  This
;; configuration always executes CLD first, so DF is unconditionally 0 at
;; the LODSB; the DF=1 (decrement) case of the SDM operation is not
;; reachable here (it would require a separate STD-based configuration).
(defthm lodsb-rsi
  (equal (rsi (lodsb x86))
         (bvplus 64 (rsi x86) 1)))

;; RDI is unchanged: LODS/LODSB does not use RDI (Intel SDM LODS/LODSB
;; entry).
(defthm lodsb-rdi-unchanged
  (equal (rdi (lodsb x86))
         (rdi x86)))

;; No flags are affected (Intel SDM LODS/LODSB entry: Flags Affected: None),
;; and CLD affects only DF, which is not read here.
(defthm lodsb-cf-unchanged
  (equal (get-flag :cf (lodsb x86))
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

(defthm lodsb-zf-unchanged
  (equal (get-flag :zf (lodsb x86))
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

(defthm lodsb-sf-unchanged
  (equal (get-flag :sf (lodsb x86))
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

(defthm lodsb-of-unchanged
  (equal (get-flag :of (lodsb x86))
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

(defthm lodsb-af-unchanged
  (equal (get-flag :af (lodsb x86))
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

(defthm lodsb-pf-unchanged
  (equal (get-flag :pf (lodsb x86))
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
(defthm lodsb-df
  (equal (get-flag :df (lodsb x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; Memory is unchanged: LODS/LODSB only reads memory, it does not write
;; (Intel SDM LODS/LODSB entry: AL <- SRC).
(defthm lodsb-memory-unchanged
  (equal (read 1 address (lodsb x86))
         (read 1 address x86)))

;; Registers other than RAX and RSI are unchanged.
(defthm lodsb-other-registers
  (implies (and (not (equal *rax* reg))
                (not (equal *rsi* reg)))
           (equal (rgfi reg (lodsb x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rax set-rsi))))

;; The RIP is advanced by 2 (CLD; LODSB is 2 bytes: FC AC)
(defthm lodsb-rip
  (equal (rip (lodsb x86))
         (+ 2 #x401000)))
