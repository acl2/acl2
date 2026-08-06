; Proofs about a binary that uses REP MOVSB with RCX=4 to copy 4 bytes
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of rep_movsb_4.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "rep_movsb_4.elf64")
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

;; Bridge lemma (purely about the model's flag machinery, not an SDM-derived
;; fact): after CLD writes DF via !rflagsbits->df, reading DF back (even
;; through the redundant bvchop the loop-condition code introduces) yields
;; the value just written. This lets the unroller resolve the per-iteration
;; direction test (DF=0 means forward) so the REP loop can be unrolled.
(local (defthm rflagsbits->df$inline-of-bvchop-32-of-!rflagsbits->df$inline
  (equal (x86isa::rflagsbits->df$inline (acl2::bvchop 32 (x86isa::!rflagsbits->df$inline df rflags)))
         (acl2::bfix df))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->df$inline x86isa::!rflagsbits->df$inline)))))

;; Lifts the subroutine into logic: Creates the function rep_movsb_4, which
;; represents the effect of the program on the x86 state.
;; CLD; MOV RCX, 4; REP MOVSB is encoded as FC B9 04 00 00 00 F3 A4
;; (8 bytes), so stop PC = 0x401008.
;; The entire 4-byte source and destination regions must be canonical, for
;; the x86 model to perform the memory reads/writes on every iteration of
;; the loop without an error branch. A region assumption (rather than just
;; the two endpoints) is needed so the unroller can derive canonicity of
;; the intermediate addresses (e.g. RSI+1, RSI+2) visited by later
;; iterations of the REP loop.
(def-unrolled rep_movsb_4
  :executable "rep_movsb_4.elf64"
  :target #x401000
  :stop-pcs '(#x401008)
  :extra-assumptions '((canonical-regionp 4 (rsi x86))
                       (canonical-regionp 4 (rdi x86))
                       ;; Keep RSI/RDI in the low canonical half (a standard,
                       ;; already-well-supported bound), so that offsets like
                       ;; RSI+1, RSI+2, etc. cannot spuriously collide via
                       ;; 48-bit wraparound.
                       (unsigned-byte-p 47 (rsi x86))
                       (unsigned-byte-p 47 (rdi x86))
                       ;; The source/destination regions must be disjoint from
                       ;; the code, so that the model can see that each
                       ;; iteration's write does not corrupt the instruction
                       ;; bytes needed to fetch/decode the next iteration.
                       (disjoint-regions48p 9 4198400 4 (rsi x86))
                       (disjoint-regions48p 9 4198400 4 (rdi x86))
                       ;; The source and destination buffers must not
                       ;; overlap each other (a non-overlapping-copy
                       ;; assumption), so that writing byte i does not
                       ;; disturb a byte still to be read from the source.
                       (disjoint-regions48p 4 (rsi x86) 4 (rdi x86)))
  ;; Needed so the unroller can resolve the per-iteration forward/backward
  ;; direction test (DF, set to 0 by CLD) to keep unrolling the REP loop,
  ;; and so it can see that each iteration's write (disjoint from the code,
  ;; per the assumptions above) does not disturb the instruction bytes
  ;; needed to fetch/decode the next iteration.
  :extra-rules '(rflagsbits->df$inline-of-bvchop-32-of-!rflagsbits->df$inline
                read-bytes-of-write-when-disjoint-regions48p
                read-bytes-of-write-when-disjoint-regions48p-alt))

;; Now we prove various properties of the lifted instruction.  WARNING: To
;; formulate these, do not look at the lifted code or the ACL2 x86 model.
;; Instead, look at other sources of information, especially the Intel/AMD
;; manuals.  The goal is to provide a cross check on what the ACL2 model does.

;; The hypotheses below mirror the extra-assumptions given to def-unrolled
;; above (needed for the model to run this REP loop without an error
;; branch); they are repeated here because they are not automatically
;; available as hypotheses of separately-stated theorems about the lifted
;; function.

;; Intel SDM: 4 bytes copied from [RSI] to [RDI]
(defthm rep_movsb_4-byte-0
  (implies (and (canonical-regionp 4 (rsi x86))
                (canonical-regionp 4 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 4 (rsi x86))
                (disjoint-regions48p 9 4198400 4 (rdi x86))
                (disjoint-regions48p 4 (rsi x86) 4 (rdi x86)))
           (equal (read 1 (rdi x86) (rep_movsb_4 x86))
                  (read 1 (rsi x86) x86))))

(defthm rep_movsb_4-byte-1
  (implies (and (canonical-regionp 4 (rsi x86))
                (canonical-regionp 4 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 4 (rsi x86))
                (disjoint-regions48p 9 4198400 4 (rdi x86))
                (disjoint-regions48p 4 (rsi x86) 4 (rdi x86)))
           (equal (read 1 (bvplus 64 (rdi x86) 1) (rep_movsb_4 x86))
                  (read 1 (bvplus 64 (rsi x86) 1) x86)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm rep_movsb_4-byte-2
  (implies (and (canonical-regionp 4 (rsi x86))
                (canonical-regionp 4 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 4 (rsi x86))
                (disjoint-regions48p 9 4198400 4 (rdi x86))
                (disjoint-regions48p 4 (rsi x86) 4 (rdi x86)))
           (equal (read 1 (bvplus 64 (rdi x86) 2) (rep_movsb_4 x86))
                  (read 1 (bvplus 64 (rsi x86) 2) x86)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthm rep_movsb_4-byte-3
  (implies (and (canonical-regionp 4 (rsi x86))
                (canonical-regionp 4 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 4 (rsi x86))
                (disjoint-regions48p 9 4198400 4 (rdi x86))
                (disjoint-regions48p 4 (rsi x86) 4 (rdi x86)))
           (equal (read 1 (bvplus 64 (rdi x86) 3) (rep_movsb_4 x86))
                  (read 1 (bvplus 64 (rsi x86) 3) x86)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; All other memory bytes are unchanged (only the 4 bytes starting at [RDI]
;; are written).  Condition: address is not within that 4-byte region.
(defthm rep_movsb_4-other-memory
  (implies (and (canonical-regionp 4 (rsi x86))
                (canonical-regionp 4 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 4 (rsi x86))
                (disjoint-regions48p 9 4198400 4 (rdi x86))
                (disjoint-regions48p 4 (rsi x86) 4 (rdi x86))
                (not (equal (bvchop 48 address) (bvchop 48 (rdi x86))))
                (not (equal (bvchop 48 address) (bvchop 48 (bvplus 64 (rdi x86) 1))))
                (not (equal (bvchop 48 address) (bvchop 48 (bvplus 64 (rdi x86) 2))))
                (not (equal (bvchop 48 address) (bvchop 48 (bvplus 64 (rdi x86) 3)))))
           (equal (read 1 address (rep_movsb_4 x86))
                  (read 1 address x86)))
  :hints (("Goal" :in-theory (enable bvplus))))

;; The RIP is advanced by 8 (CLD; MOV RCX, 4; REP MOVSB is 8 bytes:
;; FC B9 04 00 00 00 F3 A4)
(defthm rep_movsb_4-rip
  (equal (rip (rep_movsb_4 x86))
         (+ 8 #x401000)))

;; Intel SDM: RSI advances by RCX*size = 4
(defthm rep_movsb_4-rsi
  (equal (rsi (rep_movsb_4 x86))
         (bvplus 64 (rsi x86) 4)))

;; Intel SDM: RDI advances by RCX*size = 4
(defthm rep_movsb_4-rdi
  (equal (rdi (rep_movsb_4 x86))
         (bvplus 64 (rdi x86) 4)))

;; Intel SDM: RCX = 0 after REP completes
(defthm rep_movsb_4-rcx
  (equal (rcx (rep_movsb_4 x86)) 0))

;; Registers other than RSI, RDI, and RCX are unchanged.
(defthm rep_movsb_4-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg))
                (not (equal *rcx* reg)))
           (equal (rgfi reg (rep_movsb_4 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi set-rcx))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm rep_movsb_4-df
  (equal (get-flag :df (rep_movsb_4 x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: REP MOVS affects no flags itself
;; (Intel SDM REP/REPE/REPZ/REPNE/REPNZ entry: "Flags Affected: None;
;; however, the CMPS and SCAS instructions do set the status flags"), and
;; CLD affects only DF (Intel SDM Vol 2A CLD entry).
(defthm rep_movsb_4-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (rep_movsb_4 x86))
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
