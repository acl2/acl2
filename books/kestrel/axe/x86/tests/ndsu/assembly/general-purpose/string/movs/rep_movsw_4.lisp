; Proofs about a binary that uses REP MOVSW with RCX=4 to copy 4 words
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Yusuf Moshood (yusuf.moshood@ndus.edu)
;         Sudarshan Srinivasan (sudarshan.srinivasan@ndsu.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Lifts the functionality of rep_movsw_4.elf64 into logic using the
;; Axe-based x86 lifter and proves various properties.

;; (depends-on "rep_movsw_4.elf64")
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

;; Bridge lemma (purely about the model's flag/alignment machinery, not an
;; SDM-derived fact): CLD's write of DF via !rflagsbits->df does not change
;; the AC bit, so it does not affect whether alignment checking is enabled.
;; This lets the unroller see through the CLD write when discharging the
;; canonicity checks for the word reads/writes.
(local (defthm alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
  (equal (alignment-checking-enabled-p (!rflags (x86isa::!rflagsbits->df df (xr :rflags nil x86)) x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->df-is-rflagsbits
                                     alignment-checking-enabled-p-of-!rflags
                                     x86isa::rflagsbits->ac-of-rflagsbits)))))

;; Bridge lemmas (purely about the model's bit-vector representation, not an
;; SDM-derived fact): once RSI/RDI is bounded (per the extra-assumptions
;; above), a 64-bit "add a small constant" matches the 48-bit "add a small
;; constant" form that appears inside the lifted function body (addresses
;; are represented there as 48-bit values).
(local (defthm bvplus-64-becomes-bvplus-48-of-2
  (implies (unsigned-byte-p 47 x)
           (equal (bvplus 64 x 2) (bvplus 48 2 x)))
  :hints (("Goal" :in-theory (enable bvplus)))))

(local (defthm bvplus-64-becomes-bvplus-48-of-4
  (implies (unsigned-byte-p 47 x)
           (equal (bvplus 64 x 4) (bvplus 48 4 x)))
  :hints (("Goal" :in-theory (enable bvplus)))))

(local (defthm bvplus-64-becomes-bvplus-48-of-6
  (implies (unsigned-byte-p 47 x)
           (equal (bvplus 64 x 6) (bvplus 48 6 x)))
  :hints (("Goal" :in-theory (enable bvplus)))))

;; Lifts the subroutine into logic: Creates the function rep_movsw_4, which
;; represents the effect of the program on the x86 state.
;; CLD; MOV RCX, 4; REP MOVSW is encoded as FC B9 04 00 00 00 F3 66 A5
;; (9 bytes), so stop PC = 0x401009.
;; The entire 8-byte source and destination regions must be canonical, for
;; the x86 model to perform the memory reads/writes on every iteration of
;; the loop without an error branch. A region assumption (rather than just
;; the two endpoints) is needed so the unroller can derive canonicity of
;; the intermediate addresses (e.g. RSI+2, RSI+4) visited by later
;; iterations of the REP loop.
(def-unrolled rep_movsw_4
  :executable "rep_movsw_4.elf64"
  :target #x401000
  :stop-pcs '(#x401009)
  :extra-assumptions '((canonical-regionp 8 (rsi x86))
                       (canonical-regionp 8 (rdi x86))
                       ;; Keep RSI/RDI in the low canonical half (a standard,
                       ;; already-well-supported bound), so that offsets like
                       ;; RSI+2, RSI+4, etc. cannot spuriously collide via
                       ;; 48-bit wraparound.
                       (unsigned-byte-p 47 (rsi x86))
                       (unsigned-byte-p 47 (rdi x86))
                       ;; The source/destination regions must be disjoint from
                       ;; the code, so that the model can see that each
                       ;; iteration's write does not corrupt the instruction
                       ;; bytes needed to fetch/decode the next iteration.
                       (disjoint-regions48p 9 4198400 8 (rsi x86))
                       (disjoint-regions48p 9 4198400 8 (rdi x86))
                       ;; The source and destination buffers must not
                       ;; overlap each other (a non-overlapping-copy
                       ;; assumption), so that writing word i does not
                       ;; disturb a word still to be read from the source.
                       (disjoint-regions48p 8 (rsi x86) 8 (rdi x86)))
  ;; Needed so the unroller can resolve the per-iteration forward/backward
  ;; direction test (DF, set to 0 by CLD) to keep unrolling the REP loop;
  ;; so it can see that reading the source word does not change the state
  ;; (needed to check the destination address for canonicity); and so it
  ;; can see that each iteration's write (disjoint from the code, per the
  ;; assumptions above) does not disturb the instruction bytes needed to
  ;; fetch/decode the next iteration.
  :extra-rules '(rflagsbits->df$inline-of-bvchop-32-of-!rflagsbits->df$inline
                alignment-checking-enabled-p-of-!rflags-of-!rflagsbits->df
                mv-nth-2-of-rme-size$inline
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

;; Intel SDM: 4 words (each 2 bytes) copied from [RSI] to [RDI], in order.
;; Note: RSI/RDI offsets below are stated as (bvplus 48 k (rsi/rdi x86))
;; rather than (bvplus 64 (rsi/rdi x86) k); given the unsigned-byte-p 47
;; bound on RSI/RDI, both forms denote the same address, but the 48-bit
;; constant-first form is what the model's memory-region reasoning (shared
;; with the disjointness assumptions above, which are themselves 48-bit)
;; works with directly.
(defthm rep_movsw_4-word-0
  (implies (and (canonical-regionp 8 (rsi x86))
                (canonical-regionp 8 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 8 (rsi x86))
                (disjoint-regions48p 9 4198400 8 (rdi x86))
                (disjoint-regions48p 8 (rsi x86) 8 (rdi x86)))
           (equal (read 2 (rdi x86) (rep_movsw_4 x86))
                  (read 2 (rsi x86) x86))))

(defthm rep_movsw_4-word-1
  (implies (and (canonical-regionp 8 (rsi x86))
                (canonical-regionp 8 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 8 (rsi x86))
                (disjoint-regions48p 9 4198400 8 (rdi x86))
                (disjoint-regions48p 8 (rsi x86) 8 (rdi x86)))
           (equal (read 2 (bvplus 64 (rdi x86) 2) (rep_movsw_4 x86))
                  (read 2 (bvplus 64 (rsi x86) 2) x86)))
  :hints (("Goal" :in-theory (enable bvminus read-of-write-irrel-gen))))

;; Bridge lemma (purely about read/write reasoning, not an SDM-derived
;; fact): reading the middle 2-byte word (offset 4) out of a chain of 3
;; writes at offsets 6, 4, 2 gives back the value written at offset 4. This
;; is proved as a standalone fact (rather than inline, as part of the
;; rep_movsw_4-word-2 proof below) because enabling bvplus while
;; simultaneously unfolding the rep_movsw_4 definition causes the rewriter
;; to loop; proving it separately, then citing it as a targeted rewrite
;; rule, avoids that.
(local (defthm read-of-write-chain-at-offset-4
  (implies (unsigned-byte-p 47 rdi)
           (equal (read 2 (bvplus 48 4 rdi)
                        (write 2 (bvplus 48 6 rdi) v3
                               (write 2 (bvplus 48 4 rdi) v2
                                      (write 2 (bvplus 48 2 rdi) v1
                                             x86))))
                  (bvchop 16 v2)))
  :hints (("Goal" :in-theory (enable bvminus bvplus read-of-write-irrel-gen)))))

;; Simple identity: reading 2 bytes always returns an already-16-bit value.
(local (defthm bvchop-16-of-read-2
  (equal (bvchop 16 (read 2 addr x86))
         (read 2 addr x86))
  :hints (("Goal" :in-theory (enable read)))))

(defthm rep_movsw_4-word-2
  (implies (and (canonical-regionp 8 (rsi x86))
                (canonical-regionp 8 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 8 (rsi x86))
                (disjoint-regions48p 9 4198400 8 (rdi x86))
                (disjoint-regions48p 8 (rsi x86) 8 (rdi x86)))
           (equal (read 2 (bvplus 48 4 (rdi x86)) (rep_movsw_4 x86))
                  (read 2 (bvplus 48 4 (rsi x86)) x86)))
  :hints (("Goal" :expand ((rep_movsw_4 x86))
           :in-theory (e/d (read-of-write-chain-at-offset-4 bvminus bvplus read-of-write-irrel-gen)
                           (read-2-blast)))))

(defthm rep_movsw_4-word-3
  (implies (and (canonical-regionp 8 (rsi x86))
                (canonical-regionp 8 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 8 (rsi x86))
                (disjoint-regions48p 9 4198400 8 (rdi x86))
                (disjoint-regions48p 8 (rsi x86) 8 (rdi x86)))
           (equal (read 2 (bvplus 48 6 (rdi x86)) (rep_movsw_4 x86))
                  (read 2 (bvplus 48 6 (rsi x86)) x86)))
  :hints (("Goal" :expand ((rep_movsw_4 x86))
           :in-theory (e/d (bvminus bvplus read-of-write-irrel-gen)
                           (read-2-blast)))))

;; All other memory bytes are unchanged (only the 8 bytes starting at [RDI]
;; are written).  Condition: address is not within any of the 4 written
;; 2-byte words.
(defthm rep_movsw_4-other-memory
  (implies (and (canonical-regionp 8 (rsi x86))
                (canonical-regionp 8 (rdi x86))
                (unsigned-byte-p 47 (rsi x86))
                (unsigned-byte-p 47 (rdi x86))
                (disjoint-regions48p 9 4198400 8 (rsi x86))
                (disjoint-regions48p 9 4198400 8 (rdi x86))
                (disjoint-regions48p 8 (rsi x86) 8 (rdi x86))
                (not (bvlt 48 (bvminus 48 address (rdi x86)) 2))
                (not (bvlt 48 (bvminus 48 address (bvplus 48 2 (rdi x86))) 2))
                (not (bvlt 48 (bvminus 48 address (bvplus 48 4 (rdi x86))) 2))
                (not (bvlt 48 (bvminus 48 address (bvplus 48 6 (rdi x86))) 2)))
           (equal (read 1 address (rep_movsw_4 x86))
                  (read 1 address x86)))
  :hints (("Goal" :expand ((rep_movsw_4 x86))
           :in-theory (e/d (bvlt bvminus bvplus read-of-write-irrel-gen)
                           (read-2-blast)))))

;; The RIP is advanced by 9 (CLD; MOV RCX, 4; REP MOVSW is 9 bytes:
;; FC B9 04 00 00 00 F3 66 A5)
(defthm rep_movsw_4-rip
  (equal (rip (rep_movsw_4 x86))
         (+ 9 #x401000)))

;; Intel SDM: RSI advances by RCX*size = 4*2 = 8
(defthm rep_movsw_4-rsi
  (equal (rsi (rep_movsw_4 x86))
         (bvplus 64 (rsi x86) 8)))

;; Intel SDM: RDI advances by RCX*size = 4*2 = 8
(defthm rep_movsw_4-rdi
  (equal (rdi (rep_movsw_4 x86))
         (bvplus 64 (rdi x86) 8)))

;; Intel SDM: RCX = 0 after REP completes
(defthm rep_movsw_4-rcx
  (equal (rcx (rep_movsw_4 x86)) 0))

;; Registers other than RSI, RDI, and RCX are unchanged.
(defthm rep_movsw_4-other-registers
  (implies (and (not (equal *rsi* reg))
                (not (equal *rdi* reg))
                (not (equal *rcx* reg)))
           (equal (rgfi reg (rep_movsw_4 x86))
                  (rgfi reg x86)))
  :hints (("Goal" :in-theory (enable set-rsi set-rdi set-rcx))))

;; CLD clears DF (Intel SDM Vol 2A CLD entry: DF <- 0).
(defthm rep_movsw_4-df
  (equal (get-flag :df (rep_movsw_4 x86))
         0)
  :hints (("Goal" :in-theory (enable get-flag))))

;; No flags other than DF are affected: REP MOVS affects no flags itself
;; (Intel SDM REP/REPE/REPZ/REPNE/REPNZ entry: "Flags Affected: None;
;; however, the CMPS and SCAS instructions do set the status flags"), and
;; CLD affects only DF (Intel SDM Vol 2A CLD entry).
(defthm rep_movsw_4-other-flags
  (implies (not (equal flag :df))
           (equal (get-flag flag (rep_movsw_4 x86))
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
