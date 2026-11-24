; Encodings of ARM32 instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

;; TODO: Consider using lists instead of alists for the args and
;; auto-generating the boilerplate to extract list elems (also think about how
;; to do this without consing).

;; Section references are to the document "ARM Architecture Reference Manual
;; ARMv7-A and ARMv7-R edition" (see README.md).

(include-book "portcullis")
(include-book "encoding-tools")
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bvor" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These encodings come from "A8.8 Alphabetical list of instructions".
;; Here we include only the ARM encodings (Encoding A1, etc.), not the Thumb encodings (Encoding T1, etc.).
;; We attempt to represent the encoding diagrams succinctly and readably.
;; How to read this encoding notation:
;; 0 and 1 represent those constant bits in the encoding
;; (0) and (1) represent values that "should be" either 0 or 1
;; _ is just a separator (essentially ignored, we use it where two adjacent 0/1 values are in separate boxes)
;; a symbol other than _, such as p, represents a 1-bit field of that name
;; a list of the form (<var> <n>), such as (cond 4), represents the variable <var> in a field of width <n>

;; todo: do I want to use keywords for the field names?
;; TODO: Add more
;; TODO: Add _ in consistently where it separates two 0/1 values in different fields
;; todo: check for mnemonic variants in the assembly representations of each instruction (as for BL/BLX).

;; NOTE: Entries preceded by 3 semicolons are ready to be uncommented once we have semantic functions for them.
(defconst *patterns*
  '((:adc-immediate                  (cond 4) 0 0 _ 1 _ 0 1 0 1 s (rn 4) (rd 4) (imm12 12))
    (:adc-register                   (cond 4) 0 0 _ 0 _ 0 1 0 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:adc-register-shifted-register  (cond 4) 0 0 _ 0 _ 0 1 0 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:add-immediate                  (cond 4) 0 0 _ 1 _ 0 1 0 0 s (rn 4) (rd 4) (imm12 12))
    (:add-register                   (cond 4) 0 0 _ 0 _ 0 1 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:add-register-shifted-register  (cond 4) 0 0 _ 0 _ 0 1 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))
    ;; These seem to be merely special cases of :add-immediate and :add-register
    ;; (:add-sp-plus-immediate          (cond 4) 0 0 _ 1 _ 0 1 0 0 s 1 1 0 1 (rd 4) (imm12 12))
    ;; (:add-sp-plus-register           (cond 4) 0 0 _ 0 _ 0 1 0 0 s 1 1 0 1 (rd 4) (imm5 5) (type 2) 0 (rm 4))

    (:adr-encoding-a1 (cond 4) 0 0 _ 1 _ 0 1 0 0 _ 0 _ 1 1 1 1 (rd 4) (imm12 12))
    (:adr-encoding-a2 (cond 4) 0 0 _ 1 _ 0 0 1 0 _ 0 _ 1 1 1 1 (rd 4) (imm12 12))

    (:and-immediate  (cond 4) 0 0 1 0 0 0 0 s (rn 4) (rd 4) (imm12 12))
    (:and-register   (cond 4) 0 0 0 0 0 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:and-register-shifted-register   (cond 4) 0 0 0 0 0 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:asr-immediate (cond 4) 0 0 _ 0 _ 1 1 0 1 _ s (0) (0) (0) (0) (rd 4) (imm5 5) 1 0 0 (rm 4))
    (:asr-register (cond 4) 0 0 _ 0 _ 1 1 0 1 _ s 0 0 0 0 (rd 4) (rm 4) 0 1 0 1 (rn 4))

    (:b (cond 4) 1 0 1 0 (imm24 24))

    (:bfc (cond 4) 0 1 1 1 1 1 0 (msb 5) (rd 4) (lsb 5) 0 0 1 _ 1 1 1 1)

    (:bfi (cond 4) 0 1 1 1 1 1 0 (msb 5) (rd 4) (lsb 5) 0 0 1 _ (rn 4))

    (:bic-immediate (cond 4) 0 0 _ 1 _ 1 1 1 0 s (rn 4) (rd 4) (imm12 12))
    (:bic-register (cond 4) 0 0 _ 0 _ 1 1 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:bic-register-shifted-register (cond 4) 0 0 _ 0 _ 1 1 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: bkpt ; software breakpoint

    (:bl (cond 4) 1 0 1 1 (imm24 24)) ;; Encoding A1 of BL/BLX (immediate)
    (:blx-immediate  1 1 1 1 _ 1 0 1 h (imm24 24)) ;; Encoding A2 of BL/BLX (immediate)
    (:blx-register (cond 4) 0 0 0 1 0 0 1 0 (1) (1) (1) (1) _ (1) (1) (1) (1) _ (1) (1) (1) (1) 0 0 1 1 (rm 4))

    (:bx (cond 4) 0 0 0 1 0 0 1 0 _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ 0 0 0 1 (rm 4))

    ;; todo: bxj ; involves Jazelle
    ;; todo: cbnz, cbz
    ;; todo: cdp/cdp2 ; involves Coprocessor
    ;; todo: clrex ; involves exclusive monitors

    (:clz (cond 4) 0 0 0 1 0 1 1 0 (1) (1) (1) (1) (rd 4) (1) (1) (1) (1) 0 0 0 1 (rm 4))

    (:cmn-immediate (cond 4) 0 0 _ 1 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:cmn-register  (cond 4) 0 0 _ 0 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:cmn-register-shifted-register  (cond 4) 0 0 _ 0 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    (:cmp-immediate  (cond 4) 0 0 _ 1 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:cmp-register  (cond 4) 0 0 _ 0 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:cmp-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: csdb ; memory barrier
    ;; todo: dbg ; debug hint
    ;; todo: dmb ; memory barrier
    ;; todo: dsb ; memory barrier

    (:eor-immediate  (cond 4) 0 0 1 0 0 0 1 s (rn 4) (rd 4) (imm12 12))
    (:eor-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:eor-register-shifted-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: isb ; pipeline flush
    ;; todo: ldc/ldc2 ; coprocessor

    (:ldm/ldmia/ldmfd (cond 4) 1 0 0 0 1 0 w 1 (rn 4) (register_list 16))
    (:ldmda/ldmfa     (cond 4) 1 0 0 0 0 0 w 1 (rn 4) (register_list 16))
    (:ldmdb/ldmea     (cond 4) 1 0 0 1 0 0 w 1 (rn 4) (register_list 16))
    (:ldmib/ldmed     (cond 4) 1 0 0 1 1 0 w 1 (rn 4) (register_list 16))

    (:ldr-immediate  (cond 4) 0 1 0 p u 0 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldr-literal    (cond 4) 0 1 0 p u 0 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldr-register   (cond 4) 0 1 1 p u 0 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrb-immediate  (cond 4) 0 1 0 p u 1 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldrb-literal    (cond 4) 0 1 0 p u 1 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldrb-register   (cond 4) 0 1 1 p u 1 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrbt-encoding-a1 (cond 4) 0 1 0 0 u 1 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrbt-encoding-a2 (cond 4) 0 1 1 0 u 1 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrd-immediate (cond 4) 0 0 0 p u 1 w 0 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrd-literal   (cond 4) 0 0 0 (1) u 1 (0) 0 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrd-register  (cond 4) 0 0 0 p u 0 w 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

;;;    (:ldrex    (cond 4) 0 0 0 1 1 0 0 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
;;;    (:ldrexb   (cond 4) 0 0 0 1 1 1 0 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
;;;    (:ldrexd   (cond 4) 0 0 0 1 1 0 1 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
;;;    (:ldrexh   (cond 4) 0 0 0 1 1 1 1 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))

    (:ldrh-immediate (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-literal   (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-register  (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:ldrht-encoding-a1 (cond 4) 0 0 0   0 u 1   1   1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrht-encoding-a2 (cond 4) 0 0 0 _ 0 u 0 _ 1 _ 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:ldrsb-immediate (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-literal   (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-register  (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

    (:ldrsbt-encoding-a1 (cond 4) 0 0 0   0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsbt-encoding-a2 (cond 4) 0 0 0 _ 0 u 0 1 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

    (:ldrsh-immediate (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-literal   (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-register  (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 1 1 (rm 4))

    (:ldrsht-encoding-a1 (cond 4) 0 0 0   0 u 1   1   1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsht-encoding-a2 (cond 4) 0 0 0 _ 0 u 0 _ 1 _ 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 1 1 (rm 4))

    (:ldrt-encoding-a1 (cond 4) 0 1 0 0 u 0 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrt-encoding-a2 (cond 4) 0 1 1 0 u 0 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:lsl-immediate (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 0 0 (rm 4))
    (:lsl-register (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 0 1 (rn 4))

    (:lsr-immediate (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 1 0 (rm 4))
    (:lsr-register (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 1 1 (rn 4))

;;;    (:mcr  (cond 4) 1 1 1 0 (opc1 3) 0 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4))
;;;    (:mcr2 1 1 1 1 _ 1 1 1 0 (opc1 3) 0 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4))

    ;; todo: mcrr/mcrr2

    (:mla (cond 4) 0 0 0 0 0 0 1 s (rd 4) (ra 4) (rm 4) 1 0 0 1 (rn 4))

    (:mls (cond 4) 0 0 0 0 0 1 1 0 (rd 4) (ra 4) (rm 4) 1 0 0 1 (rn 4))

    (:mov-immediate   (cond 4) 0 0 _ 1 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) (imm12 12)) ; encoding a1 is mov
    (:movw-immediate  (cond 4) 0 0 1 1 _ 0 0 0 0 (imm4 4) (rd 4) (imm12 12)) ; encoding a2 is movw
    (:mov-register  (cond 4) 0 0 _ 0 1 1 0 1 s (0) (0) (0) (0) (rd 4) 0 0 0 0 0 0 0 0 (rm 4))

    (:movt (cond 4) 0 0 1 1 _ 0 1 0 0 (imm4 4) (rd 4) (imm12 12))

;;;    (:mrc (cond 4) 1 1 1 0 (opc1 3) 1 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4)) ; encoding a1 is mrc ; coprocessors
;;;    (:mrc2 1 1 1 1 _ 1 1 1 0 (opc1 3) 1 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4)) ; encoding a2 is mrc2 ; coprocessors

    ;; todo: mrrc/mrrc2 ; coprocessors

    (:mrs (cond 4) 0 0 0 1 0 _ 0 _ 0 0 (1) (1) (1) (1) (rd 4) (0) (0) 0 (0) 0 0 0 0 (0) (0) (0) (0))

    (:msr-immediate (cond 4) 0 0 1 1 0 _ 0 _ 1 0 (mask 2) 0 0 (1) (1) (1) (1) (imm12 12))
    (:msr-register  (cond 4) 0 0 0 1 0 _ 0 _ 1 0 (mask 2) 0 0 (1) (1) (1) (1) (0) (0) 0 (0) 0 0 0 0 (rn 4))

    (:mul (cond 4) 0 0 0 0 0 0 0 s (rd 4) (0) (0) (0) (0) (rm 4) 1 0 0 1 (rn 4))

    (:mvn-immediate (cond 4) 0 0 _ 1 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (imm12 12))
    (:mvn-register  (cond 4) 0 0 _ 0 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:mvn-register-shifted-register  (cond 4) 0 0 _ 0 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:nop  (cond 4) 0 0 1 1 _ 0 0 1 0 _ 0 0 0 0 (1) (1) (1) (1) (0) (0) (0) (0) 0 0 0 0 0 0 0 0)

    (:orr-immediate  (cond 4) 0 0 1 1 1 0 0 s (rn 4) (rd 4) (imm12 12))
    (:orr-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:orr-register-shifted-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: pkh
    ;; todo: pld, pldw
    ;; todo: pli

    (:pop-encoding-a1 (cond 4) 1 0 0 0 1 0 _ 1 _ 1 _ 1 1 0 1 _ (register_list 16))
    (:pop-encoding-a2 (cond 4) 0 1 0 _ 0 _ 1 _ 0 _ 0 _ 1 _ 1 1 0 1 (rt 4) 0 0 0 0 0 0 0 0 0 1 0 0)

    (:push-encoding-a1  (cond 4) 1 0 0 1 0 0 1 0 1 1 0 1 (register_list 16))
    (:push-encoding-a2  (cond 4) 0 1 0 1 0 0 1 0 1 1 0 1 (rt 4) 0 0 0 0 0 0 0 0 0 1 0 0)

    ;; todo: qadd
    ;; todo: qadd16
    ;; todo: qadd8
    ;; todo: qasx
    ;; todo: qdadd
    ;; todo: qdsub
    ;; todo: qsax
    ;; todo: qsub
    ;; todo: qsub16
    ;; todo: qsub8

    ;;; (:rbit (cond 4) 0 1 1 0 1 1 1 1 (1) (1) (1) (1) (rd 4) (1) (1) (1) (1) 0 0 1 1 (rm 4))

    (:rev (cond 4) 0 1 1 0 1 _ 0 _ 1 1 _ (1) (1) (1) (1) (rd 4) (1) (1) (1) (1) 0 0 1 1 (rm 4))
    (:rev16 (cond 4) 0 1 1 0 1 _ 0 _ 1 1 _ (1) (1) (1) (1) (rd 4) (1) (1) (1) (1) 1 0 1 1 (rm 4))
    (:revsh (cond 4) 0 1 1 0 1 _ 1 _ 1 1 _ (1) (1) (1) (1) (rd 4) (1) (1) (1) (1) 1 0 1 1 (rm 4))
    (:ror-immediate (cond 4) 0 0 _ 0 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) (imm5 5) 1 1 0 (rm 4))
    (:ror-register (cond 4) 0 0 _ 0 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) (rm 4) 0 1 1 1 (rn 4))
    (:rrx           (cond 4) 0 0 _ 0 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) 0 0 0 0 0 _ 1 1 0 (rm 4))

    (:rsb-immediate (cond 4) 0 0 _ 1 _ 0 0 1 1 s (rn 4) (rd 4) (imm12 12))
    (:rsb-register (cond 4) 0 0 _ 0 _ 0 0 1 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:rsb-register-shifted-register (cond 4) 0 0 _ 0 _ 0 0 1 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:rsc-immediate (cond 4) 0 0 _ 1 _ 0 1 1 1 s (rn 4) (rd 4) (imm12 12))
    (:rsc-register (cond 4) 0 0 _ 0 _ 0 1 1 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:rsc-register-shifted-register (cond 4) 0 0 _ 0 _ 0 1 1 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: sadd16
    ;; todo: sadd8
    ;; todo: sasx

    (:sbc-immediate (cond 4) 0 0 _ 1 _ 0 1 1 0 s (rn 4) (rd 4) (imm12 12))
    (:sbc-register (cond 4) 0 0 _ 0 _ 0 1 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:sbc-register-shifted-register (cond 4) 0 0 _ 0 _ 0 1 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;;; (:sbfx (cond 4) 0 1 1 1 1 _ 0 _ 1 _ (widthm1 5) (rd 4) (lsb 5) 1 0 1 (rn 4))

    ;; todo: sdiv
    ;; todo: sel
    ;; todo: setend
    ;; todo: sev
    ;; todo: shadd16
    ;; todo: shadd8
    ;; todo: shasx
    ;; todo: shsax
    ;; todo: shsub16
    ;; todo: shsub8
    ;; todo: smlabb/smlabt/smlatb/smlatt
    ;; todo: smlad

    (:smlal (cond 4) 0 0 0 0 1 1 1 s (rdhi 4) (rdlo 4) (rm 4) 1 0 0 1 (rn 4))

    ;; todo: smlalbb/smlalbt/smlaltb/smlaltt

    ;; also covers SMLALDX:
    ;;; (:smlald (cond 4) 0 1 1 1 0 1 0 0 (rdhi 4) (rdlo 4) (rm 4) 0 0 m 1 (rn 4))

    ;; todo: smlawb/smlawt
    ;; todo: smlsd

    ;; also covers SMLSLDX:
    ;;; (:smlsld (cond 4) 0 1 1 1 0 1 0 0 (rdhi 4) (rdlo 4) (rm 4) 0 1 m 1 (rn 4))

    ;; also covers SMMLAR:
    ;;; (:smmla (cond 4) 0 1 1 1 0 1 0 1 (rd 4) (ra 4) (rm 4) 0 0 r 1 (rn 4))

    ;; also covers SMMLSR:
    ;;; (:smmls (cond 4) 0 1 1 1 0 1 0 1 (rd 4) (ra 4) (rm 4) 1 1 r 1 (rn 4))

    ;; also covers SMMULR:
    ;;; (:smmul (cond 4) 0 1 1 1 0 1 0 1 (rd 4) 1 1 1 1 (rm 4) 0 0 r 1 (rn 4))

    ;; todo: smuad

    (:smulbb/smulbt/smultb/smultt (cond 4) 0 0 0 1 0 1 1 0 (rd 4) (0) (0) (0) (0) (rm 4) 1 m n 0 (rn 4))
    (:smull (cond 4) 0 0 0 0 1 1 0 s (rdhi 4) (rdlo 4) (rm 4) 1 0 0 1 (rn 4))

    ;; todo: smulwb/smulwt
    ;; todo: smusd
    ;; todo: ssat
    ;; todo: ssat16
    ;; todo: ssax
    ;; todo: ssub16
    ;; todo: ssub8
    ;; todo: stc/stc2

    (:stm/stmia/stmea (cond 4) 1 0 0 0 1 0 w 0 (rn 4) (register_list 16))
    (:stmda/stmed     (cond 4) 1 0 0 0 0 0 w 0 (rn 4) (register_list 16))
    (:stmdb/stmfd     (cond 4) 1 0 0 1 0 0 w 0 (rn 4) (register_list 16))
    (:stmib/stmfa     (cond 4) 1 0 0 1 1 0 w 0 (rn 4) (register_list 16))

    (:str-immediate   (cond 4) 0 1 0 p u 0 w 0 (rn 4) (rt 4) (imm12 12))
    (:str-register    (cond 4) 0 1 1 p u 0 w 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:strb-immediate  (cond 4) 0 1 0 p u 1 w 0 (rn 4) (rt 4) (imm12 12))
    (:strb-register   (cond 4) 0 1 1 p u 1 w 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:strbt-encoding-a1 (cond 4) 0 1 0 _ 0 u 1 _ 1 _ 0 (rn 4) (rt 4) (imm12 12))
    (:strbt-encoding-a2 (cond 4) 0 1 1 _ 0 u 1 _ 1 _ 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:strd-immediate  (cond 4) 0 0 0 p u 1 w 0 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:strd-register   (cond 4) 0 0 0 p u 0 w 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 1 1 (rm 4))

    ;; todo: strex
    ;; todo: strexb
    ;; todo: strexd
    ;; todo: strexh

    (:strh-immediate  (cond 4) 0 0 0 p u 1 w 0 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:strh-register   (cond 4) 0 0 0 p u 0 w 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:strht-encoding-a1 (cond 4) 0 0 0 _ 0 u 1 _ 1 _ 0 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:strht-encoding-a2 (cond 4) 0 0 0 _ 0 u 0 _ 1 _ 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:strt-encoding-a1 (cond 4) 0 1 _ 0 _ 0 u 0 _ 1 _ 0 (rn 4) (rt 4) (imm12 12))
    (:strt-encoding-a2 (cond 4) 0 1 _ 1 _ 0 u 0 _ 1 _ 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:sub-immediate                   (cond 4) 0 0 1 0 0 1 0 s (rn 4) (rd 4) (imm12 12))
    (:sub-register                    (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:sub-register-shifted-register   (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))
    ;; "sub SP minus immediate" and "sub SP minus register" seem to be just special cases of the above

    (:svc (cond 4) 1 1 1 1 (imm24 24)) ; supervisor call

    (:swp/swpb (cond 4) 0 0 0 1 0 b 0 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 0 1 (rt2 4))

    ;;; (:sxtab (cond 4) 0 1 1 0 1 0 1 0 (rn 4) (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    ;; todo: sxtab16

    ;;; (:sxtah (cond 4) 0 1 1 0 1 0 1 1 (rn 4) (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    (:sxtb (cond 4) 0 1 1 0 1 0 1 0 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))
    (:sxtb16 (cond 4) 0 1 1 0 1 0 0 0 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    (:sxth (cond 4) 0 1 1 0 1 0 1 1 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    (:teq-immediate (cond 4) 0 0 _ 1 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:teq-register (cond 4) 0 0 _ 0 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:teq-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    (:tst-immediate (cond 4) 0 0 _ 1 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:tst-register (cond 4) 0 0 _ 0 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:tst-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: uadd16
    ;; todo: uadd8
    ;; todo: uasx

    ;;; (:ubfx (cond 4) 0 1 1 1 1 _ 1 _ 1 _ (widthm1 5) (rd 4) (lsb 5) 1 0 1 (rn 4))

    ;; todo: udf
    ;; todo: udiv
    ;; todo: uhadd16
    ;; todo: uhadd8
    ;; todo: uhasx
    ;; todo: uhsax
    ;; todo: uhsub16
    ;; todo: uhsub8

    ;;; (:umaal (cond 4) 0 0 0 0 0 1 0 0 (rdhi 4) (rdlo 4) (rm 4) 1 0 0 1 (rn 4))
    (:umlal (cond 4) 0 0 0 0 1 0 1 s (rdhi 4) (rdlo 4) (rm 4) 1 0 0 1 (rn 4))
    (:umull (cond 4) 0 0 0 0 1 0 0 s (rdhi 4) (rdlo 4) (rm 4) 1 0 0 1 (rn 4))

    ;; todo: uqadd16
    ;; todo: uqadd8
    ;; todo: uqasx
    ;; todo: uqsax
    ;; todo: uqsub16
    ;; todo: uqsub8
    ;; todo: usad8
    ;; todo: usada8
    ;; todo: usat
    ;; todo: usat16
    ;; todo: usax
    ;; todo: usub16
    ;; todo: usub8

    ;;; (:uxtab (cond 4) 0 1 1 0 1 1 1 0 (rn 4) (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    ;; todo: uxtab16

    ;;; (:uxtah (cond 4) 0 1 1 0 1 1 1 1 (rn 4) (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    (:uxtb (cond 4) 0 1 1 0 1 1 1 0 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))
    (:uxtb16 (cond 4) 0 1 1 0 1 1 0 0 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    (:uxth (cond 4) 0 1 1 0 1 1 1 1 _ 1 1 1 1 _ (rd 4) (rotate 2) (0) (0) 0 1 1 1 (rm 4))

    ;; todo: vaba/vabal
    ;; todo: vabd/vabdl
    ;; todo: vabd floating point
    ;; todo: vabs
    ;; todo: vacge/vacgt/vacle/vaclt
    ;; todo: vadd
    ;; todo: vadd floating point
    ;; todo: vaddhn
    ;; todo: vaddl/vaddw
    ;; todo: vand
    ;; todo: vbic
    ;; todo: vbif/vbit/vbsl
    ;; todo: vceq
    ;; todo: vcge
    ;; todo: vcgt
    ;; todo: vcle
    ;; todo: vcls
    ;; todo: vclt
    ;; todo: vclz
    ;; todo: vcmp/vcmpe
    ;; todo: vcnt
    ;; todo: vcvt/vcvtr
    ;; todo: vcvtb/vcvtt
    ;; todo: vdiv
    ;; todo: vdup
    ;; todo: veor
    ;; todo: vext
    ;; todo: vfma/vfms
    ;; todo: vnfma/vfnms
    ;; todo: vhadd/vhsub
    ;; todo: vld1
    ;; todo: vld2
    ;; todo: vld3
    ;; todo: vld4
    ;; todo: vldm
    ;; todo: vldr
    ;; todo: vmax/vmin
    ;; todo: vmla/vmlal/vmls/vmlsl
    ;; todo: vmov
    ;; todo: vmovl
    ;; todo: vmovn
    ;; todo: vmrs
    ;; todo: vmsr
    ;; todo: vmul/vmull
    ;; todo: vmvn
    ;; todo: vneg
    ;; todo: vnmla/vnmls/vnmul
    ;; todo: vorn
    ;; todo: vorr
    ;; todo: vpadal
    ;; todo: vpadd
    ;; todo: vpaddl
    ;; todo: vpmax/vpmin
    ;; todo: vpop
    ;; todo: vpush
    ;; todo: vqabs
    ;; todo: vqadd
    ;; todo: vqdmlal/vqdmlsl
    ;; todo: vqdmulh
    ;; todo: vqdmull
    ;; todo: vqmovn/vqmovun
    ;; todo: vqneg
    ;; todo: vqrdmulh
    ;; todo: vqrshl
    ;; todo: vqrshrn
    ;; todo: vqrshrun
    ;; todo: vqshl/vqshlu
    ;; todo: vqshrn/vqshrun
    ;; todo: vqsub
    ;; todo: vraddhn
    ;; todo: vrecpe
    ;; todo: vrecps
    ;; todo: vrev16, vrev32, vrev64
    ;; todo: vrhadd
    ;; todo: vrshl
    ;; todo: vrshr
    ;; todo: vrshrn
    ;; todo: vrsqrte
    ;; todo: vrsqrts
    ;; todo: vrsra
    ;; todo: vrsubhn
    ;; todo: vshl
    ;; todo: vshll
    ;; todo: vshr
    ;; todo: vshrn
    ;; todo: vsli
    ;; todo: vsqrt
    ;; todo: vsra
    ;; todo: vsri
    ;; todo: vst1
    ;; todo: vst2
    ;; todo: vst3
    ;; todo: vst4
    ;; todo: vstm
    ;; todo: vstr
    ;; todo: vsub
    ;; todo: vsubhn
    ;; todo: vsubl/vsubw
    ;; todo: vswp
    ;; todo: vtbl/vtbx
    ;; todo: vtrn
    ;; todo: vtst
    ;; todo: vuzp
    ;; todo: vzip
    ;; todo: wfe
    ;; todo: wfi
    ;; todo: yield
    ))

;; Some bit patterns match multiple patterns.
;; For most of these, the one listed first has a special case that refers to the second.
(defconst *allowed-encoding-overlaps*
  '((:add-immediate :adr-encoding-a1)
    (:bfc :bfi)
    (:sub-immediate :adr-encoding-a2)
    (:str-immediate :push-encoding-a2)
    (:str-immediate :strt-encoding-a1)
    (:str-register :strt-encoding-a2)
    (:strh-immediate :strht-encoding-a1)
    (:strh-register :strht-encoding-a2)
    (:ldr-immediate :ldr-literal)
    (:ldrb-immediate :ldrb-literal)
    (:ldrb-immediate :ldrbt-encoding-a1)
    (:ldrb-literal :ldrbt-encoding-a1)
    (:ldrb-register :ldrbt-encoding-a2)
    (:ldrd-immediate :ldrd-literal)
    (:ldrh-immediate :ldrh-literal)
    (:ldrh-immediate :ldrht-encoding-a1)
    (:ldrh-literal :ldrht-encoding-a1)
    (:ldrh-register :ldrht-encoding-a2)
    (:ldrsb-immediate :ldrsb-literal)
    (:ldrsb-immediate :ldrsbt-encoding-a1)
    (:ldrsb-literal :ldrsbt-encoding-a1)
    (:ldrsb-register :ldrsbt-encoding-a2)
    (:ldrsh-immediate :ldrsh-literal)
    (:ldrsh-immediate :ldrsht-encoding-a1)
    (:ldrsh-literal :ldrsht-encoding-a1)
    (:ldrsh-register :ldrsht-encoding-a2)
    (:ldr-immediate :ldrt-encoding-a1)
    (:ldr-literal :ldrt-encoding-a1)
    (:ldr-register :ldrt-encoding-a2)
    (:b :blx-immediate) ; for the case of cond=1111 in B
    (:bl :blx-immediate) ; for the case of cond=1111 in BL
    (:mov-register :lsl-immediate) ; for the shift=0 case in LSL
    (:mcr :mcr2)
    (:mrc :mrc2)
    (:msr-immediate :nop)
    (:ldm/ldmia/ldmfd :pop-encoding-a1)
    (:ldr-immediate :pop-encoding-a2)
    (:strb-immediate :strbt-encoding-a1) ; check me
    (:strb-register :strbt-encoding-a2) ; check me
    (:push-encoding-a1 :stmdb/stmfd)
    (:ror-immediate :rrx)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: pass in the overlaps
(defun is-good-encoding-pattern-alistp (alist)
  (declare (xargs :guard (encoding-pattern-alistp alist)))
  (and (no-duplicatesp-equal (strip-cars alist))
       (all-patterns-incompatiblep alist *allowed-encoding-overlaps*)
       ; the patterns must be pairwise disjoint (we compute the masks and check) ; todo: first divide the set as indicated by a tree of splitters (bits or slices).  for a splitter, all (remaining) patterns must have fully concrete values
       ))

;; todo: pass in the overlaps
(defun good-encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (and (encoding-pattern-alistp alist)
       (is-good-encoding-pattern-alistp alist)))

(defconst *desugared-patterns* (desugar-patterns *patterns*))

;move
(assert-event (good-encoding-pattern-alistp *desugared-patterns*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-instruction-arg-predicates (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           (pattern (cdr entry)))
      (cons `(defund ,(pack-in-package "ARM" mnemonic '-argsp) (args)
               (declare (xargs :guard (symbol-alistp args)))
               (and ,@(make-instruction-arg-conjuncts pattern)))
            (make-instruction-arg-predicates (rest alist))))))

;; Makes predicates like add-immediate-argsp:
(make-event `(progn ,@(make-instruction-arg-predicates *desugared-patterns*)))
