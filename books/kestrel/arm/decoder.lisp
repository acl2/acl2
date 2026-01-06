; A decoder for ARM32 instructions
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
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvand-def" :dir :system) ; todo: include just the def
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(local (include-book "kestrel/alists-light/alistp" :dir :system))
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))

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

    (:b  (cond 4) 1 0 1 0 (imm24 24))

    ;; todo: bfc
    ;; todo: bfi

    (:bic-immediate (cond 4) 0 0 _ 1 _ 1 1 1 0 s (rn 4) (rd 4) (imm12 12))
    (:bic-register (cond 4) 0 0 _ 0 _ 1 1 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:bic-register-shifted-register (cond 4) 0 0 _ 0 _ 1 1 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: bkpt

    (:bl-immediate  (cond 4) 1 0 1 1 (imm24 24)) ;; Encoding A1 of BL/BLX (immediate)

    (:blx-immediate  1 1 1 1 1 0 1 h (imm24 24)) ;; Encoding A2 of BL/BLX (immediate)
    (:blx-register  (cond 4) 0 0 0 1 0 0 1 0 _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ 0 0 1 1 (rm 4))

    (:bx (cond 4) 0 0 0 1 0 0 1 0 _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ 0 0 0 1 (rm 4))

    ;; todo: bxj
    ;; todo: cdp/cdp2
    ;; todo: clrex
    ;; todo: clz

    (:cmn-immediate (cond 4) 0 0 _ 1 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:cmn-regsiter  (cond 4) 0 0 _ 0 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:cmn-regsiter-shifted-register  (cond 4) 0 0 _ 0 _ 1 0 1 1 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    (:cmp-immediate  (cond 4) 0 0 _ 1 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:cmp-register  (cond 4) 0 0 _ 0 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:cmp-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 1 0 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: csdb
    ;; todo: dbg
    ;; todo: dmb
    ;; todo: dsb

    (:eor-immediate  (cond 4) 0 0 1 0 0 0 1 s (rn 4) (rd 4) (imm12 12))
    (:eor-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:eor-shifted-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: isb
    ;; todo: ldc/ldc2

    (:ldm/ldmia/ldmfd (cond 4) 1 0 0 0 1 0 w 1 (rn 4) (register_list 16))
    (:ldmda/ldmfa     (cond 4) 1 0 0 0 0 0 w 1 (rn 4) (register_list 16))
    (:ldmdb/ldmea     (cond 4) 1 0 0 1 0 0 w 1 (rn 4) (register_list 16))
    (:ldmib/ldmed     (cond 4) 1 0 0 1 1 0 w 1 (rn 4) (register_list 16))

    (:ldr-immediate  (cond 4) 0 1 0 p u 0 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldr-literal    (cond 4) 0 1 0 p u 0 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldr-register    (cond 4) 0 1 1 p u 0 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrb-immediate  (cond 4) 0 1 0 p u 1 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldrb-literal  (cond 4) 0 1 0 p u 1 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldrb-register  (cond 4) 0 1 1 p u 1 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrbt-encoding-a1  (cond 4) 0 1 0 0 u 1 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrbt-encoding-a2  (cond 4) 0 1 1 0 u 1 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrd-immediate  (cond 4) 0 0 0 p u 1 w 0 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrd-literal    (cond 4) 0 0 0 (1) u 1 (0) 0 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrd-register   (cond 4) 0 0 0 p u 0 w 0 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

    (:ldrex    (cond 4) 0 0 0 1 1 0 0 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
    (:ldrexb   (cond 4) 0 0 0 1 1 1 0 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
    (:ldrexd   (cond 4) 0 0 0 1 1 0 1 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))
    (:ldrexh   (cond 4) 0 0 0 1 1 1 1 1 (rn 4) (rt 4) (1) (1) (1) (1) 1 0 0 1 (1) (1) (1) (1))

    (:ldrh-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:ldrht-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrht-encoding-a2  (cond 4) 0 0 0 _ 0 u 0 _ 1 _ 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 0 1 1 (rm 4))

    (:ldrsb-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

    (:ldrsbt-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsbt-encoding-a2  (cond 4) 0 0 0 _ 0 u 0 1 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 0 1 (rm 4))

    (:ldrsh-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 1 1 (rm 4))

    (:ldrsht-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsht-encoding-a2  (cond 4) 0 0 0 _ 0 u 0 _ 1 _ 1 (rn 4) (rt 4) (0) (0) (0) (0) 1 1 1 1 (rm 4))

    (:ldrt-encoding-a1  (cond 4) 0 1 0 0 u 0 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrt-encoding-a2  (cond 4) 0 1 1 0 u 0 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:lsl-immediate  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 0 0 (rm 4))
    (:lsl-register  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 0 1 (rn 4))

    (:lsr-immediate  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 1 0 (rm 4))
    (:lsr-register  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 1 1 (rn 4))

    (:mcr  (cond 4) 1 1 1 0 (opc1 3) 0 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4))
    (:mcr2 1 1 1 1 _ 1 1 1 0 (opc1 3) 0 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4))

    ;; todo: mcrr/mcrr2

    (:mla (cond 4) 0 0 0 0 0 0 1 s (rd 4) (ra 4) (rm 4) 1 0 0 1 (rn 4))

    (:mls (cond 4) 0 0 0 0 0 1 1 0 (rd 4) (ra 4) (rm 4) 1 0 0 1 (rn 4))

    (:mov-immediate   (cond 4) 0 0 _ 1 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) (imm12 12)) ; encoding a1 is mov
    (:movw-immediate  (cond 4) 0 0 1 1 _ 0 0 0 0 (imm4 4) (rd 4) (imm12 12)) ; encoding a2 is movw
    (:mov-register  (cond 4) 0 0 _ 0 1 1 0 1 s (0) (0) (0) (0) (rd 4) 0 0 0 0 0 0 0 0 (rm 4))

    (:movt  (cond 4) 0 0 1 1 0 1 0 0 (imm4 4) (rd 4) (imm12 12))

    (:mrc (cond 4) 1 1 1 0 (opc1 3) 1 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4)) ; encoding a1 is mrc
    (:mrc2 1 1 1 1 _ 1 1 1 0 (opc1 3) 1 (crn 4) (rt 4) (coproc 4) (opc2 3) 1 (crm 4)) ; encoding a2 is mrc2

    ;; todo: mrrc/mrrc2
    ;; todo: mrs
    ;; todo: msr

    (:mul (cond 4) 0 0 0 0 0 0 0 s (rd 4) (0) (0) (0) (0) (rm 4) 1 0 0 1 (rn 4))

    (:mvn-immediate (cond 4) 0 0 _ 1 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (imm12 12))
    (:mvn-register  (cond 4) 0 0 _ 0 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:mvn-shifted-register  (cond 4) 0 0 _ 0 _ 1 1 1 1 s (0) (0) (0) (0) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:nop  (cond 4) 0 0 1 1 _ 0 0 1 0 _ 0 0 0 0 (1) (1) (1) (1) (0) (0) (0) (0) 0 0 0 0 0 0 0 0)

    (:orr-immediate  (cond 4) 0 0 1 1 1 0 0 s (rn 4) (rd 4) (imm12 12))
    (:orr-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:orr-shifted-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

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
    ;; todo: rbit
    ;; todo: rev
    ;; todo: rev16
    ;; todo: revsh
    ;; todo: ror

    (:rrx (cond 4) 0 0 _ 0 _ 1 1 0 1 s (0) (0) (0) (0) (rd 4) 0 0 0 0 0 _ 1 1 0 (rm 4))

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

    ;; todo: sbfx
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
    ;; todo: smlald
    ;; todo: smlawb/smlawt
    ;; todo: smlsd
    ;; todo: smlsld
    ;; todo: smmla
    ;; todo: smmls
    ;; todo: smmul
    ;; todo: smuad
    ;; todo: smulbb/smulbt/smultb/smultt

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

    ;; todo: stmda
    ;; todo: stmdb
    ;; todo: stmib

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

    ;; todo: strht
    ;; todo: strt

    (:sub-immediate                   (cond 4) 0 0 1 0 0 1 0 s (rn 4) (rd 4) (imm12 12))
    (:sub-register                    (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:sub-register-shifted-register   (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))
    ;; "sub SP minus immediate" and "sub SP minus register" seem to be just special cases of the above

    (:svc (cond 4) 1 1 1 1 (imm24 24))

    ;; todo: swp, swpb
    ;; todo: sxtab
    ;; todo: sxtab16
    ;; todo: sxtah
    ;; todo: sxtb
    ;; todo: sxtb16
    ;; todo: sxth

    (:teq-immediate (cond 4) 0 0 _ 1 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:teq-register (cond 4) 0 0 _ 0 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:teq-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 0 1 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    (:tst-immediate (cond 4) 0 0 _ 1 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (imm12 12))
    (:tst-register (cond 4) 0 0 _ 0 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (imm5 5) (type 2) 0 (rm 4))
    (:tst-register-shifted-register (cond 4) 0 0 _ 0 _ 1 0 0 0 _ 1 (rn 4) (0) (0) (0) (0) (rs 4) 0 (type 2) 1 (rm 4))

    ;; todo: uadd16
    ;; todo: uadd8
    ;; todo: uasx
    ;; todo: ubfx
    ;; todo: udf
    ;; todo: udiv
    ;; todo: uhadd16
    ;; todo: uhadd8
    ;; todo: uhasx
    ;; todo: uhsax
    ;; todo: uhsub16
    ;; todo: uhsub8
    ;; todo: umaal

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
    ;; todo: uxtab
    ;; todo: uxtab16
    ;; todo: uxtah
    ;; todo: uxtb
    ;; todo: uxt16
    ;; todo: uxth
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
    ;; todo: verv16, vrev32, vrev64
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
    (:sub-immediate :adr-encoding-a2)
    (:str-immediate :push-encoding-a2)
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
    (:bl-immediate :blx-immediate) ; for the case of cond=1111 in BL
    (:mov-register :lsl-immediate) ; for the shift=0 case in LSL
    (:mcr :mcr2)
    (:mrc :mrc2)
    (:ldm/ldmia/ldmfd :pop-encoding-a1)
    (:ldr-immediate :pop-encoding-a2)
    (:strb-immediate :strbt-encoding-a1) ; check me
    (:strb-register :strbt-encoding-a2) ; check me
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An encoding-pattern is a list of items, each of which is 0 or 1 or of the form (<var> <numbits>).
;; These are already desugared.
(defun encoding-patternp (pat)
  (declare (xargs :guard t))
  (if (not (consp pat))
      (null pat)
    (let ((item (first pat)))
      (and (or (eql 0 item)
               (eql 1 item)
               (and (true-listp item)
                    (= 2 (len item))
                    (let ((var (first item))
                          (bits (second item)))
                      (and (symbolp var)
                           (posp bits)))))
           (encoding-patternp (rest pat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An instruction mnemonic, such as :adc-immediate.
(defun mnemonicp (m)
  (declare (xargs :guard t))
  (keywordp m))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This does the following:
;; - drops underscores (just used as seperators)
;; - replaces VAR with (VAR 1)
;; - replaces (0) with 0 -- for now
;; - replaces (1) with 1 -- for now
(defund desugar-pattern (pat)
  (declare (xargs :guard (true-listp pat)))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (atom item)
          (if (or (eql item 0)
                  (eql item 1))
              (cons item (desugar-pattern (rest pat)))
            ;; We ignore all underscores.  We can use _ to separate fields
            ;; (using | might be nicer, but it delimits symbols in Lisp).
            (if (eq item '_)
                (desugar-pattern (rest pat))
              (if (symbolp item)
                  ;; any other symbol is considered a single-bit item, so we
                  ;; can write s instead of (s 1):
                  (cons `(,item 1) (desugar-pattern (rest pat)))
                (er hard? "Bad item in pattern: ~x0." item))))
        ;; it's a cons:
        (if (not (true-listp item))
            (er hard? "Bad item in pattern: ~x0." item)
          (if (symbolp (first item)) ; (<var> <size>)
              (if (and (= 2 (len item))
                       (posp (second item)) ; item size can't be 0
                       )
                  (cons item (desugar-pattern (rest pat)))
                (er hard? "Bad item in pattern: ~x0." item))
            (if (or (eql 0 (first item))
                    (eql 1 (first item)))
                (if (= 1 (len item))
                    ;; parenthesized (0) or (1) is a "should be" value.  for
                    ;; now, we treat these just like other (mandatory) bits,
                    ;; but we could relax that in the future.
                    (cons (first item) (desugar-pattern (rest pat)))
                  (er hard? "Bad item in pattern: ~x0." item))
              (er hard? "Bad item in pattern: ~x0." item))))))))

(defthm encoding-patternp-of-desugar-pattern
  (implies (true-listp pat)
           (encoding-patternp (desugar-pattern pat)))
  :hints (("Goal" :in-theory (enable desugar-pattern))))

;; todo: better name for this thing (not just a list of patterns)
(defun desugar-patterns (patterns)
  (declare (xargs :guard (true-listp patterns)))
  (if (endp patterns)
      nil
    (let ((entry (first patterns)))
      (if (not (and (consp entry)
                    (mnemonicp (car entry))
                    (true-listp (cdr entry))))
          (er hard? 'desugar-patterns "Bad pattern entry: ~x0." entry)
        (cons (cons (car entry) (desugar-pattern (cdr entry)))
              (desugar-patterns (rest patterns)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The number of bits in a pattern
(defund encoding-pattern-size (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (if (endp pat)
      0
    (+ (let ((item (first pat)))
         (if (consp item)
             ;; must be of the form (<var> <size>):
             (second item)
           ;; must be either 0 or 1:
           1))
       (encoding-pattern-size (rest pat)))))

(defthm natp-of-encoding-pattern-size
  (implies (encoding-patternp pat)
           (natp (encoding-pattern-size pat)))
  :hints (("Goal" :in-theory (enable encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The variables listed in a pattern, representing its non-constant fields.
(defund encoding-pattern-vars (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (consp item)
          ;; must be of the form (<var> <size>):
          (cons (first item)
                (encoding-pattern-vars (rest pat)))
        ;; must be either 0 or 1 (so not a var):
        (encoding-pattern-vars (rest pat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A pattern is good if it has length 32 and has no duplicate vars
(defun is-good-encoding-patternp (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (and (if (= 32 (encoding-pattern-size pat))
           t
         (prog2$ (cw "WARNING: Size of pattern ~x0 is not 32." pat) ; todo: print the mnemonic
                 nil))
       (no-duplicatesp-equal (encoding-pattern-vars pat))))

;; Recognize a pattern that is good.
(defun good-encoding-patternp (pat)
  (declare (xargs :guard t))
  (and (encoding-patternp pat)
       (is-good-encoding-patternp pat)))

;; (is-good-encoding-patternp '((cond 4) 0 0 1 0 1 0 0 (s 1) (rn 4) (rd 4) (imm12 12)))


;; (defun good-encoding-pattern-listp (pats)
;;   (declare (xargs :guard t))
;;   (if (not (consp pats))
;;       (null pats)
;;     (and (good-encoding-patternp (first pats))
;;          (good-encoding-pattern-listp (rest pats)))))

;; An alist from mnemonics to encoding-patterns (alternatively, a list of
;; entries each of whose car is a mnemonic and whose cdr is an
;; encoding-pattern).
(defun encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (if (not (consp alist))
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (mnemonicp (car entry))
           (if (good-encoding-patternp (cdr entry))
               t
             (prog2$ (cw "ERROR: Bad encoding pattern: ~x0.~%" (cdr entry))
                     nil))
           (encoding-pattern-alistp (rest alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a pattern, produce a bitmask that has 1s where the pattern has constant bits (0 or 1).
;; Returns a bv32.
(defund mandatory-bit-mask (pat highbit mask)
  (declare (xargs :guard (and (encoding-patternp pat)
                              ;; including highbit as a param is just an optimization
                              (eql highbit (+ -1 (encoding-pattern-size pat)))
                              (unsigned-byte-p 32 mask))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      mask
    (let ((item (first pat)))
      (if (consp item) ; not a 0 or a 1, so skip:
          (mandatory-bit-mask (rest pat) (- highbit (second item)) mask)
        ;; this bit is mandatory:
        (mandatory-bit-mask (rest pat)
                            (- highbit 1)
                            (bvor 32
                                  (expt 2 highbit)
                                  mask))))))

(defthm unsigned-byte-p-32-of-mandatory-bit-mask
  (implies (and (encoding-patternp pat)
                (< highbit 32)
                (equal highbit (+ -1 (encoding-pattern-size pat)))
                (unsigned-byte-p 32 mask))
           (unsigned-byte-p 32 (mandatory-bit-mask pat highbit mask)))
  :hints (("Goal" :induct t
           :in-theory (enable mandatory-bit-mask encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a pattern, produce a bitmask that contains the mandatory values for
;; the constant bits (and zeros for the non-constant bits).
(defun mandatory-bits (pat highbit mask)
  (declare (xargs :guard (and (encoding-patternp pat)
                              ;; including highbit as a param is just an optimization
                              (equal highbit (+ -1 (encoding-pattern-size pat)))
                              (unsigned-byte-p 32 mask))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      mask
    (let ((item (first pat)))
      (if (consp item) ; not a 0 or a 1, so skip
          (mandatory-bits (rest pat) (- highbit (second item)) mask)
        ;; this bit is mandatory:
        (mandatory-bits (rest pat)
                        (- highbit 1)
                        (if (equal 1 item)
                            (bvor 32
                                  (expt 2 highbit)
                                  mask)
                          ;; already 0:
                          mask))))))

(defthm unsigned-byte-p-32-of-mandatory-bits
  (implies (and (encoding-patternp pat)
                (< highbit 32)
                (equal highbit (+ -1 (encoding-pattern-size pat)))
                (unsigned-byte-p 32 mask))
           (unsigned-byte-p 32 (mandatory-bits pat highbit mask)))
  :hints (("Goal" :induct t
           :in-theory (enable mandatory-bits encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund some-mandatory-bit-differsp (index
                                     pat1-mandatory-bits pat1-mandatory-bit-mask
                                     pat2-mandatory-bits pat2-mandatory-bit-mask)
  (declare (xargs :guard (and (integerp index)
                              (<= -1 index)
                              ;; i want the 32's here for efficiency (todo: add type decls):
                              (unsigned-byte-p 32 pat1-mandatory-bits)
                              (unsigned-byte-p 32 pat1-mandatory-bit-mask)
                              (unsigned-byte-p 32 pat2-mandatory-bits)
                              (unsigned-byte-p 32 pat2-mandatory-bit-mask))
                  :measure (nfix (+ 1 index))
                  ))
  (if (not (natp index))
      nil
    (if (and (= 1 (getbit index pat1-mandatory-bit-mask))
             (= 1 (getbit index pat2-mandatory-bit-mask))
             (not (equal (getbit index pat1-mandatory-bits)
                         (getbit index pat2-mandatory-bits))))
        t
      (some-mandatory-bit-differsp (+ -1 index)
                                   pat1-mandatory-bits pat1-mandatory-bit-mask
                                   pat2-mandatory-bits pat2-mandatory-bit-mask))))

(defund incompatible-patternsp (pat1 mnemonic1 pat2 mnemonic2)
  (declare (xargs :guard (and (encoding-patternp pat1)
                              (keywordp mnemonic1)
                              (encoding-patternp pat2)
                              (keywordp mnemonic2)
                              (equal (encoding-pattern-size pat1) 32)
                              (equal (encoding-pattern-size pat2) 32))))
  (let* ((pat1-mandatory-bit-mask (mandatory-bit-mask pat1 31 0))
         (pat1-mandatory-bits (mandatory-bits pat1 31 0))
         (pat2-mandatory-bit-mask (mandatory-bit-mask pat2 31 0))
         (pat2-mandatory-bits (mandatory-bits pat2 31 0))
         (pats-differp (some-mandatory-bit-differsp 31
                                                    pat1-mandatory-bits pat1-mandatory-bit-mask
                                                    pat2-mandatory-bits pat2-mandatory-bit-mask)))
    (if pats-differp
        t
      (prog2$ (cw "WARNING: Overlap in patterns for ~x0 and ~x1." mnemonic1 mnemonic2)
              nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun keyword-doubletp (d)
  (declare (xargs :guard t))
  (and (keyword-listp d)
       (= 2 (len d))))

(defun keyword-doublet-listp (lst)
  (declare (xargs :guard t))
  (if (not (consp lst))
      (null lst)
    (let ((doublet (first lst)))
      (and (keyword-doubletp doublet)
           (keyword-doublet-listp (rest lst))))))

;; Checks whether some allowed-overlap contains both mnemonic1 and mnemonic2.
(defund overlap-allowedp (mnemonic1 mnemonic2 allowed-overlaps)
  (declare (xargs :guard (and (keywordp mnemonic1)
                              (keywordp mnemonic2)
                              ;; (not (equal mnemonic1 mnemonic2)) ; uncomment?
                              (keyword-doublet-listp allowed-overlaps)
                              )))
  (if (endp allowed-overlaps)
      nil
    (let ((allowed-overlap (first allowed-overlaps)))
      (or (and (member-eq mnemonic1 allowed-overlap)
               (member-eq mnemonic2 allowed-overlap))
          (overlap-allowedp mnemonic1 mnemonic2 (rest allowed-overlaps))))))

(defun pattern-incompatible-with-allp (pat mnemonic alist allowed-overlaps)
  (declare (xargs :guard (and (good-encoding-patternp pat) ; maybe a bit overkill but we need the size to be 32
                              (keywordp mnemonic)
                              (encoding-pattern-alistp alist)
                              (keyword-doublet-listp allowed-overlaps))))
  (if (endp alist)
      t
    (let* ((entry2 (first alist))
           (mnemonic2 (car entry2))
           (pat2 (cdr entry2)))
      (and (if (overlap-allowedp mnemonic mnemonic2 allowed-overlaps)
               t
             (incompatible-patternsp pat mnemonic pat2 mnemonic2))
           (pattern-incompatible-with-allp pat mnemonic (rest alist) allowed-overlaps)))))

(defun all-patterns-incompatiblep (alist allowed-overlaps)
  (declare (xargs :guard (and (encoding-pattern-alistp alist)
                              (keyword-doublet-listp allowed-overlaps))))
  (if (endp alist)
      t
    (let* ((entry (first alist))
           (mnemonic (car entry))
           (pat (cdr entry)))
      (and (pattern-incompatible-with-allp pat mnemonic (rest alist) allowed-overlaps)
           (all-patterns-incompatiblep (rest alist) allowed-overlaps)))))

(defun is-good-encoding-pattern-alistp (alist)
  (declare (xargs :guard (encoding-pattern-alistp alist)))
  (and (no-duplicatesp-equal (strip-cars alist))
       (all-patterns-incompatiblep alist *allowed-encoding-overlaps*)
       ; the patterns must be pairwise disjoint (we compute the masks and check) ; todo: first divide the set as indicated by a tree of splitters (bits or slices).  for a splitter, all (remaining) patterns must have fully concrete values
       ))

(defun good-encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (and (encoding-pattern-alistp alist)
       (is-good-encoding-pattern-alistp alist)))

(defconst *desugared-patterns* (desugar-patterns *patterns*))

;move
(assert-event (good-encoding-pattern-alistp *desugared-patterns*))


(defun make-alist-for-fields (highbit pat)
  (declare (xargs :guard (and (encoding-patternp pat)
                              (equal highbit (+ -1 (encoding-pattern-size pat))))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (not (consp item)) ; it's a 0 or 1, so skip
          (make-alist-for-fields (- highbit 1) (rest pat))
        (let ((name (first item))
              (size (second item)))
          `(acons ',name
                  ,(if (= 1 size) ; todo: use bvchop if we can
                       `(getbit ,highbit inst)
                     `(slice ,highbit ,(+ 1 (- highbit size)) inst))
                  ,(make-alist-for-fields (- highbit size) (rest pat))))))))

;; for now this is linear, but see about for the idea of using a tree of splitters
(defun make-decoding-cases (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (cons (let* ((entry (first alist))
                 (mnemonic (car entry))
                 (pattern (cdr entry))
                 (mandatory-bit-mask (mandatory-bit-mask pattern 31 0)) ; has a 1 everywhere the pattern has a concrete value
                 (mandatory-bits (mandatory-bits pattern 31 0)) ; has all the mandatory bits the same as in the pattern and zeros for the don't cares
                 )
            ;; this is a cond clause:
            `((equal (bvand 32 inst ,mandatory-bit-mask) ,mandatory-bits)
              (mv nil ; no error
                  ,mnemonic
                  ,(make-alist-for-fields 31 pattern)
                  )))
          (make-decoding-cases (rest alist)))))

(defun make-instruction-arg-conjuncts (pattern)
  (declare (xargs :guard (encoding-patternp pattern)))
  (if (endp pattern)
      nil
    (let ((item (first pattern)))
      (if (not (consp item)) ; 0 or 1
          (make-instruction-arg-conjuncts (rest pattern))
        (let ((var (first item))
              (bits (second item)))
          (cons `(unsigned-byte-p ,bits (lookup-eq ',var args))
                (make-instruction-arg-conjuncts (rest pattern))))))))

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

(defun make-good-inst-cases (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           ;; (pattern (cdr entry))
           )
      (cons `(,mnemonic (,(pack-in-package "ARM" mnemonic '-argsp) args))
            (make-good-inst-cases (rest alist))))))

(defun make-good-inst-names (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           ;; (pattern (cdr entry))
           )
      (cons (pack-in-package "ARM" mnemonic '-argsp)
            (make-good-inst-names (rest alist))))))

(defun make-decoder (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (good-encoding-pattern-alistp alist))))
  `(progn
     ,@(make-instruction-arg-predicates alist)

     ;; Recognize a "good" instruction
     ;; todo: it's really the args that we are checking here
     ;; todo:  show decoder always produces a good-inst?
     (defund good-instp (mnemonic args)
       (declare (xargs :guard t))
       (and (mnemonicp mnemonic)
            (symbol-alistp args)
            (case mnemonic
              ,@(make-good-inst-cases alist)
              (otherwise nil))))

     ;; The decoder.  Given an instruction, attempt to decode it into mnemonic and args.
     ;; Returns (mv erp mnemonic args) where ARGS is an alist from field names
     ;; to their values from in the instruction (e.g., rd=14).
     (defund ,name (inst)
       (declare (xargs :guard (unsigned-byte-p 32 inst)))
       (cond
        ,@(make-decoding-cases alist)
        (t (mv :unsupported nil nil))))

     (defthm ,(pack-in-package "ARM" name '-return-type)
       (implies (not (mv-nth 0 (arm32-decode inst)))
                (good-instp (mv-nth 1 (arm32-decode inst))
                            (mv-nth 2 (arm32-decode inst))))
       :hints (("Goal" :in-theory (enable ,name good-instp ,@(make-good-inst-names alist)))))))

;; This makes a decoder called arm32-decode that decodes a USB32 into an
;; instruction (any of the instructions in the *patterns*):
(make-event (make-decoder 'arm32-decode *desugared-patterns*))
