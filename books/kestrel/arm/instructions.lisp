; A formal model of ARM32: the instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

;; Reference: ARM Architecture Reference Manual ARMv7-A and ARMv7-R edition,
;; available from https://developer.arm.com/documentation/ddi0406/latest/

;; TODO: Deal with address wrap-around, alignment issues, and endianness issues.

(include-book "def-inst")
(include-book "state")
(include-book "memory")
(include-book "pseudocode")
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus-def" :dir :system)
(include-book "kestrel/bv/bvnot" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/bvand" :dir :system))
(local (include-book "kestrel/bv/bvminus" :dir :system))

(in-theory (disable mv-nth))

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

(local (in-theory (disable symbol-alistp))) ; prevent induction

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A5.7 Unconditional instructions
;; todo: flesh this out (pass in the inst!)
(defund execute-unconditional-instruction (arm)
  (declare (xargs :stobjs arm))
  (update-error :unsupported-unconditional-instruction arm))

(defun eor32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvxor 32 x y))

(defun or32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvor 32 x y))

;; See A4.2.2 (Use of labels in UAL instruction syntax)
;; todo: add a case for Thumb
(defun pcvalue (inst-address)
  (declare (xargs :guard (addressp inst-address)))
  (+ 8 inst-address) ; todo: wrap?
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :adc-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations:
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 (apsr.c arm)))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
      arm))

(def-inst :adc-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted (apsr.c arm)))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
      arm))

(def-inst :adc-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s 1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted (apsr.c arm)))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :add-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rn #b1111)
                     (== s 0)))
          ;; todo: see ADR
          (update-error *unsupported* arm))
         ;; The special case for ADD (SP plus immediate) does not seem necessary
         ;; ((when (== rn #b1101))
         ;;  ;; Special case: ADD (SP plus immediate): ;; TODO: Why is this split out?
         ;;  (if (and (== rd #b1111) ; todo: multiple cases can match?
         ;;           (== s 1))
         ;;      (update-error *unsupported* arm)
         ;;    (b* ((d (uint 4 rd))
         ;;         (setflags (== s 1)) ; todo: use == more?
         ;;         (imm32 (ARMExpandImm imm12 arm))
         ;;         ;; end EncodingSpecificOperations
         ;;         ((mv result carry overflow)
         ;;          (AddWithCarry 32 (sp arm) imm32 0)))
         ;;      (if (== d 15)
         ;;          (update-error *unsupported* arm)
         ;;        (let* ((arm (set-reg d result arm))
         ;;               (arm (if setflags
         ;;                        (let* ((arm (set-apsr.n (getbit 31 result) arm))
         ;;                               (arm (set-apsr.z (IsZeroBit 32 result) arm))
         ;;                               (arm (set-apsr.c carry arm))
         ;;                               (arm (set-apsr.v overflow arm)))
         ;;                          arm)
         ;;                      arm)))
         ;;          arm)))))
         ((when (and (== rd #b1111) ; todo: multiple cases can match?
                     (== s 1)))
          (update-error *unsupported* arm))
         ;; Normal case:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 0))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
  arm))

(def-inst :add-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm) ; todo
          )
         ;; The special case for ADD (SP plus register) does not seem necessary
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end Encoding-specific operations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0))
         ((when (== d 15))
          (update-error *unsupported* arm) ; todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
      arm))

(def-inst :add-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s 1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         (arm (set-apsr.v overflow arm)))
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun adr-core (inst-address d imm32 add arm)
  (declare (xargs :guard (and (addressp inst-address)
                              (unsigned-byte-p 4 d)
                              (unsigned-byte-p 32 imm32))
                  :stobjs arm))
  (b* ((pc (pcvalue inst-address))
       (result (if add
                   (bvplus 32 (align pc 4) imm32) ; todo: does this wrap?
                 (bvminus 32 (align pc 4) imm32)))
       ((when (== d 15))
        (update-error *unsupported* arm) ;todo
        )
       (arm (set-reg d result arm)))
    arm))

(def-inst :adr-encoding-a1
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (imm32 (ARMExpandImm imm12 arm))
         (add t)
         ;; end EncodingSpecificOperations
         )
      (adr-core inst-address d imm32 add arm)))

(def-inst :adr-encoding-a2
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (imm32 (ARMExpandImm imm12 arm))
         (add nil)
         ;; end EncodingSpecificOperations
         )
      (adr-core inst-address d imm32 add arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :and-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations:
         (result (bvand 32 (reg n arm) imm32))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :and-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) shifted))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :and-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s 1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) shifted))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :asr-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv & shift_n) (decodeImmShift #b10 imm5))
         ;; end EncodingSpecificOperations:
         ((mv result carry) (shift_c 32 (reg m arm) *SRType_ASR* shift_n (apsr.c arm)))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :asr-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg m arm)))) ; todo: use slice instead of bvchop more
         ((mv result carry) (shift_c 32 (reg n arm) *SRType_ASR* shift_n (apsr.c arm)))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :b
    (b* (;; EncodingSpecificOperations:
         (imm32 (signextend (bvcat 24 imm24 2 0) 26 32))
         (pc (pcvalue inst-address)))
      (BranchWritePC (bvplus 32 pc imm32) arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :bic-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations:
         (result (bvand 32 (reg n arm) (bvnot 32 imm32)))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :bic-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) (bvnot 32 shifted)))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :bic-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s 1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) (bvnot 32 shifted)))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :bl-immediate
    (b* (;; EncodingSpecificOperations:
         (imm32 (signextend (bvcat 24 imm24 2 0) 26 32))
         (targetInstrSet *InstrSet_ARM*)
         ;; end EncodingSpecificOperations
         (arm (set-reg *lr* (if (== (CurrentInstrSet) *InstrSet_ARM*)
                                (bvminus 32 (pcvalue inst-address) 4)
                              (bvcat 31 (slice 31 1 (pcvalue inst-address)) 1 1))
                       arm))
         (targetAddress (if (== targetInstrSet *InstrSet_ARM*)
                            (bvplus 32 (align (pcvalue inst-address) 4) imm32)
                          (bvplus 32 (pcvalue inst-address) imm32)))
         (arm (SelectInstrSet targetInstrSet arm)))
      (BranchWritePC targetAddress arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :bx
    (b* (;; EncodingSpecificOperations:
         (m (uint 4 rm)))
      (BXWritePC (reg m arm) arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :cmn-immediate
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations:
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 0))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

(def-inst :cmn-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

(def-inst :cmn-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (shift_t (DecodeRegShift type))
         ((when (or (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :cmp-immediate
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations:
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 imm32) 1))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

(def-inst :cmp-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) 1))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

(def-inst :cmp-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (shift_t (DecodeRegShift type))
         ((when (or (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) 1))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         (arm (set-apsr.v overflow arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :eor-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations:
         (result (eor32 (reg n arm) imm32))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :eor-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations:
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (eor32 (reg n arm) shifted))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :eor-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s 1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (shift_n (uint 8 (slice 7 0 (reg sval arm)))) ; todo: use slice instead of bvchop more
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (eor32 (reg n arm) shifted))
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :orr-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s 1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations:
         (result (or32 (reg n arm) imm32))
         ((when (== d 15))
          (update-error *unsupported* arm) ;todo
          )
         (arm (set-reg d result arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 result) arm))
                         (arm (set-apsr.c carry arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))
