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

;; TODO: Alphabetize (to the extent we can, given the dependencies)

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

(local (in-theory (enable shift))) ; todo

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A5.7 Unconditional instructions
;; todo: flesh this out (pass in the inst!)
(defund execute-unconditional-instruction (arm)
  (declare (xargs :stobjs arm))
  (update-error :unsupported-unconditional-instruction arm))

(defun and32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvand 32 x y))

(defun eor32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvxor 32 x y))

(defun or32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvor 32 x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :adc-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :adc-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :adc-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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

;; We put ADR here (out of alphabetical order) because it is used by ADD (and SUB).

(defun adr-common (inst-address d imm32 add arm)
  (declare (xargs :guard (and (addressp inst-address)
                              (register-numberp d)
                              (unsigned-byte-p 32 imm32)
                              (booleanp add))
                  :stobjs arm))
  (b* ((pc (pcvalue inst-address))
       (result (if add
                   (bvplus 32 (align pc 4) imm32) ; todo: does this wrap?
                 (bvminus 32 (align pc 4) imm32))))
    (if (== d 15)
        (ALUWritePC result arm)
      (let ((arm (set-reg d result arm)))
        arm))))

(defun adr-encoding-a1-core (rd imm12 inst-address arm)
  (declare (xargs :guard (and (register-numberp rd)
                              (unsigned-byte-p 12 imm12)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       (d (uint 4 rd))
       (imm32 (ARMExpandImm imm12 arm))
       (add *true*)
       ;; end EncodingSpecificOperations
       )
    (adr-common inst-address d imm32 add arm)))

(def-inst :adr-encoding-a1
    (adr-encoding-a1-core rd imm12 inst-address arm))

;; Also called by SUB
(defun adr-encoding-a2-core (rd imm12 inst-address arm)
  (declare (xargs :guard (and (register-numberp rd)
                              (unsigned-byte-p 12 imm12)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       (d (uint 4 rd))
       (imm32 (ARMExpandImm imm12 arm))
       (add *false*)
       ;; end EncodingSpecificOperations
       )
    (adr-common inst-address d imm32 add arm)))

(def-inst :adr-encoding-a2
    (adr-encoding-a2-core rd imm12 inst-address arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :add-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rn #b1111)
                     (== s #b0)))
          (adr-encoding-a1-core rd imm12 inst-address arm))
         ;; The special case for ADD (SP plus immediate) does not seem necessary
         ;; ((when (== rn #b1101))
         ;;  ;; Special case: ADD (SP plus immediate): ;; TODO: Why is this split out?
         ;;  (if (and (== rd #b1111) ; todo: multiple cases can match?
         ;;           (== s #b1))
         ;;      (update-error *unsupported* arm)
         ;;    (b* ((d (uint 4 rd))
         ;;         (setflags (== s #b1)) ; todo: use == more?
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
                     (== s #b1)))
          (update-error *unsupported* arm))
         ;; Normal case:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) imm32 0)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :add-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm) ; todo
          )
         ;; The special case for ADD (SP plus register) does not seem necessary
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end Encoding-specific operations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0))
         (arm (if (== d 15)
                  (ALUWritePC result arm)
                (let* ((arm (set-reg d result arm))
                       (arm (if setflags
                                (let* ((arm (set-apsr.n (getbit 31 result) arm))
                                       (arm (set-apsr.z (IsZeroBit 32 result) arm))
                                       (arm (set-apsr.c carry arm))
                                       (arm (set-apsr.v overflow arm)))
                                  arm)
                              arm)))
                  arm))))
      arm))

(def-inst :add-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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

(def-inst :and-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (bvand 32 (reg n arm) imm32)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :and-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) shifted)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :and-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv & shift_n) (decodeImmShift #b10 imm5))
         ;; end EncodingSpecificOperations
         ((mv result carry) (shift_c 32 (reg m arm) *SRType_ASR* shift_n (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))


(def-inst :asr-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg m arm))))
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
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (bvand 32 (reg n arm) (bvnot 32 imm32))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :bic-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvand 32 (reg n arm) (bvnot 32 shifted))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :bic-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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
         ;; end EncodingSpecificOperations
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
         ;; end EncodingSpecificOperations
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
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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
         ;; end EncodingSpecificOperations
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
         ;; end EncodingSpecificOperations
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
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (eor32 (reg n arm) imm32)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :eor-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (eor32 (reg n arm) shifted)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :eor-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
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

;; Returns (mv address arm).
;; also used for ldmib
(defun ldm-loop (i registers address arm)
  (declare (xargs :guard (and (natp i)
                              (<= i 15)
                              (unsigned-byte-p 16 registers)
                              (addressp address))
                  :stobjs arm
                  :measure (nfix (+ 1 (- 14 i)))))
  (if (or (not (mbt (natp i)))
          (< 14 i))
      (mv address arm)
    (b* (((mv address arm)
          (if (== (getbit i registers) 1)
              (let ((arm (set-reg i (MemA address 4 arm) arm)))
                (mv (bvplus 32 4 address) arm))
            (mv address arm))))
      (ldm-loop (+ 1 i) registers address arm))))

(defthm ldm-loop-return-type
  (implies (addressp address)
           (addressp (mv-nth 0 (ldm-loop i registers address arm)))))

;; Also called by POP
(defun ldm-core (w rn register_list arm)
  (declare (xargs :guard (and (bitp w)
                              (register-numberp rn)
                              (unsigned-byte-p 16 register_list))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations (continued):
       (n (uint 4 rn))
       (registers register_list)
       (wback (== w 1))
       ((when (or (== n 15)
                  (< (BitCount 16 registers) 1)))
        (update-error *unpredictable* arm))
       ((when (and wback
                   (== (getbit n registers) 1)
                   (>= (ArchVersion) 7)))
        (update-error *unpredictable* arm))
       (arm (NullCheckIfThumbEE n arm))
       (address (reg n arm))
       ((mv address arm) (ldm-loop 0 registers address arm))
       (arm (if (== (getbit 15 registers) 1)
                (LoadWritePC (MemA address 4 arm) arm)
              arm))
       (arm (if (and wback (== (getbit n registers) 0))
                (set-reg n (bvplus 32 (reg n arm) (* 4 (bitcount 16 registers))) arm)
              arm))
       (arm (if (and wback (== (getbit n registers) 1))
                ;; todo: distinguish unknown vals when this is called by POP?
                (set-reg n (unknown-bits 32 :ldm-core arm) arm)
              arm)))
    arm))

;; Returns (mv address arm).
(defun pop-loop (i registers address UnalignedAllowed arm)
  (declare (xargs :guard (and (natp i)
                              (<= i 15)
                              (unsigned-byte-p 16 registers)
                              (addressp address)
                              (booleanp UnalignedAllowed))
                  :stobjs arm
                  :measure (nfix (+ 1 (- 14 i)))))
  (if (or (not (mbt (natp i)))
          (< 14 i))
      (mv address arm)
    (b* (((mv address arm)
          (if (== (getbit i registers) 1)
              (let* ((arm (set-reg i (if UnalignedAllowed (MemU address 4 arm) (MemA address 4 arm)) arm))
                     (address (bvplus 32 4 address)))
                (mv address arm))
            (mv address arm))))
      (pop-loop (+ 1 i) registers address UnalignedAllowed arm))))

(defthm pop-loop-return-type
  (implies (addressp address)
           (and (addressp (mv-nth 0 (pop-loop i registers address UnalignedAllowed arm)))
                (integerp (mv-nth 0 (pop-loop i registers address UnalignedAllowed arm))))))

(defun pop-common (registers UnalignedAllowed arm)
  (declare (xargs :guard (and (unsigned-byte-p 16 registers)
                              (booleanp UnalignedAllowed))
                  :guard-hints (("Goal" :in-theory (disable addressp)))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE 13 arm))
       (address (reg *sp* arm)) ; todo: any offset to SP like for PC?
       ((mv address arm) (pop-loop 0 registers address UnalignedAllowed arm))
       (arm (if (== (getbit 15 registers) 1)
                (if UnalignedAllowed
                    (if (== (slice 1 0 address) #b00)
                        (LoadWritePC (MemU address 4 arm) arm)
                      (update-error *unpredictable* arm))
                  (LoadWritePC (MemA address 4 arm) arm))
              arm))
       (arm (if (== (getbit 13 registers) 0)
                (set-reg *sp* (bvplus 32 (reg *sp* arm) (* 4 (bitcount 16 registers))) arm)
              arm))
       (arm (if (== (getbit 13 registers) 1)
                (set-reg *sp* (unknown-bits 32 :pop-common arm) arm)
              arm)))
    arm))

;; Also used by LDM
(defun pop-encoding-a1-core (register_list arm)
  (declare (xargs :guard (unsigned-byte-p 16 register_list)
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations (continued):
       (registers register_list)
       (UnalignedAllowed *false*)
       ((when (and (== (getbit 13 registers) 1)
                   (>= (ArchVersion) 7)))
        (update-error *unpredictable* arm)))
    (pop-common registers UnalignedAllowed arm)))

(def-inst :ldm/ldmia/ldmfd
    (if (and (== w 1)
             (== rn #b1101)
             (> (BitCount 16 register_list) 1))
        (pop-encoding-a1-core register_list arm)
      (ldm-core w rn register_list arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :ldmib/ldmed
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (registers register_list)
         (wback (== w 1))
         ((when (or (== n 15)
                    (< (BitCount 16 registers) 1)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (==  (getbit n registers) 1)
                     (>= (ArchVersion) 7)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations ;; todo: check for missing nullchecks everywhere
         (address (bvplus 32 (reg n arm) 4))
         ((mv address arm) (ldm-loop 0 registers address arm))
         (arm (if (== (getbit 15 registers) 1)
                  (LoadWritePC (MemA address 4 arm) arm)
                arm))
         (arm (if (and wback (== (getbit n registers) 0))
                  (set-reg n (bvplus 32 (reg n arm) (* 4 (bitcount 16 registers))) arm)
                arm))
         (arm (if (and wback (== (getbit n registers) 1))
                  (set-reg n (unknown-bits 32 :ldmib/ldmed arm) arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LDRT has been moved here (out of alphabetical order) because other
;; instructions refer to it.

(defun ldrt-common (n tval postindex add register_form imm32 m shift_t shift_n arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32)
                              (SRTypep shift_t)
                              (not (and (eq shift_t *SRType_RRX*)
                                        (not (equal shift_n 1))))
                              (natp shift_n))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (Shift 32 (reg m arm) shift_t shift_n (apsr.c arm)) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (data (MemU_unpriv address 4 arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm))
       (arm (if (or (UnalignedSupport)
                    (== (slice 1 0 address) #b00))
                (set-reg tval data arm)
              (if (== (CurrentInstrSet) *InstrSet_ARM*)
                  (set-reg tval (ROR 32 data (* 8 (uint 2 (slice 1 0 address)))) arm)
                (set-reg tval (unknown-bits 32 :ldrt-common arm) arm)))))
    arm))

;; Also called by ldr-literal and ldr-immediate.
(defun ldrt-encoding-a1-core (u rn rt imm12 arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend imm12 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       ((mv shift_t shift_n) (mv *SRType_LSL* 1)) ; arbitrary (unspecified but unused below)
       (m 0) ; arbitrary (unspecified but unused below)
       ;; end EncodingSpecificOperations
       )
    (ldrt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

;; Also called by ldr-register
(defund ldrt-encoding-a2-core (u rn rt imm5 type rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 5 imm5)
                              (unsigned-byte-p 2 type)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u 1))
       (register_form *true*)
       ((mv shift_t shift_n) (decodeImmShift type imm5))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ((when (and (< (ArchVersion) 6)
                   (== m n)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (ldrt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

(def-inst :ldrt-encoding-a1
    (ldrt-encoding-a1-core u rn rt imm12 arm))

(def-inst :ldrt-encoding-a2
    (ldrt-encoding-a2-core u rn rt imm5 type rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by ldr-immediate
(defun ldr-literal-core (p u w rt imm12 inst-address arm)
  (declare (xargs :guard (and (bitp p)
                              (bitp u)
                              (bitp w)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== p 0)
                   (== w 1)))
        (ldrt-encoding-a1-core u #b1111 ;rn
                               rt imm12 arm))
       ((when (== p w))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (imm32 (ZeroExtend imm12 32))
       (add (== u 1))
       (arm (NullCheckIfThumbEE 15 arm))
       (base (align (pcvalue inst-address) 4))
       (address (if add (bvplus 32 base imm32) (bvminus 32 base imm32)))
       (data (MemU address 4 arm))
       (arm (if (== tval 15)
                (if (== (slice 1 0 address) #b00)
                    (LoadWritePC data arm)
                  (update-error *unpredictable* arm))
              (if (or (UnalignedSupport) (== (slice 1 0 address) #b00))
                  (set-reg tval data arm)
                (if (== (CurrentInstrSet) *InstrSet_ARM*)
                    (set-reg tval (ROR 32 data (* 8 (uint 2 (slice 1 0 address)))) arm)
                  (set-reg tval (unknown-bits 32 :ldrt-literal-core arm) arm))))))
    arm))

;; Also called by ldr-immediate.
(defun pop-encoding-a2-core (rt arm)
  (declare (xargs :guard (register-numberp rt)
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (registers 0) ; call a zeros function?
       (registers (putbit 16 tval 1 registers))
       (UnalignedAllowed *true*)
       ((when (== tval 13)) (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       )
    (pop-common registers UnalignedAllowed arm)))

(def-inst :ldr-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldr-literal-core p u w rt imm12 inst-address arm))
         ((when (and (== p 0)
                     (== w 1)))
          (ldrt-encoding-a1-core u rn rt imm12 arm))
         ((when (and (== rn #b1101)
                     (== p 0)
                     (== u 1)
                     (== w 0)
                     (== imm12 #b000000000100)))
          (pop-encoding-a2-core rt arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend imm12 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and wback
                     (== n tval)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 4 arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm))
         (arm (if (== tval 15)
                  (if (== (slice 1 0 address) #b00)
                      (LoadWritePC data arm)
                    (update-error *unpredictable* arm))
                (if (or (UnalignedSupport) (== (slice 1 0 address) #b00))
                    (set-reg tval data arm)
                  (set-reg tval (ROR 32 data (* 8 (uint 2 (slice 1 0 address)))) arm)))))
      arm))

(def-inst :ldr-literal
    (ldr-literal-core p u w rt imm12 inst-address arm))

(def-inst :ldr-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (ldrt-encoding-a2-core u rn rt imm5 type rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ((when (== m 15))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 4 arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm))
         (arm (if (== tval 15)
                  (if (== (slice 1 0 address) #b00)
                      (LoadWritePC data arm)
                    (update-error *unpredictable* arm))
                (if (or (UnalignedSupport) (== (slice 1 0 address) #b00))
                    (set-reg tval data arm)
                  (set-reg tval (ROR 32 data (* 8 (uint 2 (slice 1 0 address)))) arm)))))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LDRBT has been moved here (out of alphabetical order) because other
;; instructions refer to it.

(defun ldrbt-common (n tval postindex add register_form imm32 m shift_t shift_n arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32)
                              (SRTypep shift_t)
                              (not (and (eq shift_t *SRType_RRX*)
                                        (not (equal shift_n 1))))
                              (natp shift_n))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (Shift 32 (reg m arm) shift_t shift_n (apsr.c arm)) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (arm (set-reg tval (ZeroExtend (MemU_unpriv address 1 arm) 32) arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm)))
    arm))

;; Also called by ldr-literal and ldr-immediate.
(defun ldrbt-encoding-a1-core (u rn rt imm12 arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u 1))
       (register_form *false*)
       (imm32 (ZeroExtend imm12 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       ((mv shift_t shift_n) (mv *SRType_LSL* 1)) ; arbitrary (unspecified but unused below)
       (m 0) ; arbitrary (unspecified but unused below)
       ;; end EncodingSpecificOperations
       )
    (ldrbt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

;; Also called by ldr-register
(defund ldrbt-encoding-a2-core (u rn rt imm5 type rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 5 imm5)
                              (unsigned-byte-p 2 type)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u 1))
       (register_form *true*)
       ((mv shift_t shift_n) (decodeImmShift type imm5))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ((when (and (< (ArchVersion) 6)
                   (== m n)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (ldrbt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

(def-inst :ldrbt-encoding-a1
    (ldrbt-encoding-a1-core u rn rt imm12 arm))

(def-inst :ldrbt-encoding-a2
    (ldrbt-encoding-a2-core u rn rt imm5 type rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by ldrb-immediate
(defun ldrb-literal-core (p u w rt imm12 inst-address arm)
  (declare (xargs :guard (and (bitp p)
                              (bitp u)
                              (bitp w)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== p #b0)
                   (== w #b1)))
        (ldrbt-encoding-a1-core u #b1111 ;rn
                               rt imm12 arm))
       ((when (== p w))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (imm32 (ZeroExtend imm12 32))
       (add (== u 1))
       ((when (== tval 15))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE 15 arm))
       (base (align (pcvalue inst-address) 4))
       (address (if add (bvplus 32 base imm32) (bvminus 32 base imm32)))
       (arm (set-reg tval (ZeroExtend (MemU address 1 arm) 32) arm)))
    arm))

(def-inst :ldrb-literal
    (ldrb-literal-core p u w rt imm12 inst-address arm))

(def-inst :ldrb-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldrb-literal-core p u w rt imm12 inst-address arm))
         ((when (and (== p 0)
                     (== w 1)))
          (ldrbt-encoding-a1-core u rn rt imm12 arm))
         ((when (and (== rn #b1101)
                     (== p 0)
                     (== u 1)
                     (== w 0)
                     (== imm12 #b000000000100)))
          (pop-encoding-a2-core rt arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend imm12 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (or (== tval 15)
                    (and wback
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (set-reg tval (ZeroExtend (MemU address 1 arm) 32) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

(def-inst :ldrb-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (ldrbt-encoding-a2-core u rn rt imm5 type rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (arm (set-reg tval (ZeroExtend (MemU address 1 arm) 32) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; Also called by ldrd-immediate
(defun ldrd-literal-core (u rt imm4H imm4L inst-address arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L)
                              (addressp inst-address))
                  ::guard-hints (("Goal" :in-theory (enable uint)))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (== (getbit 0 rt) #b1))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt))
       (t2 (+ tval 1)) ; tval can't be 15 because it's low bit is not 1
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       (add (== u #b1))
       ((when (== t2 15))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE 15 arm))
       (address (if add
                    (bvplus 32 (Align (pcvalue inst-address) 4) imm32)
                  (bvminus 32 (Align (pcvalue inst-address) 4) imm32)))
       (arm (if (and (HaveLPAE)
                     (== (slice 2 0 address) #b000))
                (let ((data (MemA address 8 arm)))
                  (if (BigEndian)
                      (let* ((arm (set-reg tval (slice 63 32 data) arm))
                             (arm (set-reg t2 (slice 31 0 data) arm)))
                        arm)
                    (let* ((arm (set-reg tval (slice 31 0 data) arm))
                           (arm (set-reg t2 (slice 63 32 data) arm)))
                      arm)))
              (let* ((arm (set-reg tval (MemA address 4 arm) arm))
                     (arm (set-reg t2 (MemA (bvplus 32 address 4) 4 arm) arm)))
                arm))))
    arm))

(def-inst :ldrd-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldrd-literal-core u rt imm4H imm4L inst-address arm))
         ((when (== (getbit 0 rt) #b1))
          (update-error *unpredictable* arm))
         (tval (uint 4 rt))
         (t2 (+ tval 1)) ; tval can't be 15 because it's low bit is not 1
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and (== p #b0)
                     (== w #b1)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n tval)
                         (== n t2))))
          (update-error *unpredictable* arm))
         ((when (== t2 15))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset_addr (if add
                          (bvplus 32 (reg n arm) imm32)
                        (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (if (and (HaveLPAE)
                       (== (slice 2 0 address) #b000))
                  (let ((data (MemA address 8 arm)))
                    (if (BigEndian)
                        (let* ((arm (set-reg tval (slice 63 32 data) arm))
                               (arm (set-reg t2 (slice 31 0 data) arm)))
                          arm)
                      (let* ((arm (set-reg tval (slice 31 0 data) arm))
                             (arm (set-reg t2 (slice 63 32 data) arm)))
                        arm)))
                (let* ((arm (set-reg tval (MemA address 4 arm) arm))
                       (arm (set-reg t2 (MemA (bvplus 32 address 4) 4 arm) arm)))
                  arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm)
  :guard-hints (("Goal" :in-theory (enable uint))))

(def-inst :ldrd-literal
    (ldrd-literal-core u rt imm4H imm4L inst-address arm))

(def-inst :ldrd-register
    (b* (;; EncodingSpecificOperations:
         ((when (== (getbit 0 rt) #b1))
          (update-error *unpredictable* arm))
         (tval (uint 4 rt))
         (t2 (+ tval 1)) ; tval can't be 15 because it's low bit is not 1
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and (== p #b0)
                     (== w #b1)))
          (update-error *unpredictable* arm))
         ((when (or (== t2 15)
                    (== m 15)
                    (== m tval)
                    (== m t2)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval)
                         (== n t2))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add
                          (bvplus 32 (reg n arm) (reg m arm))
                        (bvminus 32 (reg n arm) (reg m arm))))
         (address (if index offset_addr (reg n arm)))
         (arm (if (and (HaveLPAE)
                       (== (slice 2 0 address) #b000))
                  (let ((data (MemA address 8 arm)))
                    (if (BigEndian)
                        (let* ((arm (set-reg tval (slice 63 32 data) arm))
                               (arm (set-reg t2 (slice 31 0 data) arm)))
                          arm)
                      (let* ((arm (set-reg tval (slice 31 0 data) arm))
                             (arm (set-reg t2 (slice 63 32 data) arm)))
                        arm)))
                (let* ((arm (set-reg tval (MemA address 4 arm) arm))
                       (arm (set-reg t2 (MemA (bvplus 32 address 4) 4 arm) arm)))
                  arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm)
  :guard-hints (("Goal" :in-theory (enable uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LDRHT has been moved here (out of alphabetical order) because other
;; instructions refer to it.

(defun ldrht-common (n tval postindex add register_form imm32 m arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (reg m arm) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (data (MemU_unpriv address 2 arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm))
       (arm (if (or (UnalignedSupport)
                    (== (getbit 0 address) #b0))
                (set-reg tval (ZeroExtend data 32) arm)
              (set-reg tval (unknown-bits 32 :ldrht-common arm) arm))))
    arm))

;; Also called by ldr-literal and ldr-immediate.
(defun ldrht-encoding-a1-core (u rn rt imm4H imm4L arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       (m 0) ; arbitrary (unspecified but unused below)
       ;; end EncodingSpecificOperations
       )
    (ldrht-common n tval postindex add register_form imm32 m arm)))

;; Also called by ldr-register
(defund ldrht-encoding-a2-core (u rn rt rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u #b1))
       (register_form *true*)
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (ldrht-common n tval postindex add register_form imm32 m arm)))

(def-inst :ldrht-encoding-a1
    (ldrht-encoding-a1-core u rn rt imm4H imm4L arm))

(def-inst :ldrht-encoding-a2
    (ldrht-encoding-a2-core u rn rt rm arm))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by ldrh-immediate
(defun ldrh-literal-core (p u w rt imm4H imm4L inst-address arm)
  (declare (xargs :guard (and (bitp p)
                              (bitp u)
                              (bitp w)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== p #b0)
                   (== w #b1)))
        ;; Note: The manual says "SEE LDHRT" but I am going to assume it means "SEE LDRHT"
        (ldrht-encoding-a1-core u #b1111 ;rn
                                rt imm4H imm4L arm))
       ((when (== p w))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       (add (== u 1))
       ((when (== tval 15))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE 15 arm))
       (base (align (pcvalue inst-address) 4))
       (address (if add (bvplus 32 base imm32) (bvminus 32 base imm32)))
       (data (MemU address 2 arm))
       (arm (if (or (UnalignedSupport)
                    (== (getbit 0 address) #b0))
                (set-reg tval (ZeroExtend data 32) arm)
              (set-reg tval (unknown-bits 32 :ldrh-literal-core arm) arm))))
    arm))

(def-inst :ldrh-literal
    (ldrh-literal-core p u w rt imm4H imm4L inst-address arm))

(def-inst :ldrh-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldrh-literal-core p u w rt imm4H imm4L inst-address arm))
         ((when (and (== p #b0) ; todo: add #b to all bit string, like we do here
                     (== w #b1)))
          (ldrht-encoding-a1-core u rn rt imm4H imm4L arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (or (== tval 15)
                    (and wback
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 2 arm))
         (arm (if wback (set-reg n offset_addr arm) arm))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                (set-reg tval (ZeroExtend data 32) arm)
              (set-reg tval (unknown-bits 32 :ldrh-immediate arm) arm))))
      arm))

(def-inst :ldrh-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (ldrht-encoding-a2-core u rn rt rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (mv *SRType_LSL* 0))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 2 arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                  (set-reg tval (ZeroExtend data 32) arm)
                (set-reg tval (unknown-bits 32 :ldrh-register arm) arm))))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by LSL
(defun mov-register-core (s rd rm arm)
  (declare (xargs :guard (and (bitp s)
                              (register-numberp rd)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== rd #b1111)
                   (== s #b1)))
        (update-error *unsupported* arm))
       (d (uint 4 rd))
       (m (uint 4 rm))
       (setflags (== s #b1))
       ;; end EncodingSpecificOperations
       (result (reg m arm)))
    (if (== d 15)
        (ALUWritePC result arm)
      (b* ((arm (set-reg d result arm))
           (arm (if setflags
                    (let* ((arm (set-apsr.n (getbit 31 result) arm))
                           (arm (set-apsr.z (IsZeroBit 32 result) arm))
                           ;; C is unchanged
                           ;; V is unchanged
                           )
                      arm)
                  arm)))
        arm))))

(def-inst :lsl-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         ((when (== imm5 #b00000))
          (mov-register-core s rd rm arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv & shift_n) (decodeImmShift #b00 imm5))
         ;; end EncodingSpecificOperations
         ((mv result carry) (shift_c 32 (reg m arm) *SRType_LSL* shift_n (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :lsl-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg m arm))))
         ((mv result carry) (shift_c 32 (reg n arm) *SRType_LSL* shift_n (apsr.c arm)))
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

(def-inst :lsr-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv & shift_n) (decodeImmShift #b01 imm5))
         ;; end EncodingSpecificOperations
         ((mv result carry) (shift_c 32 (reg m arm) *SRType_LSR* shift_n (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :lsr-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg m arm))))
         ((mv result carry) (shift_c 32 (reg n arm) *SRType_LSR* shift_n (apsr.c arm)))
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

(def-inst :mla
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (a (uint 4 ra))
         (setflags (== s #b1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== a 15)))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (== d n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (operand1 (sint 32 (reg n arm)))
         (operand2 (sint 32 (reg m arm)))
         (addend (sint 32 (reg a arm)))
         (result (+ (* operand1 operand2) addend))
         (arm (set-reg rd (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 (slice 31 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit :mla arm)
                                            (apsr.c arm))
                                          arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :mls
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (a (uint 4 ra))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== a 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (operand1 (sint 32 (reg n arm)))
         (operand2 (sint 32 (reg m arm)))
         (addend (sint 32 (reg a arm)))
         (result (- addend (* operand1 operand2)))
         (arm (set-reg rd (slice 31 0 result) arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund mov-common (d setflags imm32 carry arm)
  (declare (xargs :guard (and (register-numberp d)
                              (booleanp setflags)
                              (unsigned-byte-p 32 imm32)
                              (bitp carry))
                  :stobjs arm))
  (let ((result imm32))
    (if (== d 15)
        (ALUWritePC result arm)
      (b* ((arm (set-reg d result arm))
           (arm (if setflags
                    (let* ((arm (set-apsr.n (getbit 31 result) arm))
                           (arm (set-apsr.z (IsZeroBit 32 result) arm))
                           (arm (set-apsr.c carry arm))
                           ;; V is unchanged
                           )
                      arm)
                  arm)))
        arm))))

(def-inst :mov-immediate ; encoding A1 is mov
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         )
      (mov-common d setflags imm32 carry arm)))

(def-inst :movw-immediate  ; encoding A2 is movw
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (setflags *false*)
         (imm32 (ZeroExtend (bvcat 4 imm4 12 imm12) 32))
         ((when (== d 15))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (carry 0) ;; Irrelevant since setflags is FALSE
         )
      (mov-common d setflags imm32 carry arm))
  :guard-debug t)



(def-inst :mov-register
    (mov-register-core s rd rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :mul
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (== d n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (operand1 (sint 32 (reg n arm)))
         (operand2 (sint 32 (reg m arm)))
         (result (* operand1 operand2))
         (arm (set-reg rd (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 (slice 31 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit :mul arm)
                                            (apsr.c arm))
                                          arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :mvn-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (bvnot 32 imm32)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :mvn-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvnot 32 shifted)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :mvn-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (bvnot 32 shifted))
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

(def-inst :nop
    (b* (;; EncodingSpecificOperations:
         ;; (none)
         ;; end EncodingSpecificOperations
         ;; (nothing to do)
         )
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :orr-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (or32 (reg n arm) imm32)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :orr-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (or32 (reg n arm) shifted)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

(def-inst :orr-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (or32 (reg n arm) shifted))
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

(def-inst :pop-encoding-a1
    (if (< (BitCount 16 register_list) 2)
        (ldm-core 1 #b1101 register_list arm)
      (pop-encoding-a1-core register_list arm)))

(def-inst :pop-encoding-a2
    (pop-encoding-a2-core rt arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :rrx
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ;; end EncodingSpecificOperations
         ((mv result carry) (shift_c 32 (reg m arm) :SRType_RRX 1 (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             ;; V is unchanged
                             )
                        arm)
                    arm)))
          arm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :rsb-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) imm32 1)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :rsb-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         ;; No need to check for SUB (SP minus register)
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) shifted 1)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :rsb-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) shifted 1))
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

(def-inst :rsc-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) imm32 (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :rsc-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         ;; No need to check for SUB (SP minus register)
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) shifted  (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :rsc-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (bvnot 32 (reg n arm)) shifted (apsr.c arm)))
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

(def-inst :sbc-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 imm32) (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :sbc-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         ;; No need to check for SUB (SP minus register)
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) (apsr.c arm))))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :sbc-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) (apsr.c arm)))
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

(def-inst :smlal
    (b* (;; EncodingSpecificOperations:
         (dLo (uint 4 RdLo))
         (dHi (uint 4 RdHi))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== dLo 15)
                    (== dHi 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (== dLo dHi))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (or (== dHi n)
                         (== dLo n))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (result (+ (* (sint 32 (reg n arm))
                       (sint 32 (reg m arm)))
                    (sint 64 (bvcat 32 (reg dHi arm) 32 (reg dLo arm)))))
         (arm (set-reg dHi (slice 63 32 result) arm))
         (arm (set-reg dLo (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 63 result) arm))
                         (arm (set-apsr.z (IsZeroBit 64 (slice 63 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :smlal :c) arm)
                                            (apsr.c arm))
                                          arm))
                         (arm (set-apsr.v (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :smlal :v) arm)
                                            (apsr.v arm))
                                          arm)))
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :smull
    (b* (;; EncodingSpecificOperations:
         (dLo (uint 4 RdLo))
         (dHi (uint 4 RdHi))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== dLo 15)
                    (== dHi 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (== dLo dHi))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (or (== dHi n)
                         (== dLo n))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (result (* (sint 32 (reg n arm))
                    (sint 32 (reg m arm))))
         (arm (set-reg dHi (slice 63 32 result) arm))
         (arm (set-reg dLo (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 63 result) arm))
                         (arm (set-apsr.z (IsZeroBit 64 (slice 63 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :smull :c) arm)
                                            (apsr.c arm))
                                          arm))
                         (arm (set-apsr.v (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :smull :v) arm)
                                            (apsr.v arm))
                                          arm)))
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :sub-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rn #b1111)
                     (== s 0)))
          ;; it's encoding A2 because of bits 24-21:
          (adr-encoding-a2-core rd imm12 inst-address arm))
         ;; No need to check for SUB (SP minus immediate)
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (setflags (== s #b1))
         (imm32 (ARMExpandImm imm12 arm))
         ;; end EncodingSpecificOperations
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 imm32) 1)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :sub-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== rd #b1111)
                     (== s #b1)))
          ;; todo:
          (update-error *unsupported* arm))
         ;; No need to check for SUB (SP minus register)
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) 1)))
      (if (== d 15)
          (ALUWritePC result arm)
        (b* ((arm (set-reg d result arm))
             (arm (if setflags
                      (let* ((arm (set-apsr.n (getbit 31 result) arm))
                             (arm (set-apsr.z (IsZeroBit 32 result) arm))
                             (arm (set-apsr.c carry arm))
                             (arm (set-apsr.v overflow arm)))
                        arm)
                    arm)))
          arm))))

(def-inst :sub-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs)) ; use sval since S is a field of the inst
         (setflags (== s #b1))
         (shift_t (DecodeRegShift type))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         ((mv result carry overflow) (AddWithCarry 32 (reg n arm) (bvnot 32 shifted) 1))
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

(def-inst :teq-immediate
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
         ;; end EncodingSpecificOperations
         (result (eor32 (reg n arm) imm32))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         ;; V is unchanged
         )
      arm))

(def-inst :teq-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (eor32 (reg n arm) shifted))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         ;; V is unchanged
         )
      arm))

(def-inst :teq-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (shift_t (DecodeRegShift type))
         ((when (or (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (eor32 (reg n arm) shifted))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         ;; V is unchanged
         )
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun tst-immediate-core (rn imm12 arm)
  (declare (xargs :guard (and (register-numberp rn)
                              (unsigned-byte-p 12 imm12))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       (n (uint 4 rn))
       ((mv imm32 carry) (ARMExpandImm_C imm12 (apsr.c arm)))
       ;; end EncodingSpecificOperations
       (result (and32 (reg n arm) imm32))
       (arm (set-apsr.n (getbit 31 result) arm))
       (arm (set-apsr.z (IsZeroBit 32 result) arm))
       (arm (set-apsr.c carry arm))
       ;; V is unchanged
       )
    arm))

(def-inst :tst-immediate
    (tst-immediate-core rn imm12 arm))

(def-inst :tst-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ;; end EncodingSpecificOperations
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (and32 (reg n arm) shifted))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         ;; V is unchanged
         )
      arm))

(def-inst :tst-register-shifted-register
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (m (uint 4 rm))
         (sval (uint 4 rs))
         (shift_t (DecodeRegShift type))
         ((when (or (== n 15)
                    (== m 15)
                    (== sval 15)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (shift_n (uint 8 (slice 7 0 (reg sval arm))))
         ((mv shifted carry) (shift_c 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (result (and32 (reg n arm) shifted))
         (arm (set-apsr.n (getbit 31 result) arm))
         (arm (set-apsr.z (IsZeroBit 32 result) arm))
         (arm (set-apsr.c carry arm))
         ;; V is unchanged
         )
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :umlal
    (b* (;; EncodingSpecificOperations:
         (dLo (uint 4 RdLo))
         (dHi (uint 4 RdHi))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== dLo 15)
                    (== dHi 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (== dLo dHi))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (or (== dHi n)
                         (== dLo n))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (result (+ (* (uint 32 (reg n arm))
                       (uint 32 (reg m arm)))
                    (uint 64 (bvcat 32 (reg dHi arm) 32 (reg dLo arm)))))
         (arm (set-reg dHi (slice 63 32 result) arm))
         (arm (set-reg dLo (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 63 result) arm))
                         (arm (set-apsr.z (IsZeroBit 64 (slice 63 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :umlal :c) arm)
                                            (apsr.c arm))
                                          arm))
                         (arm (set-apsr.v (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :umlal :v) arm)
                                            (apsr.v arm))
                                          arm)))
                    arm)
                arm)))
      arm))

(def-inst :umull
    (b* (;; EncodingSpecificOperations:
         (dLo (uint 4 RdLo))
         (dHi (uint 4 RdHi))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s #b1))
         ((when (or (== dLo 15)
                    (== dHi 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (== dLo dHi))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     (or (== dHi n)
                         (== dLo n))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (result (* (uint 32 (reg n arm))
                    (uint 32 (reg m arm))))
         (arm (set-reg dHi (slice 63 32 result) arm))
         (arm (set-reg dLo (slice 31 0 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 63 result) arm))
                         (arm (set-apsr.z (IsZeroBit 64 (slice 63 0 result)) arm))
                         (arm (set-apsr.c (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :umull :c) arm)
                                            (apsr.c arm))
                                          arm))
                         (arm (set-apsr.v (if (== (ArchVersion) 4)
                                              (unknown-bit (cons :umull :v) arm)
                                            (apsr.v arm))
                                          arm)))
                    arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LDRSBT has been moved here (out of alphabetical order) because other
;; instructions refer to it.

(defun ldrsbt-common (n tval postindex add register_form imm32 m arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (reg m arm) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (arm (set-reg tval (SignExtend (MemU_unpriv address 1 arm) 8 32) arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm)))
    arm))

;; Also called by ldr-literal and ldr-immediate.
(defun ldrsbt-encoding-a1-core (u rn rt imm4H imm4L arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       (m 0) ; arbitrary (unspecified but unused below)
       ;; end EncodingSpecificOperations
       )
    (ldrsbt-common n tval postindex add register_form imm32 m arm)))

;; Also called by ldr-register ;; toso: update these and all similar comments
(defund ldrsbt-encoding-a2-core (u rn rt rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u 1))
       (register_form *true*)
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (ldrsbt-common n tval postindex add register_form imm32 m arm)))

(def-inst :ldrsbt-encoding-a1
    (ldrsbt-encoding-a1-core u rn rt imm4H imm4L arm))

(def-inst :ldrsbt-encoding-a2
    (ldrsbt-encoding-a2-core u rn rt rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by ldrsb-immediate
(defun ldrsb-literal-core (p u w rt imm4H imm4L inst-address arm)
  (declare (xargs :guard (and (bitp p)
                              (bitp u)
                              (bitp w)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== p #b0)
                   (== w #b1)))
        (ldrsbt-encoding-a1-core u #b1111 ;rn
                                 rt imm4H imm4L arm))
       ((when (== p w))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       (add (== u #b1))
       ((when (== tval 15))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE 15 arm))
       (base (align (pcvalue inst-address) 4))
       (address (if add (bvplus 32 base imm32) (bvminus 32 base imm32)))
       (arm (set-reg tval (SignExtend (MemU address 1 arm) 8 32) arm)))
    arm))

(def-inst :ldrsb-literal
    (ldrsb-literal-core p u w rt imm4H imm4L inst-address arm))

(def-inst :ldrsb-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldrsb-literal-core p u w rt imm4H imm4L inst-address arm))
         ((when (and (== p 0)
                     (== w 1)))
          (ldrsbt-encoding-a1-core u rn rt imm4H imm4L arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (or (== tval 15)
                    (and wback
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (set-reg tval (SignExtend (MemU address 1 arm) 8 32) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

(def-inst :ldrsb-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (ldrsbt-encoding-a2-core u rn rt rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (mv *SRType_LSL* 0))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (arm (set-reg tval (SignExtend (MemU address 1 arm) 8 32) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LDRHT has been moved here (out of alphabetical order) because other
;; instructions refer to it.

(defun ldrsht-common (n tval postindex add register_form imm32 m arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (reg m arm) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (data (MemU_unpriv address 2 arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm))
       (arm (if (or (UnalignedSupport)
                    (== (getbit 0 address) #b0))
                (set-reg tval (SignExtend data 16 32) arm)
              (set-reg tval (unknown-bits 32 :ldrsht-common arm) arm))))
    arm))

;; Also called by ldr-literal and ldr-immediate.
(defun ldrsht-encoding-a1-core (u rn rt imm4H imm4L arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       (m 0) ; arbitrary (unspecified but unused below)
       ;; end EncodingSpecificOperations
       )
    (ldrsht-common n tval postindex add register_form imm32 m arm)))

;; Also called by ldr-register
(defund ldrsht-encoding-a2-core (u rn rt rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u #b1))
       (register_form *true*)
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (ldrsht-common n tval postindex add register_form imm32 m arm)))

(def-inst :ldrsht-encoding-a1
    (ldrsht-encoding-a1-core u rn rt imm4H imm4L arm))

(def-inst :ldrsht-encoding-a2
    (ldrsht-encoding-a2-core u rn rt rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Also called by ldrsh-immediate
(defun ldrsh-literal-core (p u w rt imm4H imm4L inst-address arm)
  (declare (xargs :guard (and (bitp p)
                              (bitp u)
                              (bitp w)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       ((when (and (== p #b0)
                   (== w #b1)))
        (ldrsht-encoding-a1-core u #b1111 ;rn
                                rt imm4H imm4L arm))
       ((when (== p w))
        (update-error *unpredictable* arm))
       (tval (uint 4 rt)) ; can't use "t" since it means true in Lisp
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       (add (== u 1))
       ((when (== tval 15))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE 15 arm))
       (base (align (pcvalue inst-address) 4))
       (address (if add (bvplus 32 base imm32) (bvminus 32 base imm32)))
       (data (MemU address 2 arm))
       (arm (if (or (UnalignedSupport)
                    (== (getbit 0 address) #b0))
                (set-reg tval (SignExtend data 16 32) arm)
              (set-reg tval (unknown-bits 32 :ldrsh-literal-core arm) arm))))
    arm))

(def-inst :ldrsh-literal
    (ldrsh-literal-core p u w rt imm4H imm4L inst-address arm))

(def-inst :ldrsh-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== rn #b1111))
          (ldrsh-literal-core p u w rt imm4H imm4L inst-address arm))
         ((when (and (== p #b0) ; todo: add #b to all bit strings, like we do here
                     (== w #b1)))
          (ldrsht-encoding-a1-core u rn rt imm4H imm4L arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (or (== tval 15)
                    (and wback
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 2 arm))
         (arm (if wback (set-reg n offset_addr arm) arm))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                (set-reg tval (SignExtend data 16 32) arm)
              (set-reg tval (unknown-bits 32 :ldrsh-immediate arm) arm))))
      arm))

(def-inst :ldrsh-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (ldrsht-encoding-a2-core u rn rt rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (mv *SRType_LSL* 0))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (data (MemU address 2 arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                  (set-reg tval (SignExtend data 16 32) arm)
                (set-reg tval (unknown-bits 32 :ldrsh-register arm) arm))))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun strt-common (n tval postindex add register_form imm32 m shift_t shift_n inst-address arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32)
                              (SRTypep shift_t)
                              (not (and (eq shift_t *SRType_RRX*) ;todo: think about this
                                        (not (equal shift_n 1))))
                              (natp shift_n)
                              (addressp inst-address))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (Shift 32 (reg m arm) shift_t shift_n (apsr.c arm)) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (data (if (== tval 15)
                 (PCStoreValue inst-address)
               (reg tval arm)))
       (arm (if (or (UnalignedSupport)
                    (== (slice 1 0 address) #b00)
                    (== (CurrentInstrSet) *InstrSet_ARM*))
                (write_MemU_unpriv address 4 data arm)
              (write_MemU_unpriv address 4 (unknown-bits 32 :strt-common arm) arm)))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm)))
    arm))

;; todo; add all "also called by" comments, everywhere
(defun strt-encoding-a1-core (u rn rt imm12 inst-address arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend imm12 32))
       ((when (or (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       ((mv shift_t shift_n) (mv *SRType_LSL* 1)) ; arbitrary (unspecified but unused below)
       (m 0) ; arbitrary (unspecified but unused below)
       )
    (strt-common n tval postindex add register_form imm32 m shift_t shift_n inst-address arm)))

(def-inst :strt-encoding-a1
    (strt-encoding-a1-core u rn rt imm12 inst-address arm))

(defun strt-encoding-a2-core (u rn rt imm5 type rm inst-address arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 5 imm5)
                              (unsigned-byte-p 2 type)
                              (register-numberp rm)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u #b1))
       (register_form *true*)
       ((mv shift_t shift_n) (decodeImmShift type imm5))
       ((when (or (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ((when (and (< (ArchVersion) 6)
                   (== m n)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (strt-common n tval postindex add register_form imm32 m shift_t shift_n inst-address arm)))

(def-inst :strt-encoding-a2
    (strt-encoding-a2-core u rn rt imm5 type rm inst-address arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv address arm).
(defun push-loop (i registers address UnalignedAllowed arm)
  (declare (xargs :guard (and (natp i)
                              (<= i 15)
                              (unsigned-byte-p 16 registers)
                              (addressp address)
                              (booleanp UnalignedAllowed))
                  :stobjs arm
                  :measure (nfix (+ 1 (- 14 i)))))
  (if (or (not (mbt (natp i)))
          (< 14 i))
      (mv address arm)
    (b* (((mv address arm)
          (if (== (getbit i registers) 1)
              (let* ((arm (if (and (== i 13)
                                   (!= i (LowestSetBit 16 registers)))
                              (write_MemA address 4 (unknown-bits 32 :push-loop arm) arm)
                            (if UnalignedAllowed
                                (write_MemU address 4 (reg i arm) arm)
                              (write_MemA address 4 (reg i arm) arm))))
                     (address (bvplus 32 address 4)) ; call a + address function?
                     )
                (mv address arm))
            (mv address arm))))
      (push-loop (+ 1 i) registers address UnalignedAllowed arm))))

(defthm push-loop-return-type
  (implies (addressp address)
           (and (addressp (mv-nth 0 (push-loop i registers address UnalignedAllowed arm)))
                (integerp (mv-nth 0 (push-loop i registers address UnalignedAllowed arm))))))

(defun push-common (registers UnalignedAllowed inst-address arm)
  (declare (xargs :guard (and (unsigned-byte-p 16 registers)
                              (booleanp UnalignedAllowed)
                              (addressp inst-address))
                  :guard-hints (("Goal" :in-theory (disable addressp)))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE 13 arm))
       (address (bvminus 32 (reg *sp* arm) ; todo: any offset to SP like for PC?
                         (* 4 (BitCount 16 registers))))
       ((mv address arm)
        (push-loop 0 registers address UnalignedAllowed arm))
       (arm (if (== (getbit 15 registers) 1)
                (if UnalignedAllowed
                    (write_MemU address 4 (PCStoreValue inst-address) arm)
                  (write_MemA address 4 (PCStoreValue inst-address) arm))
              arm))
       (arm (set-reg *sp*
                     (bvminus 32 (reg *sp* arm) ; todo: any offset to SP like for PC?
                              (* 4 (BitCount 16 registers)))
                     arm)))
    arm))

(defun push-encoding-a2-core (rt inst-address arm)
  (declare (xargs :guard (and (register-numberp rt)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (registers (Zeros 16))
       (registers (putbit 16 tval 1 registers))
       (UnalignedAllowed *true*)
       ((when (== tval 13))
        (update-error *unpredictable* arm)))
    (push-common registers UnalignedAllowed inst-address arm)))

(def-inst :push-encoding-a2
    (push-encoding-a2-core rt inst-address arm))

(defun push-encoding-a1-core (register_list inst-address arm)
  (declare (xargs :guard (and (unsigned-byte-p 16 register_list)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations (continued):
       (registers register_list)
       (UnalignedAllowed *false*))
    (push-common registers UnalignedAllowed inst-address arm)))

;; Returns (mv address arm).
;; Also used or STMDB.
(defun stm-loop (i registers address wback n arm)
  (declare (xargs :guard (and (natp i)
                              (<= i 15)
                              (unsigned-byte-p 16 registers)
                              (addressp address)
                              (booleanp wback)
                              (register-numberp n))
                  :stobjs arm
                  :measure (nfix (+ 1 (- 14 i)))))
  (if (or (not (mbt (natp i)))
          (< 14 i))
      (mv address arm)
    (b* (((mv address arm)
          (if (== (getbit i registers) 1)
              (let* ((arm (if (and (== i n)
                                   wback
                                   (!= i (LowestSetBit 16 registers)))
                              (write_MemA address 4 (unknown-bits 32 :stm-loop arm) arm) ; distinguish from the STMDB case?
                            (write_MemA address 4 (reg i arm) arm)))
                     (address (bvplus 32 address 4)))
                (mv address arm))
            (mv address arm))))
      (stm-loop (+ 1 i) registers address wback n arm))))

(defthm stm-loop-return-type
  (implies (addressp address)
           (addressp (mv-nth 0 (stm-loop i registers address wback n arm)))))

(defun stmdb-core (w rn register_list inst-address arm)
  (declare (xargs :guard (and (bitp w)
                              (register-numberp rn)
                              (unsigned-byte-p 16 register_list)
                              (addressp inst-address))
                  :stobjs arm))
  (b* (;; EncodingSpecificOperations (continued):
       (n (uint 4 rn))
       (registers register_list)
       (wback (== w #b1))
       ((when (or (== n 15)
                  (< (BitCount 16 registers) 1)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (arm (NullCheckIfThumbEE n arm))
       (address (bvminus 32 (reg n arm) (* 4 (bitcount 16 registers))))
       ((mv address arm) (stm-loop 0 registers address wback n arm))
       (arm (if (== (getbit 15 registers) 1)
                (write_MemA address 4 (PCStoreValue inst-address) arm)
              arm))
       (arm (if wback
                (set-reg n (bvplus 32 (reg n arm) (* 4 (bitcount 16 registers))) arm)
              arm)))
    arm))

(def-inst :push-encoding-a1
    (if (< (BitCount 16 register_list) 2)
        (stmdb-core #b1 ; w
                    #b1101 ;rn
                    register_list inst-address arm)
      (push-encoding-a1-core register_list inst-address arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :str-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strt-encoding-a1-core u rn rt imm12 inst-address arm))
         ((when (and (== rn #b1101)
                     (== p 1)
                     (== u 0)
                     (== w 1)
                     (== imm12 #b000000000100)))
          (push-encoding-a2-core rt inst-address arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend imm12 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (write_MemU address 4 (if (== tval 15) (PCStoreValue inst-address) (reg tval arm)) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

(def-inst :str-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strt-encoding-a2-core u rn rt imm5 type rm inst-address arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ((when (== m 15))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (data (if (== tval 15)
                   (PCStoreValue inst-address)
                 (reg tval arm)))
         (arm (if (or (UnalignedSupport)
                      (== (slice 1 0 address) #b00)
                      (== (CurrentInstrSet) *InstrSet_ARM*))
                  (write_MemU address 4 data arm)
                (write_MemU address 4 (unknown-bits 32 :str-register arm) arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun strbt-common (n tval postindex add register_form imm32 m shift_t shift_n arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32)
                              (SRTypep shift_t)
                              (not (and (eq shift_t *SRType_RRX*) ;todo: think about this
                                        (not (equal shift_n 1))))
                              (natp shift_n))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (Shift 32 (reg m arm) shift_t shift_n (apsr.c arm)) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (arm (write_MemU_unpriv address 1 (slice 7 0 (reg tval arm)) arm))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm)))
    arm))

(defun strbt-encoding-a1-core (u rn rt imm12 arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 12 imm12))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend imm12 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       ((mv shift_t shift_n) (mv *SRType_LSL* 1)) ; arbitrary (unspecified but unused below)
       (m 0) ; arbitrary (unspecified but unused below)
       )
    (strbt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

(def-inst :strbt-encoding-a1
    (strbt-encoding-a1-core u rn rt imm12 arm))

(defun strbt-encoding-a2-core (u rn rt imm5 type rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 5 imm5)
                              (unsigned-byte-p 2 type)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u #b1))
       (register_form *true*)
       ((mv shift_t shift_n) (decodeImmShift type imm5))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ((when (and (< (ArchVersion) 6)
                   (== m n)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (strbt-common n tval postindex add register_form imm32 m shift_t shift_n arm)))

(def-inst :strbt-encoding-a2
    (strbt-encoding-a2-core u rn rt imm5 type rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :strb-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strbt-encoding-a1-core u rn rt imm12 arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend imm12 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (== tval 15))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (write_MemU address 1 (slice 7 0 (reg tval arm)) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

(def-inst :strb-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strbt-encoding-a2-core u rn rt imm5 type rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (decodeImmShift type imm5))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (arm (write_MemU address 1 (slice 7 0 (reg tval arm)) arm))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun strht-common (n tval postindex add register_form imm32 m arm)
  (declare (xargs :guard (and (register-numberp n)
                              (register-numberp tval)
                              (register-numberp m)
                              (booleanp postindex)
                              (booleanp add)
                              (booleanp register_form)
                              (unsigned-byte-p 32 imm32))
                  :stobjs arm))
  (b* ((arm (NullCheckIfThumbEE n arm))
       (offset (if register_form (reg m arm) imm32))
       (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
       (address (if postindex (reg n arm) offset_addr))
       (arm (if (or (UnalignedSupport)
                    (== (getbit 0 address) #b0))
                (write_MemU_unpriv address 2 (slice 15 0 (reg tval arm)) arm)
              (write_MemU_unpriv address 2 (unknown-bits 16 :strht-common arm) arm)))
       (arm (if postindex
                (set-reg n offset_addr arm)
              arm)))
    arm))

(defun strht-encoding-a1-core (u rn rt imm4H imm4L arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (unsigned-byte-p 4 imm4H)
                              (unsigned-byte-p 4 imm4L))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (postindex *true*)
       (add (== u #b1))
       (register_form *false*)
       (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (m 0) ; arbitrary (unspecified but unused below)
       )
    (strht-common n tval postindex add register_form imm32 m arm)))

(def-inst :strht-encoding-a1
    (strht-encoding-a1-core u rn rt imm4H imm4L arm))

(defun strht-encoding-a2-core (u rn rt rm arm)
  (declare (xargs :guard (and (bitp u)
                              (register-numberp rn)
                              (register-numberp rt)
                              (register-numberp rm))
                  :stobjs arm))
  (b* (((when (CurrentModeIsHyp)) (update-error *unpredictable* arm))
       ;; EncodingSpecificOperations:
       (tval (uint 4 rt))
       (n (uint 4 rn))
       (m (uint 4 rm))
       (postindex *true*)
       (add (== u #b1))
       (register_form *true*)
       ((when (or (== tval 15)
                  (== n 15)
                  (== n tval)
                  (== m 15)))
        (update-error *unpredictable* arm))
       ;; end EncodingSpecificOperations
       (imm32 0) ; arbitrary (unspecified but unused below)
       )
    (strht-common n tval postindex add register_form imm32 m arm)))

(def-inst :strht-encoding-a2
    (strht-encoding-a2-core u rn rt rm arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :strh-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strht-encoding-a1-core u rn rt imm4H imm4L arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (== tval 15))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add (bvplus 32 (reg n arm) imm32) (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                  (write_MemU address 2 (slice 15 0 (reg tval arm)) arm)
                (write_MemU address 2 (unknown-bits 16 :strh-immediate arm) arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

(def-inst :strh-register
    (b* (;; EncodingSpecificOperations:
         ((when (and (== p #b0)
                     (== w #b1)))
          (strht-encoding-a2-core u rn rt rm arm))
         (tval (uint 4 rt))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((mv shift_t shift_n) (mv *SRType_LSL* 0))
         ((when (or (== tval 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
         (offset_addr (if add (bvplus 32 (reg n arm) offset) (bvminus 32 (reg n arm) offset)))
         (address (if index offset_addr (reg n arm)))
         (arm (if (or (UnalignedSupport)
                      (== (getbit 0 address) #b0))
                  (write_MemU address 2 (slice 15 0 (reg tval arm)) arm)
                (write_MemU address 2 (unknown-bits 16 :strh-register arm) arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :strd-immediate
    (b* (;; EncodingSpecificOperations:
         ((when (== (getbit 0 rt) #b1))
          (update-error *unpredictable* arm))
         (tval (uint 4 rt))
         (t2 (+ tval 1)) ; tval can't be 15 because it's low bit is not 1
         (n (uint 4 rn))
         (imm32 (ZeroExtend (bvcat 4 imm4H 4 imm4L) 32))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and (== p #b0)
                     (== w #b1)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval)
                         (== n t2))))
          (update-error *unpredictable* arm))
         ((when (== t2 15))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (offset_addr (if add
                          (bvplus 32 (reg n arm) imm32)
                        (bvminus 32 (reg n arm) imm32)))
         (address (if index offset_addr (reg n arm)))
         (arm (if (and (HaveLPAE)
                       (== (slice 2 0 address) #b000))
                  (let* ((data (if (BigEndian)
                                  (bvcat 32 (reg tval arm) 32 (reg t2 arm))
                                 (bvcat 32 (reg t2 arm) 32 (reg tval arm))))
                         (arm (write_MemA address 8 data arm)))
                    arm)
                (let* ((arm (write_MemA address 4 (reg tval arm) arm))
                       (arm (write_MemA (bvplus 32 address 4) 4 (reg t2 arm) arm)))
                  arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm)
  :guard-hints (("Goal" :in-theory (enable uint))))

(def-inst :strd-register
    (b* (;; EncodingSpecificOperations:
         ((when (== (getbit 0 rt) #b1))
          (update-error *unpredictable* arm))
         (tval (uint 4 rt))
         (t2 (+ tval 1)) ; tval can't be 15 because it's low bit is not 1
         (n (uint 4 rn))
         (m (uint 4 rm))
         (index (== p #b1))
         (add (== u #b1))
         (wback (or (== p #b0)
                    (== w #b1)))
         ((when (and (== p #b0)
                     (== w #b1)))
          (update-error *unpredictable* arm))
         ((when (or (== t2 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and wback
                     (or (== n 15)
                         (== n tval)
                         (== n t2))))
          (update-error *unpredictable* arm))
         ((when (and (< (ArchVersion) 6)
                     wback
                     (== m n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (offset_addr (if add
                          (bvplus 32 (reg n arm) (reg m arm))
                        (bvminus 32 (reg n arm) (reg m arm))))
         (address (if index offset_addr (reg n arm)))
         (arm (if (and (HaveLPAE)
                       (== (slice 2 0 address) #b000))
                  (let* ((data (if (BigEndian)
                                  (bvcat 32 (reg tval arm) 32 (reg t2 arm))
                                 (bvcat 32 (reg t2 arm) 32 (reg tval arm))))
                         (arm (write_MemA address 8 data arm)))
                    arm)
                (let* ((arm (write_MemA address 4 (reg tval arm) arm))
                       (arm (write_MemA (bvplus 32 address 4) 4 (reg t2 arm) arm)))
                  arm)))
         (arm (if wback
                  (set-reg n offset_addr arm)
                arm)))
      arm)
  :guard-hints (("Goal" :in-theory (enable uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :stm/stmia/stmea
    (b* (;; EncodingSpecificOperations:
         (n (uint 4 rn))
         (registers register_list)
         (wback (== w #b1))
         ((when (or (== n 15)
                    (< (BitCount 16 registers) 1)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations
         (arm (NullCheckIfThumbEE n arm))
         (address (reg n arm))
         ((mv address arm) (stm-loop 0 registers address wback n arm))
         (arm (if (== (getbit 15 registers) 1)
                  (write_MemA address 4 (PCStoreValue inst-address) arm)
                arm))
         (arm (if wback
                  (set-reg n (bvplus 32 (reg n arm) (* 4 (bitcount 16 registers))) arm)
                arm)))
      arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :stmdb/stmfd
    (if (and (== w #b1)
             (== rn #b1101)
             (>= (BitCount 16 register_list) 2))
        (push-encoding-a1-core register_list inst-address arm)
      (stmdb-core w rn register_list inst-address arm)))
