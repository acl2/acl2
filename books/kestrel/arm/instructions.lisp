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

(defconst *unpredictable* :unpredictable)
(defconst *unsupported* :unsupported)

(defun eor32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvxor 32 x y))

(defun or32 (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))))
  (bvor 32 x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: check
(def-inst :add-immediate
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
         ((when (and (== rn #b1111)
                     (== s 0)))
          ;; todo: see ADR
          (update-error *unsupported* arm))
         ((when (== rn #b1101))
          ;; Special case: ADD (SP plus immediate): ;; TODO: Why is this split out?
          (if (and (== rd #b1111) ; todo: multiple cases can match?
                   (== s 1))
              (update-error *unsupported* arm)
            (b* ((d rd)
                 (setflags (== s 1)) ; todo: use == more?
                 (imm32 (ARMExpandImm imm12 arm))
                 ;; end EncodingSpecificOperations
                 ((mv result carry overflow)
                  (AddWithCarry 32 (sp arm) imm32 0)))
              (if (== d 15)
                  (update-error *unsupported* arm)
                (let* ((arm (set-reg d result arm))
                       (arm (if setflags
                                (let* ((arm (set-apsr.n (getbit 31 result) arm))
                                       (arm (set-apsr.z (IsZeroBit 32 result) arm))
                                       (arm (set-apsr.c carry arm))
                                       (arm (set-apsr.v overflow arm)))
                                  arm)
                              arm)))
                  arm)))))
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

;; todo: check
(def-inst :add-register
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
         ((when (and (== rd #b1111)
                     (== s 1)))
          (update-error *unsupported* arm) ; todo
          )
         ((when (== rn #b1101))
          (update-error *unsupported* arm) ; todo
          )
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


(def-inst :and-immediate
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
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

(def-inst :mul
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
         (d (uint 4 rd))
         (n (uint 4 rn))
         (m (uint 4 rm))
         (setflags (== s 1))
         ((when (or (== d 15)
                    (== n 15)
                    (== m 15)))
          (update-error *unpredictable* arm))
         ((when (and (< (archversion) 6)
                     (== d n)))
          (update-error *unpredictable* arm))
         ;; end EncodingSpecificOperations:
         (operand1 (sint 32 (reg n arm)))
         (operand2 (sint 32 (reg m arm)))
         (result (* operand1 operand2))
         (arm (set-reg d (bvchop 32 result) arm))
         (arm (if setflags
                  (let* ((arm (set-apsr.n (getbit 31 result) arm))
                         (arm (set-apsr.z (IsZeroBit 32 (bvchop 32 result)) arm))
                         (arm (if (== (archversion) 4)
                                  (update-error :unknown arm) ; (set-apsr.c (UNKNOWN arm) arm))
                                arm))
                         ;; V is unchanged
                         )
                    arm)
                arm)))
      arm))

(def-inst :eor-immediate
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
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

(def-inst :orr-immediate
    (b* (((when (not (ConditionPassed cond arm))) arm)
         ;; EncodingSpecificOperations:
         ((when (= cond #b1111)) (execute-unconditional-instruction arm))
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
