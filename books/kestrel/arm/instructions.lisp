; A formal model of ARM32: the instructions
;
; Copyright (C) 2025 Kestrel Institute
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
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))

(in-theory (disable mv-nth))

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst :add-immediate
    (if (not (ConditionPassed cond arm))
        arm
      ;; Encoding-specific operations:
      (cond ((= cond #b1111) (update-error :unsupported arm))
            ((and (== rn #b1111)
                  (== s 0))
             ;; todo: see ADR
             (update-error :unsupported arm))
            ((== rn #b1101)
             ;; Special case: ADD (SP plus immediate): ;; TODO: Why is this split out?
             (if (and (== rd #b1111) ; todo: multiple cases can match?
                      (== s 1))
                 (update-error :unsupported arm)
               (b* ((d rd)
                    (setflags (== s 1)) ; todo: use == more?
                    (imm32 (ARMExpandImm imm12 arm))
                    ;; end EncodingSpecificOperations
                    ((mv result carry overflow)
                     (AddWithCarry 32 (sp arm) imm32 0)))
                 (if (== d 15)
                     (update-error :unsupported arm)
                   (let* ((arm (set-reg d result arm))
                          (arm (if setflags
                                   (let* ((arm (set-apsr.n (getbit 31 result) arm))
                                          (arm (set-apsr.z (IsZeroBit 32 result) arm))
                                          (arm (set-apsr.c carry arm))
                                          (arm (set-apsr.v overflow arm)))
                                     arm)
                                 arm)))
                     arm)))))
            ((and (== rd #b1111) ; todo: multiple cases can match?
                  (== s 1))
             (update-error :unsupported arm))
            ;; Normal case:
            (t (b* ((d rd)
                    (n rn)
                    (setflags (== s 1))
                    (imm32 (ARMExpandImm imm12 arm))
                    ;; end EncodingSpecificOperations
                    ((mv result carry overflow)
                     (AddWithCarry 32 (reg n arm) imm32 0)))
                 (if (== d 15)
                     (update-error :unsupported arm)
                   (let* ((arm (set-reg d result arm))
                          (arm (if setflags
                                   (let* ((arm (set-apsr.n (getbit 31 result) arm))
                                          (arm (set-apsr.z (IsZeroBit 32 result) arm))
                                          (arm (set-apsr.c carry arm))
                                          (arm (set-apsr.v overflow arm)))
                                     arm)
                                 arm)))
                     arm)))))))

(def-inst :add-register
    (if (not (ConditionPassed cond arm))
        arm
      ;; Encoding-specific operations:
      (cond
        ((and (== rd #b1111)
              (== s 1))
         (update-error :unsupported arm))
        ((== rn #b1101)
         (update-error :unsupported arm))
        (t (b* ((d rd)
                (n rn)
                (m rm)
                (setflags (== s 1))
                ((mv shift_t shift_n) (decodeImmShift type imm5))
                ;; end Encoding-specific operations
                (shifted (shift 32 (reg m arm) shift_t shift_n (apsr.c arm)))
                ((mv result carry overflow) (AddWithCarry 32 (reg n arm) shifted 0)))
             (if (== d 15)
                 (update-error :unsupported arm)
               (let* ((arm (set-reg d result arm))
                      (arm (if setflags
                               (let* ((arm (set-apsr.n (getbit 31 result) arm))
                                      (arm (set-apsr.z (IsZeroBit 32 result) arm))
                                      (arm (set-apsr.c carry arm))
                                      (arm (set-apsr.v overflow arm)))
                                 arm)
                             arm)))
                 arm)))))))
