; Functions appearing in the pseudocode used to describe ARM instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "state")
(include-book "memory")
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/bv/bvcount" :dir :system)
(include-book "kestrel/bv/bool-to-bit" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))

(in-theory (disable mv-nth))

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *unpredictable* :unpredictable)
(defconst *unsupported* :unsupported)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See D16.5.3 (Bitstring manipulation)

;; See "Zero-extension and sign-extension of bitstrings"
;; We add the "xsize" parameter here because we can't ask x for its size.
;todo: reorder args?
(defun SignExtend (x xsize i)
  (declare (xargs :guard (and (unsigned-byte-p xsize x)
                              (< 0 xsize) ; so there is a sign bit to copy
                              (natp i)
                              (<= xsize i))))
  (bvsx i xsize x))

;; Prove the claim "If i == Len(x) ..." from the spec
(thm
  (implies (and (unsigned-byte-p xsize x)
                (equal i xsize))
           (equal (signextend x xsize i)
                  x)))

;; Prove the claim "If i > Len(x) ..." from the spec
(thm
  (implies (and (unsigned-byte-p xsize x)
                (> i xsize)
                (< 0 xsize) ; so we can get the top bit
                (natp i))
           (equal (signextend x xsize i)
                  (bvcat (- i xsize)
                         (repeatbit (- i xsize) (getbit (+ -1 xsize) x))
                         xsize
                         x)))
  :hints (("Goal" :in-theory (enable bvsx ;todo
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: could pass the old size too?
(defund ZeroExtend (x n)
  (declare (xargs :guard (and (posp n)
                              (unsigned-byte-p n x) ; could require n-1
                              )))
  (mbe :logic (bvchop n x)
       :exec x))

(defthm unsigned-byte-p-of-ZeroExtend
  (implies (natp n)
           (unsigned-byte-p n (ZeroExtend x n)))
  :hints (("Goal" :in-theory (enable ZeroExtend))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A2.2.1 (Integer arithmetic)

;; Returns (mv bits bit)
;;todo: do we want N or X first (here and elsewhere)?
(defun lsl_c (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (integerp shift)
                              ;; the assert:
                              (> shift 0))))
  (let* ((extended_x (bvcat n x shift 0))
         (result (slice (- n 1) 0 extended_x))
         (carry_out (getbit n extended_x)))
    (mv result carry_out)))

;; Returns the new bits.
(defun lsl (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (integerp shift)
                              ;; the assert:
                              (>= shift 0))))
  (b* (((mv result &)
        (if (= shift 0)
            (mv x nil) ; the nil is irrelevant
          (lsl_c n x shift))))
    result))


;; Returns (mv bits bit)
(defun lsr_c (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (integerp shift)
                              ;; the assert:
                              (> shift 0))))
  (let* ((extended_x x) ; ZeroExtend does nothing
         (result (slice (+ shift (- n 1)) shift extended_x))
         (carry_out (getbit (- shift 1) extended_x)))
    (mv result carry_out)))

;; Returns new bits
(defund lsr (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                             (integerp shift)
                              ;; the assert:
                              (>= shift 0))))
  (b* (((mv result &)
        (if (= shift 0)
            (mv x nil)
          (lsr_c n x shift))))
    result))

(defthm integerp-of-lsr
  (implies (and (unsigned-byte-p n x)
                 (integerp shift)
                 ;; the assert:
                 (>= shift 0))
            (integerp (lsr n x hift)))
  :hints (("Goal" :in-theory (enable lsr))))


;; Returns (mv bits bit)
(defun asr_c (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (< 0 n) ; so we have a sign bit
                              (integerp shift)
                              ;; the assert:
                              (> shift 0))))
  (let* ((extended_x (SignExtend x n (+ shift n)))
         (result (slice (+ shift (- n 1)) shift extended_x))
         (carry_out (getbit (- shift 1) extended_x)))
    (mv result carry_out)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Slightly more restrictive than = as this excludes complex numbers.  The spec
;; says that the comparison functions operate on integers or 'reals'.
(defun-inline == (x y) (declare (xargs :guard (and (rationalp x) (rationalp y)))) (equal x y))

(defun-inline != (x y) (declare (xargs :guard (and (rationalp x) (rationalp y)))) (not (== x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A8.3.1 (Pseudocode details of conditional execution)

;; We don't currently need the CurrentCond() function as the condition gets
;; extracted from the instruction during decoding.

(defund ConditionPassed (cond ; from the instruction
                          arm)
  (declare (xargs :guard (unsigned-byte-p 4 cond)
                  :stobjs arm))
  (let ((result (let ((cond3_1 (slice 3 1 cond)))
                  (case cond3_1
                    (#b000 (== (apsr.z arm) 1))
                    (#b001 (== (apsr.c arm) 1))
                    (#b010 (== (apsr.n arm) 1))
                    (#b011 (== (apsr.v arm) 1))
                    (#b100 (and (== (apsr.c arm) 1) (== (apsr.z arm) 0)))
                    (#b101 (== (apsr.n arm) (apsr.v arm)))
                    (#b110 (and (== (apsr.n arm) (apsr.v arm))
                                (== (apsr.z arm) 0)))
                    (#b111 t)
                    (otherwise (er hard 'ConditionPassed "Unreachable case."))))))
    (if (and (== (getbit 0 cond) 1)
             (!= cond #b1111))
        (not result)
      result)))

;; So we can call ConditionPassed before checking for a condition of #b1111.
(thm (ConditionPassed #b1111 arm) :hints (("Goal" :in-theory (enable conditionpassed))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A8.4.3 (Pseudocode details of instruction-specified shifts and rotates)

;; enumeration SRType:

;; We define these constants so we don't mistype these values:
(defconst *SRType_LSL* :SRType_LSL)
(defconst *SRType_LSR* :SRType_LSR)
(defconst *SRType_ASR* :SRType_ASR)
(defconst *SRType_ROR* :SRType_ROR)
(defconst *SRType_RRX* :SRType_RRX)

(defconst *SRTypes* (list *SRType_LSL* *SRType_LSR* *SRType_ASR* *SRType_ROR* *SRType_RRX*))

(defund SRTypep (ty)
  (declare (xargs :guard t))
  (member-eq ty *SRTypes*))

;; Returns (mv SRType integer).
(defund DecodeImmShift (type imm5)
  (declare (xargs :guard (and (unsigned-byte-p 2 type)
                              (unsigned-byte-p 5 imm5))))
  (mv-let (shift_t shift_n) ; this mv-let is not really needed, but we try to follow the spec
    (case type
      (#b00 (mv *SRType_LSL* imm5))
      (#b01 (mv *SRType_LSR* (if (== imm5 #b00000) 32 imm5)))
      (#b10 (mv *SRType_ASR* (if (== imm5 #b00000) 32 imm5)))
      (#b11 (if (= imm5 #b00000)
                (mv *SRType_RRX* 1)
              (mv *SRType_ROR* imm5)))
      (otherwise (prog2$ (er hard 'DecodeImmShift "Unreachable case")
                         (mv nil nil))))
    (mv shift_t shift_n)))

(defthm DecodeImmShift-return-type
  (implies (and (unsigned-byte-p 2 type)
                (unsigned-byte-p 5 imm5))
           (and (SRTypep (mv-nth 0 (DecodeImmShift type imm5)))
                (integerp (mv-nth 1 (DecodeImmShift type imm5)))
                (<= 0 (mv-nth 1 (DecodeImmShift type imm5)))))
  :hints (("Goal" :in-theory (enable DecodeImmShift))))

(defthm mv-nth-1-of-decodeimmshift-when-rrx
  (implies (equal (mv-nth 0 (decodeimmshift type imm5)) :srtype_rrx)
           (equal (mv-nth 1 (decodeimmshift type imm5))
                  1))
  :hints (("Goal" :in-theory (enable decodeimmshift))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defund DecodeRegShift (type)
  (declare (xargs :guard (unsigned-byte-p 2 type)))
  (let ((shift_t ; this let is not really needed, but we try to follow the spec
          (case type
            (#b00 *SRType_LSL*)
            (#b01 *SRType_LSR*)
            (#b10 *SRType_ASR*)
            (#b11 *SRType_ROR*)
            (otherwise (er hard 'DecodeRegShift "Unreachable case")))))
    shift_t))

(defthm DecodeRegShift-return-type
  (implies (unsigned-byte-p 2 type)
           (SRTypep (DecodeRegShift type)))
  :hints (("Goal" :in-theory (enable DecodeRegShift))))

(defthm not-equal-of-DecodeRegShift-and-SRTYPE_RRX
 (not (equal (DecodeRegShift type) :SRTYPE_RRX))
 :hints (("Goal" :in-theory (enable DecodeRegShift))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; D16.5.4 (Arithmetic)

;; div is RoundDown(x/y)
(defun div (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (not (equal 0 y)))))
  (floor (/ x y) 1))

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defthm div-becomes-floor
  (equal (div x y)
         (floor x y))
  :hints (("Goal" :in-theory (e/d (acl2::floor-normalize-denominator)
                                  (acl2::floor-of-*-of-/-and-1) ; todo: gen?
                                  ))))


;; For mod, we can just use the ACL2 mod.  This theorem shows that the ACL2 mod
;; satisfies the definiting equation used for mod in the spec:
(defthmd mod-correct
  (equal (mod x y)
         (- x (* y (div x y))))
  :hints (("Goal" :in-theory (enable mod))))

;; Returns (mv bits bit)
(defun ROR_C (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (< 0 n) ; todo: require this elsewhere

                              (integerp shift)
                              ;; the assert:
                              (not (equal shift 0)))))
  (let* ((m (mod shift n))
         (result (bvor n (lsr n x m) (lsl n x (- n m))))
         (carry_out (getbit (- n 1) result)))
    (mv result carry_out)))

(defun ROR (n x shift)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (< 0 n) ; todo: require this elsewhere
                              (integerp shift))))
  (if (== shift 0)
      x
    (mv-let (result bit)
        (ROR_C n x shift)
      (declare (ignore bit))
      result)))

;; Returns (mv bits bit)
(defun RRX_C (n x carry_in)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (< 0 n)
                              (bitp carry_in))))
  (let ((result (bvcat 1 carry_in (- n 1) (slice (- n 1) 1 x)))
        (carry_out (getbit 0 x)))
    (mv result carry_out)))

(defun RRX (n x carry_in)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (< 0 n)
                              (bitp carry_in))))
  (mv-let (result bit)
      (RRX_C n x carry_in)
    (declare (ignore bit))
    result))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv bits bit)
(defund shift_c (n value type amount carry_in)
  (declare (xargs :guard (and (unsigned-byte-p n value)
                              (< 0 n)
                              (SRTypep type)
                              (integerp amount) ; restrict?
                              (<= 0 amount) ; for the guard of lsl_c
                              (bitp carry_in)
                              ;; the assert:
                              (not (and (eq type :SRType_RRX)
                                        (not (equal amount 1)))))
                  :guard-hints (("Goal" :in-theory (enable srtypep)))))
  (b* (((mv result carry_out)
        (if (= amount 0)
            (mv value carry_in)
          (case type
            (:SRType_LSL (lsl_c n value amount))
            (:SRType_LSR (lsr_c n value amount))
            (:SRType_ASR (asr_c n value amount))
            (:SRType_ROR (ror_c n value amount))
            (:SRType_RRX (rrx_c n value carry_in))
            (otherwise (prog2$ (er hard 'shift_c "Unreachable case.")
                               (mv nil nil)))))))
    (mv result carry_out)))

(defthm unsigned-byte-p-of-mv-nth-0-of-shift_c
  (implies (and (unsigned-byte-p n value)
                (< 0 n)
                (SRTypep type)
                (integerp amount) ; restrict?
                (<= 0 amount) ; for the guard of lsl_c
                (bitp carry_in)
        )
           (unsigned-byte-p n (mv-nth 0 (shift_c n value type amount carry_in))))
  :hints (("Goal" :in-theory (enable shift_c srtypep))))

(defthm unsigned-byte-p-of-mv-nth-1-of-shift_c
  (implies (and (unsigned-byte-p n value)
                (< 0 n)
                (SRTypep type)
                (integerp amount)           ; restrict?
                (<= 0 amount)               ; for the guard of lsl_c
                (bitp carry_in)
)
           (unsigned-byte-p 1 (mv-nth 1 (shift_c n value type amount carry_in))))
  :hints (("Goal" :in-theory (enable shift_c srtypep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See A8.4.3 (Pseudocode details of instruction-specified shifts and rotates)
(defund shift (n value type amount carry_in)
  (declare (xargs :guard (and (unsigned-byte-p n value)
                              (< 0 n)
                              (SRTypep type)
                              (integerp amount) ; restrict?
                              (<= 0 amount) ; for the guard of lsl_c
                              ;; the assert in shift_c:
                              (not (and (eq type :SRType_RRX)
                                        (not (equal amount 1))))
                              (bitp carry_in))))
  (b* (((mv result &) (shift_c n value type amount carry_in)))
    result))

(defthm unsigned-byte-p-of-shift
  (implies (and (unsigned-byte-p n value)
                (< 0 n)
                (SRTypep type)
                (integerp amount) ; restrict?
                (<= 0 amount) ; for the guard of lsl_c
                ;; the assert in shift_c:
                (not (and (eq type :SRType_RRX)
                          (not (equal amount 1))))
                (bitp carry_in))
           (unsigned-byte-p n (shift n value type amount carry_in)))
  :hints (("Goal" :in-theory (enable shift))))

;; returns (mv result carry_out overflow)
(defund AddWithCarry (n x y carry_in)
  (declare (xargs :guard (and (unsigned-byte-p n x)
                              (unsigned-byte-p n y)
                              (posp n) ; so there is a sign bit
                              (bitp carry_in))))
  (let* ((unsigned_sum (+ x y carry_in))
         (signed_sum (+ (logext n x)
                        (logext n y)
                        carry_in))
         (result (slice (- n 1) 0 unsigned_sum))
         (carry_out (if (== result unsigned_sum) 0 1))
         (overflow (if (== (logext n result) signed_sum) 0 1)))
    (mv result carry_out overflow)))

;; todo: other rvs
(defthm mv-nth-0-of-AddWithCarry
  (implies (and (posp n)
                (integerp x)
                (integerp y)
                (integerp carry_in))
           (equal (mv-nth 0 (AddWithCarry n x y carry_in))
                  (bvplus n x (bvplus n y carry_in))))
  :hints (("Goal" :in-theory (enable AddWithCarry bvplus))))

(defthm unsigned-byte-p-of-mv-nth-0-of-AddWithCarry
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (posp n) ; so there is a sign bit
                (bitp carry_in))
           (unsigned-byte-p n (mv-nth 0 (AddWithCarry n x y carry_in))))
  :hints (("Goal" :in-theory (enable AddWithCarry))))

(defthm unsigned-byte-p-of-mv-nth-1-of-AddWithCarry
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (posp n) ; so there is a sign bit
                (bitp carry_in))
           (unsigned-byte-p 1 (mv-nth 1 (AddWithCarry n x y carry_in))))
  :hints (("Goal" :in-theory (enable AddWithCarry))))

(defthm unsigned-byte-p-of-mv-nth-2-of-AddWithCarry
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (posp n) ; so there is a sign bit
                (bitp carry_in))
           (unsigned-byte-p 1 (mv-nth 2 (AddWithCarry n x y carry_in))))
  :hints (("Goal" :in-theory (enable AddWithCarry))))

(defund BitCount (n x)
  (declare (xargs :guard (unsigned-byte-p n x)))
  (bvcount n x))

(defun IsZero (n x)
  (declare (xargs :guard (unsigned-byte-p n x))
           (ignore n))
  (equal 0 x) ; todo: phrase using bitcount
  )

(defund IsZeroBit (n x)
  (declare (xargs :guard (unsigned-byte-p n x)))
  (if (IsZero n x) 1 0))

;; can avoid a case split
(defthm IsZeroBit-alt-def
  (equal (IsZeroBit n x)
         (bool-to-bit (equal x 0)))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable IsZeroBit))))

;; (local
;;   (defthm integerp-when-unsigned-byte-p-32
;;     (implies (unsigned-byte-p 32 x)
;;              (integerp x))))

(defund ARMExpandImm_C (imm12 carry_in)
  (declare (xargs :guard (and (unsigned-byte-p 12 imm12)
                              (bitp carry_in))))
  (b* ((unrotated_value (slice 7 0 imm12))
       ((mv imm32 carry_out) (Shift_C 32 unrotated_value :SRType_ROR (* 2 (slice 11 8 imm12)) carry_in)))
    (mv imm32 carry_out)))

(defthm unsigned-byte-p-32-of-mv-nth-0-of-armexpandimm_c
  (implies (bitp carry_in)
           (unsigned-byte-p 32 (mv-nth 0 (armexpandimm_c imm12 carry_in))))
  :hints (("Goal" :in-theory (enable armexpandimm_c))))

(defthm unsigned-byte-p-1-of-mv-nth-1-of-armexpandimm_c
  (implies (bitp carry_in)
           (unsigned-byte-p 1 (mv-nth 1 (armexpandimm_c imm12 carry_in))))
  :hints (("Goal" :in-theory (enable armexpandimm_c))))

;; the arm arg is irrelevant?
(defun ARMExpandImm (imm12 arm)
  (declare (xargs :guard (unsigned-byte-p 12 imm12)
                  :stobjs arm))
  (b* (((mv imm32 & ;carry_out
            )
        (ARMExpandImm_C imm12 (apsr.c arm))))
    imm32))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A2.5.1 (Instruction set state register, ISETSTATE)

(defconst *InstrSet_ARM* #b00)
(defconst *InstrSet_Thumb* #b01)
(defconst *InstrSet_Jazelle* #b10)
(defconst *InstrSet_ThumbEE* #b11)

(defund CurrentInstrSet (arm)
  (declare (xargs :stobjs arm))
  (isetstate arm))

(defthm natp-of-CurrentInstrSet-type
  (implies (armp arm)
           (natp (CurrentInstrSet arm)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable CurrentInstrSet armp isetstate isetstatep))))

(defund SelectInstrSet (iset arm)
  (declare (xargs :guard (member iset (list *InstrSet_ARM*
                                            *InstrSet_Thumb*
                                            *InstrSet_Jazelle*
                                            *InstrSet_ThumbEE*))
                  :stobjs arm))
  (if (== iset *InstrSet_ARM*)
      (if (== (CurrentInstrSet arm) *InstrSet_ThumbEE*)
          (update-error *unpredictable* arm)
        (update-isetstate *InstrSet_ARM* arm))
    (update-isetstate iset arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund archversion ()
  (declare (xargs :guard t))
  5 ; todo
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A2.3.2 (Pseudocode details of operations on ARM core registers)

;; Returns arm.
;; todo: compare this to what the manual has
(defun BranchTo (address arm)
  (declare (xargs :guard (unsigned-byte-p 32 address)
                  :stobjs arm))
  ;; todo: do we need to deal with the 8-byte offset?:
  (set-reg *pc* address arm))

;; A2.3.2 (Pseudocode details of operations on ARM core registers)

;; Returns arm.
(defun BranchWritePC (address arm)
  (declare (xargs :guard (unsigned-byte-p 32 address) ; or call addressp
                  :stobjs arm))
  (if (== (CurrentInstrSet arm) *InstrSet_ARM*)
      (if (and (< (ArchVersion) 6)
               (!= (slice 1 0 address) #b00))
          (update-error *unpredictable* arm)
        (BranchTo (bvcat 30 (slice 31 2 address) 2 #b00) arm))
    (if (== (CurrentInstrSet arm) *InstrSet_Jazelle*)
        (update-error *unsupported* arm) ; todo
      (BranchTo (bvcat 31 (slice 31 1 address) 1 #b0) arm))))

;; Returns arm.
(defun BXWritePC (address arm)
  (declare (xargs :guard (unsigned-byte-p 32 address)
                  :stobjs arm))
  (if (== (CurrentInstrSet arm) *InstrSet_ThumbEE*)
      (update-error :unsupported arm) ; todo
    (if (== (getbit 0 address) 1)
        (update-error :unsupported arm) ; todo: use the name "set-error"
      (if (== (getbit 1 address) 0)
          ;; todo: change the ARM instr set
          (BranchTo address arm)
        (update-error :unpredictable arm)))))

;; Returns arm.
(defun ALUWritePC (address arm)
  (declare (xargs :guard (addressp address)
                  :stobjs arm))
  (if (and (>= (ArchVersion) 7)
           (== (CurrentInstrSet arm) *InstrSet_ARM*))
      (BXWritePC address arm)
    (BranchWritePC address arm)))

;; Returns arm.
(defun LoadWritePC (address arm)
  (declare (xargs :guard (addressp address)
                  :stobjs arm))
  (if (>= (ArchVersion) 5)
      (BXWritePC address arm)
    (BranchWritePC address arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This represents a normal increment of the PC by 4 to advance to the next
;; instruction.
;; TODO: Do we need to do any of the checking that BranchWritePC or ALUWritePC does?
(defund advance-pc (arm)
  (declare (xargs :stobjs arm))
  (let ((arm (set-reg *pc* (add-to-address 4 (reg *pc* arm)) arm)))
    arm))

(defthm armp-of-advance-pc
  (implies (armp arm)
           (armp (advance-pc arm)))
  :hints (("Goal" :in-theory (enable advance-pc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sint (n x)
  (declare (xargs :guard (and (posp n)
                              (unsigned-byte-p n x))))
  (logext n x))

;; for us, a bitstring is already an unsigned integer, but we chop to make an
;; unconditional return type.
(defund uint (n x)
  (declare (xargs :guard (and (posp n)
                              (unsigned-byte-p n x))))
  (bvchop n x))

(defthm uint-bound-linear
  (implies (natp n)
           (<= (uint n x) (+ -1 (expt 2 n))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable uint))))

(defund int (n x unsigned)
  (declare (xargs :guard (and (posp n)
                              (unsigned-byte-p n x)
                              (booleanp unsigned))))
  (if unsigned (uint n x) (sint n x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See "Rounding and aligning" in D16.5.4 Arithmetic
(defund align (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (not (equal 0 y)))))
  (* y (div x y)))

;; todo
;; (thm
;;  (equal (align x 4)
;;         (bvand 32 #xfffffffc x))
;;  :hints (("Goal" :in-theory (enable align bvand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: think about this
;; Val should contain enough informaion to distinguish different unknown bits (e.g., opcode, flag, etc.)
(encapsulate (((unknown-bits * * arm) => *))
    (local (defun unknown-bits (n val arm)
             (declare (xargs :guard (posp n) :stobjs arm)
                      (ignore n val arm))
             0))
  (defthm unsigned-byte-p-of-unknown-bits
    (equal (unsigned-byte-p n (unknown-bits n val arm))
           (natp n))))

(defund unknown-bit (val arm)
  (declare (xargs :stobjs arm))
  (unknown-bits 1 val arm))

(defthm bitp-of-unknown-bits
  (bitp (unknown-bit val arm))
  :hints (("Goal" :in-theory (enable unknown-bit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun UnalignedSupport ()
  (declare (xargs :guard t))
  t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: How should we handle this?
(defun HaveLPAE ()
  (declare (xargs :guard t))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun BigEndian ()
  (declare (xargs :guard t))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
;; See A4.2.2 (Use of labels in UAL instruction syntax)
;; todo: add a case for Thumb
(defun pcvalue (inst-address)
  (declare (xargs :guard (addressp inst-address)))
  (+ 8 inst-address) ; todo: wrap?
  )

;; TODO: Can return PC+4 on versions before ARMv7?
(defund PCStoreValue (inst-address)
  (declare (xargs :guard (addressp inst-address)))
  (bvplus 32 8 inst-address))

(defthm unsigned-byte-p-of-PCStoreValue
  (unsigned-byte-p 32 (PCStoreValue inst-address))
  :hints (("Goal" :in-theory (enable PCStoreValue))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun Zeros (n)
  (declare (xargs :guard (posp n))
           (ignore n))
  0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun LowestSetBit-aux (n size x)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p size x)
                              (<= n (+ 1 size)))
                  :measure (nfix (+ 1 (- size n)))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp size)))
          (<= size n))
      size
    (if (= 1 (getbit n x))
        n
      (LowestSetBit-aux (+ 1 n) size x))))

(defund LowestSetBit (size x)
  (declare (xargs :guard (unsigned-byte-p size x)))
  (LowestSetBit-aux 0 size x))

;; (assert-equal (LowestSetBit 32 1) 0)
;; (assert-equal (LowestSetBit 32 8) 3)
;; (assert-equal (LowestSetBit 32 0) 32)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *true* t)
(defconst *false* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: flesh out
;; Returns arm.
(defun NullCheckIfThumbEE (n arm)
  (declare (xargs :guard (register-numberp n)
                  :stobjs arm)
           (ignore n))
  arm ; for now, since we don't yet support Thumb
  )
