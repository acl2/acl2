; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "values")

(include-book "ihs/basic-definitions" :dir :system)

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shift-operations
  :parents (dynamic-semantics)
  :short "Leo shift operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are arithmetic shift left and shift right operations,
     in regular and wrapped variants.")
   (xdoc::p
    "The left operand can be any signed or unsigned integer type;
     the right operand can only be @('u8'), @('u16'), or @('u32').
     The return type is the same as the left operand type.")
   (xdoc::p
    "For the regular shift left and shift right operations,
     it is an error if the right operand is larger than the number of bits
     of the left operand's type.")
   (xdoc::p
    "For the wrapped shift left and shift right operations,
     instead of getting an error when the right operand is too large,
     only the low @($log_2(N)$) bits are used when deciding how far to shift,
     where @('N') is the bit size of the left operand's type.  In other words,
     the shift amount is first reduced modulo @('N').")
   (xdoc::p
    "Arithmetic shift is best thought of as multiplication (left shift)
     or division (right shift) by a power of two.  The right operand is the
     power of two.  In the case of division, fractions are rounded towards
     negative infinity.")
   (xdoc::p
    "For example @('-3i8 >> 1u8') becomes @('-3/2') which is rounded to
     @('-2i8').")
   (xdoc::p
    "For regular left shift, if the result of multiplying by the power of two
     is not representable in the return type, it is an error.
     For example, @('64i8 << 1u8') and @('-65i8 << 1u8') are errors.")
   (xdoc::p
    "For wrapped left shift, if the result of multiplying by the power of two
     is not representable in the return type, then the low @('N') bits
     are interpreted as a value of the return type.  For example,
     consider @('127i8.shl_wrapped(2u8)').  The bits @('0111 1111') are shifted left
     by two places: @('1 1111 1100'); the low 8 bits are @('1111 1100'),
     which represents the returned value @('-4i8')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-shl ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo left shift operation."
  (b* ((err (list :op-shl (value-fix left) (value-fix right)))
       ;; It is currently an error to call op-shl on values of
       ;; types other than signed and unsigned integers.
       ((unless (int-valuep left))
        (reserrf err))
       ((unless (int-valuep right))
        (reserrf err))
       (left-operand-numbits (int-value-numbits left))
       (left-operand-int (int-value-to-int left))
       ;; int-valuep already restricts the type of 'right', but
       ;; dynamically check the more restrictive condition here
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        (reserrf err))
       (right-operand-int (int-value-to-int right))
       ;; The previous check on value-kind should have ensured
       ;; the right operand value is nonnegative, but we
       ;; make that more clear here.
       ((unless (natp right-operand-int))
        (reserrf err))
       ;; First documented restriction.
       ((when (<= left-operand-numbits right-operand-int))
        (reserrf err))
       (shifted-value (* left-operand-int (expt 2 right-operand-int))))
    ;; make-int-value will return an error if shifted-value doesn't fit
    ;; in the type of the left operand.
    (make-int-value (value-kind left) shifted-value))
  :guard-hints (("Goal" :in-theory (enable int-valuep))))

(define op-shr ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo right shift operation."
  (b* ((err (list :op-shr (value-fix left) (value-fix right)))
       ;; It is currently an error to call op-shl on values of
       ;; types other than signed and unsigned integers.
       ((unless (int-valuep left))
        (reserrf err))
       ((unless (int-valuep right))
        (reserrf err))
       (left-operand-numbits (int-value-numbits left))
       (left-operand-int (int-value-to-int left))
       ;; int-valuep already restricts the type of 'right', but
       ;; dynamically check the more restrictive condition here
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        (reserrf err))
       (right-operand-int (int-value-to-int right))
       ;; The previous check on value-kind should have ensured
       ;; the right operand value is nonnegative, but we
       ;; make that more clear here.
       ((unless (natp right-operand-int))
        (reserrf err))
       ;; First documented restriction.
       ((when (<= left-operand-numbits right-operand-int))
        (reserrf err))
       (shifted-value (floor left-operand-int (expt 2 right-operand-int))))
    (make-int-value (value-kind left) shifted-value))
  :guard-hints (("Goal" :in-theory (enable int-valuep))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Wrapped versions of shift operations.

(define op-shl-wrapped ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo wrapped left shift operation."
  (b* ((err (list :op-shl-wrapped (value-fix left) (value-fix right)))
       ;; It is currently an error to call op-shl on values of
       ;; types other than signed and unsigned integers.
       ((unless (int-valuep left))
        (reserrf err))
       ((unless (int-valuep right))
        (reserrf err))
       (left-operand-numbits (int-value-numbits left))
       (left-operand-int (int-value-to-int left))
       ;; int-valuep already restricts the type of 'right', but
       ;; dynamically check the more restrictive condition here
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        (reserrf err))
       (right-operand-int (int-value-to-int right))
       ;; The previous check on value-kind should have ensured
       ;; the right operand value is nonnegative, but we
       ;; make that more clear here.
       ((unless (natp right-operand-int))
        (reserrf err))
       ;; The right operand is reduced mod the number of bits
       ;; of the type of the left operand
       (right-operand-int (mod right-operand-int left-operand-numbits))
       (shifted-value (* left-operand-int (expt 2 right-operand-int))))
    (cond ((value-case left :u8)
           (value-u8 (loghead 8 shifted-value)))
          ((value-case left :u16)
           (value-u16 (loghead 16 shifted-value)))
          ((value-case left :u32)
           (value-u32 (loghead 32 shifted-value)))
          ((value-case left :u64)
           (value-u64 (loghead 64 shifted-value)))
          ((value-case left :u128)
           (value-u128 (loghead 128 shifted-value)))
          ;; signed
          ((value-case left :i8)
           (value-i8 (logext 8 shifted-value)))
          ((value-case left :i16)
           (value-i16 (logext 16 shifted-value)))
          ((value-case left :i32)
           (value-i32 (logext 32 shifted-value)))
          ((value-case left :i64)
           (value-i64 (logext 64 shifted-value)))
          ((value-case left :i128)
           (value-i128 (logext 128 shifted-value)))
          (t (reserrf err)))) ; impossible
  :guard-hints (("Goal" :in-theory (e/d (int-valuep int-value-numbits
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext)))))

(define op-shr-wrapped ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo wrapped right shift operation."
  (b* ((err (list :op-shr-wrapped (value-fix left) (value-fix right)))
       ;; It is currently an error to call op-shl on values of
       ;; types other than signed and unsigned integers.
       ((unless (int-valuep left))
        (reserrf err))
       ((unless (int-valuep right))
        (reserrf err))
       (left-operand-numbits (int-value-numbits left))
       (left-operand-int (int-value-to-int left))
       ;; int-valuep already restricts the type of 'right', but
       ;; dynamically check the more restrictive condition here
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        (reserrf err))
       (right-operand-int (int-value-to-int right))
       ;; The previous check on value-kind should have ensured
       ;; the right operand value is nonnegative, but we
       ;; make that more clear here.
       ((unless (natp right-operand-int))
        (reserrf err))
       ;; The right operand is reduced mod the number of bits
       ;; of the type of the left operand
       (right-operand-int (mod right-operand-int left-operand-numbits))
       (shifted-value (floor left-operand-int (expt 2 right-operand-int))))
    (make-int-value (value-kind left) shifted-value))
  :guard-hints (("Goal" :in-theory (enable int-valuep int-value-numbits))))
