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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-arithmetic-operations
  :parents (arithmetic-operations)
  :short "Leo integer arithmetic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are negation (unary), absolute value and wrapped absolute value (unary),
     addition, subtraction, multiplication, division, remainder, and exponentiation,
     and wrapped versions of those six (all binary ops).
     The result has always the same type as the first operand.")
   (xdoc::p
    "The binary operations are currently only allowed
     on integers of the same type (there are no automatic conversions),
     except that any signed or unsigned integer value
     may be raised to the power of any unsigned integer value.
     The result type is always the common type,
     or the type of the base (i.e. first operand) for exponentiation.")
   (xdoc::p
    "Except for the @('-wrapped') versions of operations,
     if the exact mathematical result is not representable in the result type,
     it is considered an error in the same way as division by zero.
     We defensively return an error indication when these events happen.")
   (xdoc::p
    "For the @('-wrapped') versions of operations,
     if the exact mathematical result is not representable in the result type,
     then the return value is computed from the mathematical result by taking
     the low @('N') bits if positive, or if negative by forming the sign-extended
     two's complement bit pattern and taking the low @('N') bits of that.
     In either case, the resulting bitvector is then interpreted as an integer
     of the result type.")
   (xdoc::p
    "For example @('127i8.add_wrapped(127i8)') becomes @('254'), which has the
     bit pattern @('1111 1110'), which represents the returned value @('-2i8').")
   (xdoc::p
    "for another example, @('-128i8.add_wrapped(-2i8)') becomes @('-130'), which
     in two's complement requires 9 bits: @('1 0111 1110').
     The low 8 bits are @('0111 1110'), which represents the returned value @('126i8')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-neg ((arg int-valuep))
  :returns (result value-resultp)
  :short "Leo integer negation operation."
  (b* ((err (reserrf (list :op-int-neg (value-fix arg)))))
    (case (value-kind arg)
      (:i8 (b* ((res (- (value-i8->get arg))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
      (:i16 (b* ((res (- (value-i16->get arg))))
              (if (sbyte16p res)
                  (value-i16 res)
                err)))
      (:i32 (b* ((res (- (value-i32->get arg))))
              (if (sbyte32p res)
                  (value-i32 res)
                err)))
      (:i64 (b* ((res (- (value-i64->get arg))))
              (if (sbyte64p res)
                  (value-i64 res)
                err)))
      (:i128 (b* ((res (- (value-i128->get arg))))
               (if (sbyte128p res)
                   (value-i128 res)
                 err)))
      (t err)))
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-neg
    :args ((arg valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-abs ((arg int-valuep))
  :returns (result value-resultp)
  :short "Leo integer absolute value operation."
  (b* ((err (reserrf (list :op-int-abs (value-fix arg)))))
    (case (value-kind arg)
      (:i8 (b* ((res (abs (value-i8->get arg))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
      (:i16 (b* ((res (abs (value-i16->get arg))))
              (if (sbyte16p res)
                  (value-i16 res)
                err)))
      (:i32 (b* ((res (abs (value-i32->get arg))))
              (if (sbyte32p res)
                  (value-i32 res)
                err)))
      (:i64 (b* ((res (abs (value-i64->get arg))))
              (if (sbyte64p res)
                  (value-i64 res)
                err)))
      (:i128 (b* ((res (abs (value-i128->get arg))))
               (if (sbyte128p res)
                   (value-i128 res)
                 err)))
      (t err)))
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-abs
    :args ((arg valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-abs-wrapped ((arg int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped absolute value operation."
  (b* ((err (reserrf (list :op-int-abs (value-fix arg)))))
    (case (value-kind arg)
      (:i8 (b* ((argint (value-i8->get arg))
                ((when (= argint *most-negative-i8*))
                 (value-i8 argint))
                (res (abs argint)))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
      (:i16 (b* ((argint (value-i16->get arg))
                ((when (= argint *most-negative-i16*))
                 (value-i16 argint))
                (res (abs argint)))
             (if (sbyte16p res)
                 (value-i16 res)
               err)))
      (:i32 (b* ((argint (value-i32->get arg))
                ((when (= argint *most-negative-i32*))
                 (value-i32 argint))
                (res (abs argint)))
             (if (sbyte32p res)
                 (value-i32 res)
               err)))
      (:i64 (b* ((argint (value-i64->get arg))
                ((when (= argint *most-negative-i64*))
                 (value-i64 argint))
                (res (abs argint)))
             (if (sbyte64p res)
                 (value-i64 res)
               err)))
      (:i128 (b* ((argint (value-i128->get arg))
                ((when (= argint *most-negative-i128*))
                 (value-i128 argint))
                (res (abs argint)))
             (if (sbyte128p res)
                 (value-i128 res)
               err)))
      (t err)))
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-abs-wrapped
    :args ((arg valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-add ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer addition operation."
  (b* ((err (reserrf (list :op-int-add (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (+ (value-u8->get left) (value-u8->get right))))
             (if (ubyte8p res)
                 (value-u8 res)
               err)))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (+ (value-u16->get left) (value-u16->get right))))
             (if (ubyte16p res)
                 (value-u16 res)
               err)))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (+ (value-u32->get left) (value-u32->get right))))
             (if (ubyte32p res)
                 (value-u32 res)
               err)))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (+ (value-u64->get left) (value-u64->get right))))
             (if (ubyte64p res)
                 (value-u64 res)
               err)))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (+ (value-u128->get left) (value-u128->get right))))
             (if (ubyte128p res)
                 (value-u128 res)
               err)))
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (+ (value-i8->get left) (value-i8->get right))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (+ (value-i16->get left) (value-i16->get right))))
             (if (sbyte16p res)
                 (value-i16 res)
               err)))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (+ (value-i32->get left) (value-i32->get right))))
             (if (sbyte32p res)
                 (value-i32 res)
               err)))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (+ (value-i64->get left) (value-i64->get right))))
             (if (sbyte64p res)
                 (value-i64 res)
               err)))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (+ (value-i128->get left) (value-i128->get right))))
             (if (sbyte128p res)
                 (value-i128 res)
               err)))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-add
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-add-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped addition operation."
  (b* ((err (reserrf (list :op-int-add-wrapped (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (+ (value-u8->get left) (value-u8->get right))))
             (value-u8 (loghead 8 res))))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (+ (value-u16->get left) (value-u16->get right))))
             (value-u16 (loghead 16 res))))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (+ (value-u32->get left) (value-u32->get right))))
             (value-u32 (loghead 32 res))))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (+ (value-u64->get left) (value-u64->get right))))
             (value-u64 (loghead 64 res))))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (+ (value-u128->get left) (value-u128->get right))))
             (value-u128 (loghead 128 res))))
          ;; signed
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (+ (value-i8->get left) (value-i8->get right))))
             (value-i8 (logext 8 res))))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (+ (value-i16->get left) (value-i16->get right))))
             (value-i16 (logext 16 res))))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (+ (value-i32->get left) (value-i32->get right))))
             (value-i32 (logext 32 res))))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (+ (value-i64->get left) (value-i64->get right))))
             (value-i64 (logext 64 res))))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (+ (value-i128->get left) (value-i128->get right))))
             (value-i128 (logext 128 res))))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (e/d (int-valuep
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext))))
  ///
  (fty::deffixequiv op-int-add-wrapped
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-sub ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer subtraction operation."
  (b* ((err (reserrf (list :op-int-sub (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (- (value-u8->get left) (value-u8->get right))))
             (if (ubyte8p res)
                 (value-u8 res)
               err)))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (- (value-u16->get left) (value-u16->get right))))
             (if (ubyte16p res)
                 (value-u16 res)
               err)))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (- (value-u32->get left) (value-u32->get right))))
             (if (ubyte32p res)
                 (value-u32 res)
               err)))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (- (value-u64->get left) (value-u64->get right))))
             (if (ubyte64p res)
                 (value-u64 res)
               err)))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (- (value-u128->get left) (value-u128->get right))))
             (if (ubyte128p res)
                 (value-u128 res)
               err)))
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (- (value-i8->get left) (value-i8->get right))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (- (value-i16->get left) (value-i16->get right))))
             (if (sbyte16p res)
                 (value-i16 res)
               err)))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (- (value-i32->get left) (value-i32->get right))))
             (if (sbyte32p res)
                 (value-i32 res)
               err)))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (- (value-i64->get left) (value-i64->get right))))
             (if (sbyte64p res)
                 (value-i64 res)
               err)))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (- (value-i128->get left) (value-i128->get right))))
             (if (sbyte128p res)
                 (value-i128 res)
               err)))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-sub
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-sub-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped subtraction operation."
  (b* ((err (reserrf (list :op-int-sub-wrapped (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (- (value-u8->get left) (value-u8->get right))))
             (value-u8 (loghead 8 res))))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (- (value-u16->get left) (value-u16->get right))))
             (value-u16 (loghead 16 res))))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (- (value-u32->get left) (value-u32->get right))))
             (value-u32 (loghead 32 res))))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (- (value-u64->get left) (value-u64->get right))))
             (value-u64 (loghead 64 res))))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (- (value-u128->get left) (value-u128->get right))))
             (value-u128 (loghead 128 res))))
          ;; signed
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (- (value-i8->get left) (value-i8->get right))))
             (value-i8 (logext 8 res))))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (- (value-i16->get left) (value-i16->get right))))
             (value-i16 (logext 16 res))))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (- (value-i32->get left) (value-i32->get right))))
             (value-i32 (logext 32 res))))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (- (value-i64->get left) (value-i64->get right))))
             (value-i64 (logext 64 res))))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (- (value-i128->get left) (value-i128->get right))))
             (value-i128 (logext 128 res))))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (e/d (int-valuep
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext))))
  ///
  (fty::deffixequiv op-int-sub-wrapped
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-mul ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer multiplication operation."
  (b* ((err (reserrf (list :op-mul-mul (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (* (value-u8->get left) (value-u8->get right))))
             (if (ubyte8p res)
                 (value-u8 res)
               err)))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (* (value-u16->get left) (value-u16->get right))))
             (if (ubyte16p res)
                 (value-u16 res)
               err)))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (* (value-u32->get left) (value-u32->get right))))
             (if (ubyte32p res)
                 (value-u32 res)
               err)))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (* (value-u64->get left) (value-u64->get right))))
             (if (ubyte64p res)
                 (value-u64 res)
               err)))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (* (value-u128->get left) (value-u128->get right))))
             (if (ubyte128p res)
                 (value-u128 res)
               err)))
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (* (value-i8->get left) (value-i8->get right))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (* (value-i16->get left) (value-i16->get right))))
             (if (sbyte16p res)
                 (value-i16 res)
               err)))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (* (value-i32->get left) (value-i32->get right))))
             (if (sbyte32p res)
                 (value-i32 res)
               err)))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (* (value-i64->get left) (value-i64->get right))))
             (if (sbyte64p res)
                 (value-i64 res)
               err)))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (* (value-i128->get left) (value-i128->get right))))
             (if (sbyte128p res)
                 (value-i128 res)
               err)))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-mul
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-mul-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped multiplication operation."
  (b* ((err (reserrf (list :op-int-mul-wrapped (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* ((res (* (value-u8->get left) (value-u8->get right))))
             (value-u8 (loghead 8 res))))
          ((and (value-case left :u16) (value-case right :u16))
           (b* ((res (* (value-u16->get left) (value-u16->get right))))
             (value-u16 (loghead 16 res))))
          ((and (value-case left :u32) (value-case right :u32))
           (b* ((res (* (value-u32->get left) (value-u32->get right))))
             (value-u32 (loghead 32 res))))
          ((and (value-case left :u64) (value-case right :u64))
           (b* ((res (* (value-u64->get left) (value-u64->get right))))
             (value-u64 (loghead 64 res))))
          ((and (value-case left :u128) (value-case right :u128))
           (b* ((res (* (value-u128->get left) (value-u128->get right))))
             (value-u128 (loghead 128 res))))
          ;; signed
          ((and (value-case left :i8) (value-case right :i8))
           (b* ((res (* (value-i8->get left) (value-i8->get right))))
             (value-i8 (logext 8 res))))
          ((and (value-case left :i16) (value-case right :i16))
           (b* ((res (* (value-i16->get left) (value-i16->get right))))
             (value-i16 (logext 16 res))))
          ((and (value-case left :i32) (value-case right :i32))
           (b* ((res (* (value-i32->get left) (value-i32->get right))))
             (value-i32 (logext 32 res))))
          ((and (value-case left :i64) (value-case right :i64))
           (b* ((res (* (value-i64->get left) (value-i64->get right))))
             (value-i64 (logext 64 res))))
          ((and (value-case left :i128) (value-case right :i128))
           (b* ((res (* (value-i128->get left) (value-i128->get right))))
             (value-i128 (logext 128 res))))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (e/d (int-valuep
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext))))
  ///
  (fty::deffixequiv op-int-mul-wrapped
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-div ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer division operation."
  (b* ((err (reserrf (list :op-int-div (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* (((when (= (value-u8->get right) 0))
                 err)
                (res (truncate (value-u8->get left) (value-u8->get right))))
             (if (ubyte8p res)
                 (value-u8 res)
               err)))
          ((and (value-case left :u16) (value-case right :u16))
           (b* (((when (= (value-u16->get right) 0))
                 err)
                (res (truncate (value-u16->get left) (value-u16->get right))))
             (if (ubyte16p res)
                 (value-u16 res)
               err)))
          ((and (value-case left :u32) (value-case right :u32))
           (b* (((when (= (value-u32->get right) 0))
                 err)
                (res (truncate (value-u32->get left) (value-u32->get right))))
             (if (ubyte32p res)
                 (value-u32 res)
               err)))
          ((and (value-case left :u64) (value-case right :u64))
           (b* (((when (= (value-u64->get right) 0))
                 err)
                (res (truncate (value-u64->get left) (value-u64->get right))))
             (if (ubyte64p res)
                 (value-u64 res)
               err)))
          ((and (value-case left :u128) (value-case right :u128))
           (b* (((when (= (value-u128->get right) 0))
                 err)
                (res (truncate (value-u128->get left) (value-u128->get right))))
             (if (ubyte128p res)
                 (value-u128 res)
               err)))
          ((and (value-case left :i8) (value-case right :i8))
           (b* (((when (= (value-i8->get right) 0))
                 err)
                (res (truncate (value-i8->get left) (value-i8->get right))))
             (if (sbyte8p res)
                 (value-i8 res)
               err)))
          ((and (value-case left :i16) (value-case right :i16))
           (b* (((when (= (value-i16->get right) 0))
                 err)
                (res (truncate (value-i16->get left) (value-i16->get right))))
             (if (sbyte16p res)
                 (value-i16 res)
               err)))
          ((and (value-case left :i32) (value-case right :i32))
           (b* (((when (= (value-i32->get right) 0))
                 err)
                (res (truncate (value-i32->get left) (value-i32->get right))))
             (if (sbyte32p res)
                 (value-i32 res)
               err)))
          ((and (value-case left :i64) (value-case right :i64))
           (b* (((when (= (value-i64->get right) 0))
                 err)
                (res (truncate (value-i64->get left) (value-i64->get right))))
             (if (sbyte64p res)
                 (value-i64 res)
               err)))
          ((and (value-case left :i128) (value-case right :i128))
           (b* (((when (= (value-i128->get right) 0))
                 err)
                (res (truncate (value-i128->get left) (value-i128->get right))))
             (if (sbyte128p res)
                 (value-i128 res)
               err)))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (enable int-valuep)))
  ///
  (fty::deffixequiv op-int-div
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-div-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped division operation."
  (b* ((err (reserrf (list :op-int-div-wrapped (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* (((when (= (value-u8->get right) 0))
                 err)
                (res (truncate (value-u8->get left) (value-u8->get right))))
             ;; Strictly speaking we don't need this loghead on the unsigned ints
             ;; because there is no danger of overflow in execution, I believe.
             ;; It is here for consistency with other wrapped ops and
             ;; to satisfy the guard on the value-uN constructor. - EM
             (value-u8 (loghead 8 res))))
          ((and (value-case left :u16) (value-case right :u16))
           (b* (((when (= (value-u16->get right) 0))
                 err)
                (res (truncate (value-u16->get left) (value-u16->get right))))
             (value-u16 (loghead 16 res))))
          ((and (value-case left :u32) (value-case right :u32))
           (b* (((when (= (value-u32->get right) 0))
                 err)
                (res (truncate (value-u32->get left) (value-u32->get right))))
             (value-u32 (loghead 32 res))))
          ((and (value-case left :u64) (value-case right :u64))
           (b* (((when (= (value-u64->get right) 0))
                 err)
                (res (truncate (value-u64->get left) (value-u64->get right))))
             (value-u64 (loghead 64 res))))
          ((and (value-case left :u128) (value-case right :u128))
           (b* (((when (= (value-u128->get right) 0))
                 err)
                (res (truncate (value-u128->get left) (value-u128->get right))))
             (value-u128 (loghead 128 res))))
          ;; signed
          ((and (value-case left :i8) (value-case right :i8))
           (b* (((when (= (value-i8->get right) 0))
                 err)
                (res (truncate (value-i8->get left) (value-i8->get right))))
             (value-i8 (logext 8 res))))
          ((and (value-case left :i16) (value-case right :i16))
           (b* (((when (= (value-i16->get right) 0))
                 err)
                (res (truncate (value-i16->get left) (value-i16->get right))))
             (value-i16 (logext 16 res))))
          ((and (value-case left :i32) (value-case right :i32))
           (b* (((when (= (value-i32->get right) 0))
                 err)
                (res (truncate (value-i32->get left) (value-i32->get right))))
             (value-i32 (logext 32 res))))
          ((and (value-case left :i64) (value-case right :i64))
           (b* (((when (= (value-i64->get right) 0))
                 err)
                (res (truncate (value-i64->get left) (value-i64->get right))))
             (value-i64 (logext 64 res))))
          ((and (value-case left :i128) (value-case right :i128))
           (b* (((when (= (value-i128->get right) 0))
                 err)
                (res (truncate (value-i128->get left) (value-i128->get right))))
             (value-i128 (logext 128 res))))
          (t err))) ; different operand types
  :guard-hints (("Goal" :in-theory (e/d (int-valuep
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext))))
  ///
  (fty::deffixequiv op-int-div-wrapped
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-rem ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer remainder operation."
  (b* ((err (reserrf (list :op-int-rem (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* (((when (= (value-u8->get right) 0))
                 err)
                (divres (truncate (value-u8->get left) (value-u8->get right)))
                ((unless (ubyte8p divres))
                 err)
                (res (rem (value-u8->get left) (value-u8->get right)))
                ((unless (ubyte8p res))
                 ;; this should always be true, we should
                 ;; prove it and then get rid of it or replace by mbt
                 err))
             (value-u8 res)))
          ((and (value-case left :u16) (value-case right :u16))
           (b* (((when (= (value-u16->get right) 0))
                 err)
                (divres (truncate (value-u16->get left) (value-u16->get right)))
                ((unless (ubyte16p divres))
                 err)
                (res (rem (value-u16->get left) (value-u16->get right)))
                ((unless (ubyte16p res))
                 err))
             (value-u16 res)))
          ((and (value-case left :u32) (value-case right :u32))
           (b* (((when (= (value-u32->get right) 0))
                 err)
                (divres (truncate (value-u32->get left) (value-u32->get right)))
                ((unless (ubyte32p divres))
                 err)
                (res (rem (value-u32->get left) (value-u32->get right)))
                ((unless (ubyte32p res))
                 err))
             (value-u32 res)))
          ((and (value-case left :u64) (value-case right :u64))
           (b* (((when (= (value-u64->get right) 0))
                 err)
                (divres (truncate (value-u64->get left) (value-u64->get right)))
                ((unless (ubyte64p divres))
                 err)
                (res (rem (value-u64->get left) (value-u64->get right)))
                ((unless (ubyte64p res))
                 err))
             (value-u64 res)))
          ((and (value-case left :u128) (value-case right :u128))
           (b* (((when (= (value-u128->get right) 0))
                 err)
                (divres (truncate (value-u128->get left) (value-u128->get right)))
                ((unless (ubyte128p divres))
                 err)
                (res (rem (value-u128->get left) (value-u128->get right)))
                ((unless (ubyte128p res))
                 err))
             (value-u128 res)))
          (t err))) ; different operand types
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (int-valuep
                       ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                       sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                 (truncate rem))))
  ///
  (fty::deffixequiv op-int-rem
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-rem-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped remainder operation."
  (b* ((err (reserrf (list :op-int-rem-wrapped
                           (value-fix left) (value-fix right)))))
    (cond ((and (value-case left :u8) (value-case right :u8))
           (b* (((when (= (value-u8->get right) 0))
                 err)
                (res (rem (value-u8->get left) (value-u8->get right))))
             ;; Strictly speaking we don't need this loghead on the remainder
             ;; because there is no danger of overflow in execution, I believe.
             ;; It is here for consistency with other wrapped ops and
             ;; to satisfy the guard on the value-uN constructor. - EM
             (value-u8 (loghead 8 res))))
          ((and (value-case left :u16) (value-case right :u16))
           (b* (((when (= (value-u16->get right) 0))
                 err)
                (res (rem (value-u16->get left) (value-u16->get right))))
             (value-u16 (loghead 16 res))))
          ((and (value-case left :u32) (value-case right :u32))
           (b* (((when (= (value-u32->get right) 0))
                 err)
                (res (rem (value-u32->get left) (value-u32->get right))))
             (value-u32 (loghead 32 res))))
          ((and (value-case left :u64) (value-case right :u64))
           (b* (((when (= (value-u64->get right) 0))
                 err)
                (res (rem (value-u64->get left) (value-u64->get right))))
             (value-u64 (loghead 64 res))))
          ((and (value-case left :u128) (value-case right :u128))
           (b* (((when (= (value-u128->get right) 0))
                 err)
                (res (rem (value-u128->get left) (value-u128->get right))))
             (value-u128 (loghead 128 res))))
          ;; signed
          ((and (value-case left :i8) (value-case right :i8))
           (b* (((when (= (value-i8->get right) 0))
                 err)
                (z (truncate (value-i8->get left) (value-i8->get right)))
                (w (logext 8 z))
                (res (rem (value-i8->get left) (value-i8->get right)))
                (wres (if (= w z) res 0)))
             (if (sbyte8p wres)
                 (value-i8 wres)
               err)))
          ((and (value-case left :i16) (value-case right :i16))
           (b* (((when (= (value-i16->get right) 0))
                 err)
                (z (truncate (value-i16->get left) (value-i16->get right)))
                (w (logext 16 z))
                (res (rem (value-i16->get left) (value-i16->get right)))
                (wres (if (= w z) res 0)))
             (if (sbyte16p wres)
                 (value-i16 wres)
               err)))
          ((and (value-case left :i32) (value-case right :i32))
           (b* (((when (= (value-i32->get right) 0))
                 err)
                (z (truncate (value-i32->get left) (value-i32->get right)))
                (w (logext 32 z))
                (res (rem (value-i32->get left) (value-i32->get right)))
                (wres (if (= w z) res 0)))
             (if (sbyte32p wres)
                 (value-i32 wres)
               err)))
          ((and (value-case left :i64) (value-case right :i64))
           (b* (((when (= (value-i64->get right) 0))
                 err)
                (z (truncate (value-i64->get left) (value-i64->get right)))
                (w (logext 64 z))
                (res (rem (value-i64->get left) (value-i64->get right)))
                (wres (if (= w z) res 0)))
             (if (sbyte64p wres)
                 (value-i64 wres)
               err)))
          ((and (value-case left :i128) (value-case right :i128))
           (b* (((when (= (value-i128->get right) 0))
                 err)
                (z (truncate (value-i128->get left) (value-i128->get right)))
                (w (logext 128 z))
                (res (rem (value-i128->get left) (value-i128->get right)))
                (wres (if (= w z) res 0)))
             (if (sbyte128p wres)
                 (value-i128 wres)
               err)))
          (t err))) ; different operand types
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (int-valuep
                       ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                       sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                      (loghead logext))))
  ///
  (fty::deffixequiv op-int-rem-wrapped
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-pow ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer exponentiation operation."
  (b* ((err (reserrf (list :op-int-pow (value-fix left) (value-fix right))))
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        err)
       (left-int (int-value-to-int left))
       (right-int (int-value-to-int right))
       (res (expt left-int right-int)))
    (cond ((value-case left :u8)
           (if (ubyte8p res)
               (value-u8 res)
             err))
          ((value-case left :u16)
           (if (ubyte16p res)
               (value-u16 res)
             err))
          ((value-case left :u32)
           (if (ubyte32p res)
               (value-u32 res)
             err))
          ((value-case left :u64)
           (if (ubyte64p res)
               (value-u64 res)
             err))
          ((value-case left :u128)
           (if (ubyte128p res)
               (value-u128 res)
             err))
          ((value-case left :i8)
           (if (sbyte8p res)
               (value-i8 res)
             err))
          ((value-case left :i16)
           (if (sbyte16p res)
               (value-i16 res)
             err))
          ((value-case left :i32)
           (if (sbyte32p res)
               (value-i32 res)
             err))
          ((value-case left :i64)
           (if (sbyte64p res)
               (value-i64 res)
             err))
          ((value-case left :i128)
           (if (sbyte128p res)
               (value-i128 res)
             err))
          (t (reserrf (impossible)))))
  :guard-hints (("Goal" :in-theory (enable int-valuep
                                           int-value-to-int)))
  ///
  (fty::deffixequiv op-int-pow
    :args ((left valuep) (right valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-int-pow-wrapped ((left int-valuep) (right int-valuep))
  :returns (result value-resultp)
  :short "Leo integer wrapped exponentiation operation."
  (b* ((err (reserrf (list :op-int-pow-wrapped (value-fix left) (value-fix right))))
       ((unless (member-eq (value-kind right) '(:u8 :u16 :u32)))
        err)
       (left-int (int-value-to-int left))
       (right-int (int-value-to-int right))
       (res (expt left-int right-int)))
    (cond ((value-case left :u8)
           (value-u8 (loghead 8 res)))
          ((value-case left :u16)
           (value-u16 (loghead 16 res)))
          ((value-case left :u32)
           (value-u32 (loghead 32 res)))
          ((value-case left :u64)
           (value-u64 (loghead 64 res)))
          ((value-case left :u128)
           (value-u128 (loghead 128 res)))
          ;; signed
          ((value-case left :i8)
           (value-i8 (logext 8 res)))
          ((value-case left :i16)
           (value-i16 (logext 16 res)))
          ((value-case left :i32)
           (value-i32 (logext 32 res)))
          ((value-case left :i64)
           (value-i64 (logext 64 res)))
          ((value-case left :i128)
           (value-i128 (logext 128 res)))
          (t (reserrf (impossible)))))
  :guard-hints (("Goal" :in-theory (e/d (int-valuep int-value-to-int
                                         ubyte8p ubyte16p ubyte32p ubyte64p ubyte128p
                                         sbyte8p sbyte16p sbyte32p sbyte64p sbyte128p)
                                        (loghead logext))))

  ///
  (fty::deffixequiv op-int-pow-wrapped
    :args ((left valuep) (right valuep))))
