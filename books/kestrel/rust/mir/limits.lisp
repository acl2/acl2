; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "types")

(include-book "std/util/defval" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir-limits
  :parents (mir)
  :short "Target parameters: integer widths, ranges, and wrapping."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rust leaves the widths of @('usize') and @('isize')
     to the target platform.
     We model a 64-bit target
     (the common case: x86-64 and AArch64),
     so @('usize') and @('isize') are 64 bits wide;
     all other integer types have the width their name states.")
   (xdoc::p
    "This book also defines
     the value ranges of the integer types,
     recognizers for integers within those ranges,
     and the wrapping (two's-complement truncating) conversions
     used by the semantics of
     arithmetic and overflow-checked operations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *pointer-bits*
  :short "Width in bits of pointers, @('usize'), and @('isize')."
  64)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-type-bits ((type int-typep))
  :returns (bits posp)
  :short "Width in bits of a signed integer type."
  (int-type-case type
                 :isize *pointer-bits*
                 :i8 8
                 :i16 16
                 :i32 32
                 :i64 64
                 :i128 128)
  ///

  (defret int-type-bits-lower-bound
    (<= 8 bits)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-type-bits ((type uint-typep))
  :returns (bits posp)
  :short "Width in bits of an unsigned integer type."
  (uint-type-case type
                  :usize *pointer-bits*
                  :u8 8
                  :u16 16
                  :u32 32
                  :u64 64
                  :u128 128)
  ///

  (defret uint-type-bits-lower-bound
    (<= 8 bits)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-type-max ((type uint-typep))
  :returns (max posp
                :hints (("Goal" :in-theory (enable uint-type-bits))))
  :short "Maximum value of an unsigned integer type."
  (1- (expt 2 (uint-type-bits type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-type-max ((type int-typep))
  :returns (max posp
                :hints (("Goal" :in-theory (enable int-type-bits))))
  :short "Maximum value of a signed integer type."
  (1- (expt 2 (1- (int-type-bits type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-type-min ((type int-typep))
  :returns (min acl2::integerp)
  :short "Minimum value of a signed integer type."
  (- (expt 2 (1- (int-type-bits type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-valuep ((val acl2::integerp) (type uint-typep))
  :returns (yes/no booleanp)
  :short "Check if an integer is in the range of an unsigned integer type."
  (b* ((val (acl2::ifix val)))
    (and (<= 0 val)
         (<= val (uint-type-max type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-valuep ((val acl2::integerp) (type int-typep))
  :returns (yes/no booleanp)
  :short "Check if an integer is in the range of a signed integer type."
  (b* ((val (acl2::ifix val)))
    (and (<= (int-type-min type) val)
         (<= val (int-type-max type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-wrap ((val acl2::integerp) (type uint-typep))
  :returns (result natp)
  :short "Wrap an integer into the range of an unsigned integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is reduction modulo @($2^n$) for the type's width @($n$):
     the semantics of Rust's wrapping unsigned operations,
     and of the value component of the overflow-checked operations."))
  (mod (acl2::ifix val)
       (expt 2 (uint-type-bits type)))
  ///

  (defret uint-valuep-of-uint-wrap
    (uint-valuep result type)
    :hints (("Goal" :in-theory (enable uint-valuep uint-type-max ifix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-wrap ((val acl2::integerp) (type int-typep))
  :returns (result acl2::integerp)
  :short "Wrap an integer into the range of a signed integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two's-complement truncation:
     reduce modulo @($2^n$) for the type's width @($n$),
     then subtract @($2^n$) if the result is
     @($2^{n-1}$) or more.
     This is the semantics of Rust's wrapping signed operations,
     and of the value component of the overflow-checked operations."))
  (b* ((bits (int-type-bits type))
       (m (mod (acl2::ifix val) (expt 2 bits))))
    (if (< m (expt 2 (1- bits)))
        m
      (- m (expt 2 bits))))
  ///

  (defret int-valuep-of-int-wrap
    (int-valuep result type)
    :hints (("Goal" :in-theory (enable int-valuep
                                       int-type-max
                                       int-type-min
                                       ifix)))))
