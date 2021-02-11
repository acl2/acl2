; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/fty/sbyte32" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-signed-ints
  :parents (atc-integers)
  :short "A model of C (@('signed')) @('int')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a fixtype for values of the (@('signed')) @('int') type,
     along with functions for operations on these values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sint
  :short "Fixtype of C (@('signed')) @('int') values [C:6.2.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we represent these as 32-bit two's complement integers.
     This is consistent with macOS and with (at least some) Linux.
     In the future, we will generalize this model."))
  ((get acl2::sbyte32))
  :tag :sint
  :layout :list
  :pred sintp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-const ((x natp))
  :guard (acl2::sbyte32p x)
  :returns (result sintp)
  :short "Integer constant of type @('int') [C:6.4.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [C:6.4.4.1/5], @('int') is
     the first integer type assigned to an integer constant,
     provided that the constant's value is representable.
     The value is always non-negative.")
   (xdoc::p
    "This ACL2 function models an integer constant of type @('int').
     It takes as argument a natural number, i.e. the constant's value,
     whose representability as an @('int') is ensured by the guard."))
  (sint x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-nonzerop ((x sintp))
  :returns (yes/no booleanp)
  :short "Check if an @('int') value is not 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used to turn an ACL2 term that returns a C @('int') value
     into an ACL2 boolean term that may be the test of an @(tsee if).
     This way, we can represent in ACL2 shallowly embedded C conditionals,
     whose tests must be integers (0 for false, non-0 for true)."))
  (/= (sint->get x) 0)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint01 ((b booleanp))
  :returns (x sintp)
  :short "Turn an ACL2 boolean into an @('int') value 0 or 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially (but not exactly) the inverse of @(tsee sint-nonzerop).
     Together with @(tsee sint-nonzerop),
     it can be used to represent in ACL2
     shallowly embedded C logical conjunctions and disjunctions,
     which must be integers in C,
     but must be booleans in ACL2 to represent their non-strictness."))
  (if b (sint 1) (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-plus ((x sintp))
  :returns (result sintp)
  :short "Unary plus of @('int') values [C:6.5.3.3]."
  (sint-fix x)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-minus-okp ((x sintp))
  :returns (yes/no booleanp)
  :short "Check if the unary minus of an @('int') value is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result is representable in @('int')."))
  (acl2::sbyte32p (- (sint->get x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-minus ((x sintp))
  :guard (sint-minus-okp x)
  :returns (result sintp)
  :short "Unary minus of @('int') values [C:6.5.3.3]."
  (sint (- (sint->get x)))
  :guard-hints (("Goal" :in-theory (enable sint-minus-okp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-bitnot ((x sintp))
  :returns (result sintp)
  :short "Bitwise complement of @('int') values [C:6.5.3]."
  (sint (lognot (sint->get x)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable acl2::sbyte32p
                                           sint->get
                                           sintp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-lognot ((x sintp))
  :returns (result sintp)
  :short "Logical complement of @('int') values [C:6.5.3]."
  (if (= (sint->get x) 0)
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-add-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the addition of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result is representable in @('int')."))
  (acl2::sbyte32p (+ (sint->get x) (sint->get y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-add ((x sintp) (y sintp))
  :guard (sint-add-okp x y)
  :returns (result sintp)
  :short "Addition of @('int') values [C:6.5.6]."
  (sint (+ (sint->get x) (sint->get y)))
  :guard-hints (("Goal" :in-theory (enable sint-add-okp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-sub-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the subtraction of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result is representable in @('int')."))
  (acl2::sbyte32p (- (sint->get x) (sint->get y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-sub ((x sintp) (y sintp))
  :guard (sint-sub-okp x y)
  :returns (result sintp)
  :short "Subtraction of @('int') values [C:6.5.6]."
  (sint (- (sint->get x) (sint->get y)))
  :guard-hints (("Goal" :in-theory (enable sint-sub-okp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-mul-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the multiplication of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result is representable in @('int')."))
  (acl2::sbyte32p (* (sint->get x) (sint->get y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-mul ((x sintp) (y sintp))
  :guard (sint-mul-okp x y)
  :returns (result sintp)
  :short "Multiplication of @('int') values [C:6.5.5]."
  (sint (* (sint->get x) (sint->get y)))
  :guard-hints (("Goal" :in-theory (enable sint-mul-okp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-div-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the division of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result is representable in @('int').
     We also check if the divisor is not 0."))
  (and (not (equal (sint->get y) 0))
       (acl2::sbyte32p (truncate (sint->get x) (sint->get y))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-div ((x sintp) (y sintp))
  :guard (sint-div-okp x y)
  :returns (result sintp)
  :short "Division of @('int') values [C:6.5.5]."
  :long
  (xdoc::topstring-p
   "Integer division truncates towards 0 [C:6.5.5/5].")
  (sint (truncate (sint->get x) (sint->get y)))
  :guard-hints (("Goal" :in-theory (enable sint-div-okp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-rem-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the remainder of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if the exact result of the integer division is representable,
     consistently with [C:6.5.5/6].
     We also check if the divisor is not 0."))
  (and (not (equal (sint->get y) 0))
       (acl2::sbyte32p (truncate (sint->get x) (sint->get y))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-rem ((x sintp) (y sintp))
  :guard (sint-rem-okp x y)
  :returns (result sintp)
  :short "Remainder of @('int') values [C:6.5.5]."
  :long
  (xdoc::topstring-p
   "Note that the guard mentions @(tsee truncate) and not @(tsee rem),
    consistently with [C:6.5.5/6].")
  (sint (rem (sint->get x) (sint->get y)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable sint-rem-okp
                                           acl2::sbyte32p
                                           sint->get
                                           sintp)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-shl-sint-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the left shift of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "The right operand must be non-negative
     and below the bit size of the left operand
     [C:6.5.7/3].
     The bit size of @('int') is currently 32 in our model.")
   (xdoc::p
    "Since the left operand is signed here,
     it must be non-negative,
     and its product with 2 raised to the right operand must fit @('int')
     [C:6.5.7/4]."))
  (and (integer-range-p 0 32 (sint->get y))
       (>= (sint->get x) 0)
       (acl2::sbyte32p (* (sint->get x)
                          (expt 2 (sint->get y)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-shl-sint ((x sintp) (y sintp))
  :guard (sint-shl-sint-okp x y)
  :returns (result sintp)
  :short "Left shift of @('int') values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is described in [C:6.5.7/4]."))
  (sint (* (sint->get x)
           (expt 2 (sint->get y))))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable sint-shl-sint-okp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-shr-sint-okp ((x sintp) (y sintp))
  :returns (yes/no booleanp)
  :short "Check if the right shift of two @('int') values is well-defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "The right operand must be non-negative
     and below the bit size of the left operand
     [C:6.5.7/3].
     The bit size of @('int') is currently 32 in our model.")
   (xdoc::p
    "Since the left operand is signed here,
     it must be non-negative [C:6.5.7/5]."))
  (and (integer-range-p 0 32 (sint->get y))
       (>= (sint->get x) 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define sint-shr-sint ((x sintp) (y sintp))
  :guard (sint-shr-sint-okp x y)
  :returns (result sintp)
  :short "Right shift of @('int') values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is described in [C:6.5.7/4\5]."))
  (sint (truncate (sint->get x)
                  (expt 2 (sint->get y))))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable sint-shr-sint-okp
                                           acl2::sbyte32p
                                           sint->get
                                           sintp)))
  :prepwork
  ((local (include-book "kestrel/arithmetic-light/expt" :dir :system))
   (local (include-book "kestrel/arithmetic-light/truncate" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-lt ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Less than on @('int') values."
  (if (< (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-gt ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Greater than on @('int') values."
  (if (> (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-le ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Less than or equal to on @('int') values."
  (if (<= (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-ge ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Greater than or equal to on @('int') values."
  (if (>= (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-eq ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Equality on @('int') values."
  (if (= (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-ne ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Non-equality on @('int') values."
  (if (/= (sint->get x) (sint->get y))
      (sint 1)
    (sint 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-bitand ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Bitwise conjunction on @('int') values."
  (sint (logand (sint->get x) (sint->get y)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable acl2::sbyte32p
                                           sintp
                                           sint->get)))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-bitxor ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Bitwise exclusive disjunction on @('int') values."
  (sint (logxor (sint->get x) (sint->get y)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable acl2::sbyte32p
                                           sintp
                                           sint->get)))
  :prepwork
  ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-bitior ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Bitwise inclusive disjunction on @('int') values."
  (sint (logior (sint->get x) (sint->get y)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable acl2::sbyte32p
                                           sintp
                                           sint->get)))
  :prepwork
  ((local (include-book "centaur/bitops/ihs-extensions" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-logand ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Logical conjunction on @('int') values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a strict version of this operator,
     because it takes two values.
     Non-strict versions are represented differently;
     see @(tsee atc)."))
  (sint01 (and (sint-nonzerop x) (sint-nonzerop y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-logor ((x sintp) (y sintp))
  :returns (result sintp)
  :short "Logical disjunction on @('int') values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a strict version of this operator,
     because it takes two values.
     Non-strict versions are represented differently;
     see @(tsee atc)."))
  (sint01 (or (sint-nonzerop x) (sint-nonzerop y)))
  :hooks (:fix))
