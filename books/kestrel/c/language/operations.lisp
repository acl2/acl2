; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "scalar-operations")
(include-book "array-operations")
(include-book "structure-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (language)
  :short "Operations on C values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-value ((val valuep))
  :returns (res boolean-resultp)
  :short "Test a value logically."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some contexts (e.g. conditional tests),
     a value is treated as a logical boolean.
     The value must be scalar; see @(tsee test-scalar-value) for details."))
  (if (value-scalarp val)
      (test-scalar-value val)
    (error (list :test-mistype
                 :required :scalar
                 :supplied (value-fix val))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plus-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply unary @('+') to a value [C:6.5.3.3/1] [C:6.5.3.3/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not arithmetic."))
  (if (value-arithmeticp val)
      (plus-arithmetic-value val)
    (error (list :plus-mistype
                 :required :arithmetic
                 :supplied (value-fix val))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply unary @('-') to a value [C:6.5.3.3/1] [C:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not arithmetic."))
  (if (value-arithmeticp val)
      (minus-arithmetic-value val)
    (error (list :minus-mistype
                 :required :arithmetic
                 :supplied (value-fix val))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitnot-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply @('~') to a value [C:6.5.3.3/1] [C:6.5.3.3/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not integer.
     If it is integer, we promote it and then we flip its bits."))
  (if (value-integerp val)
      (bitnot-integer-value (promote-value val))
    (error (list :bitnot-mistype
                 :required :integer
                 :supplied (value-fix val))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply @('!') to a value [C:6.5.3.3/1] [C:6.5.3.3/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not scalar."))
  (if (value-scalarp val)
      (lognot-scalar-value val)
    (error (list :lognot-mistype
                 :required :scalar
                 :supplied (value-fix val))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mul-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply binary @('*') to values [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not arithmetic."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (mul-arithmetic-values val1 val2)
    (error (list :mul-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define div-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('/') to values [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not arithmetic."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (div-arithmetic-values val1 val2)
    (error (list :div-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rem-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('%') to values
          [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/5] [C:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not arithmetic."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (rem-arithmetic-values val1 val2)
    (error (list :rem-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply binary @('+') to values [C:6.5.5/2] [C:6.5.5/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support arithmetic values for now (no pointer arithmetic)."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (add-arithmetic-values val1 val2)
    (error (list :add-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply binary @('-') to values [C:6.5.5/3] [C:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support arithmetic values for now (no pointer arithmetic)."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (sub-arithmetic-values val1 val2)
    (error (list :sub-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shl-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('<<') to values [C:6.5.7/2] [C:6.5.7/3] [C:6.5.7/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not integers.
     If they are integers, we promote them
     and then we call the operation on integer values."))
  (if (and (value-integerp val1)
           (value-integerp val2))
      (shl-integer-values (promote-value val1)
                          (promote-value val2))
    (error (list :shl-mistype
                 :required :integer :integer
                 :supplied (value-fix val1) (value-fix val2))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shr-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('>>') to values [C:6.5.7/2] [C:6.5.7/3] [C:6.5.7/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not integers.
     If they are integers, we promote them
     and then we call the operation on integer values."))
  (if (and (value-integerp val1)
           (value-integerp val2))
      (shr-integer-values (promote-value val1)
                          (promote-value val2))
    (error (list :shr-mistype
                 :required :integer :integer
                 :supplied (value-fix val1) (value-fix val2))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))
