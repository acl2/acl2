; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "scalar-operations")
(include-book "array-operations")
(include-book "structure-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
  :short "Apply unary @('+') to a value [C17:6.5.3.3/1] [C17:6.5.3.3/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not arithmetic."))
  (if (value-arithmeticp val)
      (plus-arithmetic-value val)
    (error (list :plus-mistype
                 :required :arithmetic
                 :supplied (value-fix val))))
  :hooks (:fix)

  ///

  (defret valuep-of-plus-value
    (valuep resval)
    :hyp (value-arithmeticp val))

  (defret type-of-value-of-plus-value
    (equal (type-of-value resval)
           (promote-type (type-of-value val)))
    :hyp (value-arithmeticp val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply unary @('-') to a value [C17:6.5.3.3/1] [C17:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not arithmetic."))
  (if (value-arithmeticp val)
      (minus-arithmetic-value val)
    (error (list :minus-mistype
                 :required :arithmetic
                 :supplied (value-fix val))))
  :hooks (:fix)

  ///

  (defret type-of-value-of-minus-value
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (promote-type (type-of-value val))))
    :hyp (value-arithmeticp val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitnot-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply @('~') to a value [C17:6.5.3.3/1] [C17:6.5.3.3/4]."
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
  :hooks (:fix)

  ///

  (defret type-of-value-of-bitnot-value
    (equal (type-of-value resval)
           (promote-type (type-of-value val)))
    :hyp (value-integerp val)
    :hints (("Goal" :in-theory (enable type-of-value-of-promote-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-value ((val valuep))
  :returns (resval value-resultp)
  :short "Apply @('!') to a value [C17:6.5.3.3/1] [C17:6.5.3.3/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the value is not scalar."))
  (if (value-scalarp val)
      (lognot-scalar-value val)
    (error (list :lognot-mistype
                 :required :scalar
                 :supplied (value-fix val))))
  :hooks (:fix)

  ///

  (defret type-of-value-of-lognot-value
    (equal (type-of-value resval)
           (type-sint))
    :hyp (value-scalarp val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mul-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply binary @('*') to values [C17:6.5.5/2] [C17:6.5.5/3] [C17:6.5.5/4]."
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
  :short "Apply @('/') to values [C17:6.5.5/2] [C17:6.5.5/3] [C17:6.5.5/5]."
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
          [C17:6.5.5/2] [C17:6.5.5/3] [C17:6.5.5/5] [C17:6.5.5/6]."
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
  :short "Apply binary @('+') to values [C17:6.5.5/2] [C17:6.5.5/5]."
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
  :short "Apply binary @('-') to values [C17:6.5.5/3] [C17:6.5.5/6]."
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
  :short "Apply @('<<') to values [C17:6.5.7/2] [C17:6.5.7/3] [C17:6.5.7/4]."
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
  :short "Apply @('>>') to values [C17:6.5.7/2] [C17:6.5.7/3] [C17:6.5.7/5]."
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lt-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('<') to values [C17:6.5.8/2] [C17:6.5.8/3] [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not real;
     we do not support comparison of pointers yet."))
  (if (and (value-realp val1)
           (value-realp val2))
      (lt-real-values val1 val2)
    (error (list :lt-mistype
                 :required :real :real
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gt-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('>') to values [C17:6.5.8/2] [C17:6.5.8/3] [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not real;
     we do not support comparison of pointers yet."))
  (if (and (value-realp val1)
           (value-realp val2))
      (gt-real-values val1 val2)
    (error (list :gt-mistype
                 :required :real :real
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define le-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('<=') to values [C17:6.5.8/2] [C17:6.5.8/3] [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not real;
     we do not support comparison of pointers yet."))
  (if (and (value-realp val1)
           (value-realp val2))
      (le-real-values val1 val2)
    (error (list :le-mistype
                 :required :real :real
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ge-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('>=') to values [C17:6.5.8/2] [C17:6.5.8/3] [C17:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not real;
     we do not support comparison of pointers yet."))
  (if (and (value-realp val1)
           (value-realp val2))
      (ge-real-values val1 val2)
    (error (list :ge-mistype
                 :required :real :real
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eq-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('==') to values [C17:6.5.9/2] [C17:6.5.9/3] [C17:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support arithmetic types."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (eq-arithmetic-values val1 val2)
    (error (list :eq-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ne-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('!=') to values [C17:6.5.9/2] [C17:6.5.9/3] [C17:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support arithmetic types."))
  (if (and (value-arithmeticp val1)
           (value-arithmeticp val2))
      (ne-arithmetic-values val1 val2)
    (error (list :ne-mistype
                 :required :arithmetic :arithmetic
                 :supplied (value-fix val1) (value-fix val2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitand-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('&') to values [C17:6.5.10/2] [C17:6.5.10/3] [C17:6.5.10/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not integers.
     If they are integers, we perform the usual arithmetic conversions
     and then we call the operation on integer values."))
  (if (and (value-integerp val1)
           (value-integerp val2))
      (b* (((mv val1 val2) (uaconvert-values val1 val2)))
        (bitand-integer-values val1 val2))
    (error (list :bitand-mistype
                 :required :integer :integer
                 :supplied (value-fix val1) (value-fix val2))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitxor-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('^') to values [C17:6.5.11/2] [C17:6.5.11/3] [C17:6.5.11/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not integers.
     If they are integers, we perform the usual arithmetic conversions
     and then we call the operation on integer values."))
  (if (and (value-integerp val1)
           (value-integerp val2))
      (b* (((mv val1 val2) (uaconvert-values val1 val2)))
        (bitxor-integer-values val1 val2))
    (error (list :bitand-mistype
                 :required :integer :integer
                 :supplied (value-fix val1) (value-fix val2))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitior-values ((val1 valuep) (val2 valuep))
  :returns (resval value-resultp)
  :short "Apply @('|') to values [C17:6.5.12/2] [C17:6.5.12/3] [C17:6.5.12/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the values are not integers.
     If they are integers, we perform the usual arithmetic conversions
     and then we call the operation on integer values."))
  (if (and (value-integerp val1)
           (value-integerp val2))
      (b* (((mv val1 val2) (uaconvert-values val1 val2)))
        (bitior-integer-values val1 val2))
    (error (list :bitand-mistype
                 :required :integer :integer
                 :supplied (value-fix val1) (value-fix val2))))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix))
