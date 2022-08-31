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
