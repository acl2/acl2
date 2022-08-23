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

(include-book "arithmetic-operations")
(include-book "pointer-operations")
(include-book "array-operations")
(include-book "structure-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (language)
  :short "Operations on C values."
  :order-subtopics t
  :default-parent t)

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