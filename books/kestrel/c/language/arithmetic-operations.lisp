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

(include-book "integer-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ arithmetic-operations
  :parents (language)
  :short "Operations on C arithmetic values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plus-arithmetic-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (resval value-resultp)
  :short "Apply unary @('+') to an arithmetic value [C:6.5.3.3/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We promote the operand
     and then we apply the operation on the integer.
     In our current formalization,
     integers are the only arithmetic value.
     This ACL2 function will be extended with more cases
     if/when we extend out model with non-integer arithmetic values."))
  (b* ((val (promote-value val)))
    (plus-integer-value val))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-arithmetic-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (resval value-resultp)
  :short "Apply unary @('-') to an arithmetic value [C:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We promote the operand
     and then we apply the operation on the integer.
     In our current formalization,
     integers are the only arithmetic value.
     This ACL2 function will be extended with more cases
     if/when we extend out model with non-integer arithmetic value."))
  (b* ((val (promote-value val)))
    (minus-integer-value val))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mul-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply binary @('*') to arithmetic values [C:6.5.5/2] [C:6.5.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic value.
     This ACL2 function will be extended with more cases
     if/when we extend out model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (mul-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix))
