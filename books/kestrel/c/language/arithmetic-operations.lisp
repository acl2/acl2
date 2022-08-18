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
     if/when we extend out model with non-integer arithmetic value."))
  (b* ((val (promote-value val)))
    (plus-integer-value val))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))
