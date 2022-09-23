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

(defxdoc+ real-operations
  :parents (language)
  :short "Operations on C real values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lt-real-values ((val1 valuep) (val2 valuep))
  :guard (and (value-realp val1)
              (value-realp val2))
  :returns (resval valuep)
  :short "Apply @('<') to real values [C:6.5.8/3] [C:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only real values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer real values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (lt-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix))
