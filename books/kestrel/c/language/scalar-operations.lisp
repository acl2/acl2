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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ scalar-operations
  :parents (language)
  :short "Operations on C scalar values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-scalar-value ((val valuep))
  :guard (value-scalarp val)
  :returns (resval valuep)
  :short "Apply @('!') to a scalar value [C:6.5.3.3/5]."
  (cond ((value-integerp val) (lognot-integer-value val))
        ((value-case val :pointer) (lognot-pointer-value val))
        (t (ec-call (value-fix (impossible)))))
  :guard-hints (("Goal" :in-theory (enable value-scalarp
                                           value-arithmeticp
                                           value-realp)))
  :hooks (:fix))
