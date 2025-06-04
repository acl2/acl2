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

(include-book "arithmetic-operations")
(include-book "pointer-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ scalar-operations
  :parents (language)
  :short "Operations on C scalar values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-scalar-value ((val valuep))
  :guard (value-scalarp val)
  :returns (res booleanp)
  :short "Test a scalar value logically."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some contexts (e.g. conditional tests),
     a scalar is treated as a logical boolean:
     false if 0 (i.e. null if a pointer),
     true if not 0 (i.e. not null if a pointer).
     This is captured by this ACL2 function."))
  (cond ((value-integerp val) (test-integer-value val))
        ((value-case val :pointer) (test-pointer-value val))
        (t (ec-call (acl2::bool-fix (impossible)))))
  :guard-hints (("Goal" :in-theory (enable value-scalarp
                                           value-arithmeticp
                                           value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-scalar-value ((val valuep))
  :guard (value-scalarp val)
  :returns (resval valuep)
  :short "Apply @('!') to a scalar value [C17:6.5.3.3/5]."
  (cond ((value-integerp val) (lognot-integer-value val))
        ((value-case val :pointer) (lognot-pointer-value val))
        (t (ec-call (value-fix (impossible)))))
  :guard-hints (("Goal" :in-theory (enable value-scalarp
                                           value-arithmeticp
                                           value-realp)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-lognot-scalar-value
    (equal (type-of-value resval)
           (type-sint))
    :hyp (value-scalarp val)
    :hints (("Goal" :in-theory (enable value-scalarp
                                       value-arithmeticp
                                       value-realp
                                       value-integerp
                                       value-signed-integerp
                                       value-unsigned-integerp)))))
