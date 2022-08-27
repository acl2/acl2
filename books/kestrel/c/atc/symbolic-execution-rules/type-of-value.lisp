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

(include-book "integers")
(include-book "arrays")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-type-of-value-rules
  :short "Rules about @(tsee type-of-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules rewrite @(tsee type-of-value) to specific types
     under hypotheses on different types of values
     that occur during symbolic execution."))

  (defruled type-of-value-when-value-pointer
    (implies (and (valuep x)
                  (value-case x :pointer))
             (equal (type-of-value x)
                    (type-pointer (value-pointer->reftype x))))
    :enable type-of-value)

  (defval *atc-type-of-value-rules*
    '(type-of-value-when-ucharp
      type-of-value-when-scharp
      type-of-value-when-ushortp
      type-of-value-when-sshortp
      type-of-value-when-uintp
      type-of-value-when-sintp
      type-of-value-when-ulongp
      type-of-value-when-slongp
      type-of-value-when-ullongp
      type-of-value-when-sllongp
      type-of-value-when-value-pointer
      type-of-value-when-uchar-arrayp
      type-of-value-when-schar-arrayp
      type-of-value-when-ushort-arrayp
      type-of-value-when-sshort-arrayp
      type-of-value-when-uint-arrayp
      type-of-value-when-sint-arrayp
      type-of-value-when-ulong-arrayp
      type-of-value-when-slong-arrayp
      type-of-value-when-ullong-arrayp
      type-of-value-when-sllong-arrayp)))
