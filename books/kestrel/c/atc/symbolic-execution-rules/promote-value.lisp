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

(include-book "integer-conversions")
(include-book "convert-integer-value")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-promote-value-rules
  :short "Rules about @(tsee promote-value) on values of given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules used during the symbolic execution."))

  (make-event
   `(local (in-theory (enable promote-value
                              promote-type
                              convert-integer-value-to-type-of-value
                              ,@*atc-convert-integer-value-rules*))))

  (defruled promote-value-when-scharp
    (implies (scharp x)
             (equal (promote-value x)
                    (sint-from-schar x))))

  (defruled promote-value-when-ucharp
    (implies (ucharp x)
             (equal (promote-value x)
                    (if (<= (uchar-max) (sint-max))
                        (sint-from-uchar x)
                      (uint-from-uchar x)))))

  (defruled promote-value-when-sshortp
    (implies (sshortp x)
             (equal (promote-value x)
                    (sint-from-sshort x))))

  (defruled promote-value-when-ushortp
    (implies (ushortp x)
             (equal (promote-value x)
                    (if (<= (ushort-max) (sint-max))
                        (sint-from-ushort x)
                      (uint-from-ushort x)))))

  (defruled promote-value-when-sintp
    (implies (sintp x)
             (equal (promote-value x)
                    x)))

  (defruled promote-value-when-uintp
    (implies (uintp x)
             (equal (promote-value x)
                    x)))

  (defruled promote-value-when-slongp
    (implies (slongp x)
             (equal (promote-value x)
                    x)))

  (defruled promote-value-when-ulongp
    (implies (ulongp x)
             (equal (promote-value x)
                    x)))

  (defruled promote-value-when-sllongp
    (implies (sllongp x)
             (equal (promote-value x)
                    x)))

  (defruled promote-value-when-ullongp
    (implies (ullongp x)
             (equal (promote-value x)
                    x)))

  (defval *atc-promote-value-rules*
    '(promote-value-when-scharp
      promote-value-when-ucharp
      promote-value-when-sshortp
      promote-value-when-ushortp
      promote-value-when-sintp
      promote-value-when-uintp
      promote-value-when-slongp
      promote-value-when-ulongp
      promote-value-when-sllongp
      promote-value-when-ullongp)))
