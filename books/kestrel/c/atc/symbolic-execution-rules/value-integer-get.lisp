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

(include-book "../../language/integer-operations")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-integer->get-rules
  :short "Rules about @(tsee value-integer->get)
          assuming the various integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Using these rules,
     instead of opening the definition of @(tsee value-integer->get),
     avoids case splits in proofs."))

  (defruled value-integer->get-when-scharp
    (implies (scharp x)
             (equal (value-integer->get x)
                    (schar->get x)))
    :enable (value-integer->get
             value-schar->get-to-schar->get))

  (defruled value-integer->get-when-ucharp
    (implies (ucharp x)
             (equal (value-integer->get x)
                    (uchar->get x)))
    :enable (value-integer->get
             value-uchar->get-to-uchar->get))

  (defruled value-integer->get-when-sshortp
    (implies (sshortp x)
             (equal (value-integer->get x)
                    (sshort->get x)))
    :enable (value-integer->get
             value-sshort->get-to-sshort->get))

  (defruled value-integer->get-when-ushortp
    (implies (ushortp x)
             (equal (value-integer->get x)
                    (ushort->get x)))
    :enable (value-integer->get
             value-ushort->get-to-ushort->get))

  (defruled value-integer->get-when-sintp
    (implies (sintp x)
             (equal (value-integer->get x)
                    (sint->get x)))
    :enable (value-integer->get
             value-sint->get-to-sint->get))

  (defruled value-integer->get-when-uintp
    (implies (uintp x)
             (equal (value-integer->get x)
                    (uint->get x)))
    :enable (value-integer->get
             value-uint->get-to-uint->get))

  (defruled value-integer->get-when-slongp
    (implies (slongp x)
             (equal (value-integer->get x)
                    (slong->get x)))
    :enable (value-integer->get
             value-slong->get-to-slong->get))

  (defruled value-integer->get-when-ulongp
    (implies (ulongp x)
             (equal (value-integer->get x)
                    (ulong->get x)))
    :enable (value-integer->get
             value-ulong->get-to-ulong->get))

  (defruled value-integer->get-when-sllongp
    (implies (sllongp x)
             (equal (value-integer->get x)
                    (sllong->get x)))
    :enable (value-integer->get
             value-sllong->get-to-sllong->get))

  (defruled value-integer->get-when-ullongp
    (implies (ullongp x)
             (equal (value-integer->get x)
                    (ullong->get x)))
    :enable (value-integer->get
             value-ullong->get-to-ullong->get))

  (defval *atc-value-integer->get-rules*
    '(value-integer->get-when-scharp
      value-integer->get-when-ucharp
      value-integer->get-when-sshortp
      value-integer->get-when-ushortp
      value-integer->get-when-sintp
      value-integer->get-when-uintp
      value-integer->get-when-slongp
      value-integer->get-when-ulongp
      value-integer->get-when-sllongp
      value-integer->get-when-ullongp)))
