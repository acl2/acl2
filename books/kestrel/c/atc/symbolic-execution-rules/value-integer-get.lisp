; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")

(include-book "../../language/integer-operations")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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
                    (integer-from-schar x)))
    :enable (value-integer->get
             value-schar->get-to-integer-from-schar))

  (defruled value-integer->get-when-ucharp
    (implies (ucharp x)
             (equal (value-integer->get x)
                    (integer-from-uchar x)))
    :enable (value-integer->get
             value-uchar->get-to-integer-from-uchar))

  (defruled value-integer->get-when-sshortp
    (implies (sshortp x)
             (equal (value-integer->get x)
                    (integer-from-sshort x)))
    :enable (value-integer->get
             value-sshort->get-to-integer-from-sshort))

  (defruled value-integer->get-when-ushortp
    (implies (ushortp x)
             (equal (value-integer->get x)
                    (integer-from-ushort x)))
    :enable (value-integer->get
             value-ushort->get-to-integer-from-ushort))

  (defruled value-integer->get-when-sintp
    (implies (sintp x)
             (equal (value-integer->get x)
                    (integer-from-sint x)))
    :enable (value-integer->get
             value-sint->get-to-integer-from-sint))

  (defruled value-integer->get-when-uintp
    (implies (uintp x)
             (equal (value-integer->get x)
                    (integer-from-uint x)))
    :enable (value-integer->get
             value-uint->get-to-integer-from-uint))

  (defruled value-integer->get-when-slongp
    (implies (slongp x)
             (equal (value-integer->get x)
                    (integer-from-slong x)))
    :enable (value-integer->get
             value-slong->get-to-integer-from-slong))

  (defruled value-integer->get-when-ulongp
    (implies (ulongp x)
             (equal (value-integer->get x)
                    (integer-from-ulong x)))
    :enable (value-integer->get
             value-ulong->get-to-integer-from-ulong))

  (defruled value-integer->get-when-sllongp
    (implies (sllongp x)
             (equal (value-integer->get x)
                    (integer-from-sllong x)))
    :enable (value-integer->get
             value-sllong->get-to-integer-from-sllong))

  (defruled value-integer->get-when-ullongp
    (implies (ullongp x)
             (equal (value-integer->get x)
                    (integer-from-ullong x)))
    :enable (value-integer->get
             value-ullong->get-to-integer-from-ullong))

  (defruled value-integer->get-when-cintegerp
    (implies (cintegerp x)
             (equal (value-integer->get x)
                    (integer-from-cinteger x)))
    :enable (cintegerp
             cinteger-kind
             integer-from-cinteger
             cinteger-schar->get
             cinteger-uchar->get
             cinteger-sshort->get
             cinteger-ushort->get
             cinteger-sint->get
             cinteger-uint->get
             cinteger-slong->get
             cinteger-ulong->get
             cinteger-sllong->get
             cinteger-ullong->get
             value-integer->get-when-scharp
             value-integer->get-when-ucharp
             value-integer->get-when-sshortp
             value-integer->get-when-ushortp
             value-integer->get-when-sintp
             value-integer->get-when-uintp
             value-integer->get-when-slongp
             value-integer->get-when-ulongp
             value-integer->get-when-sllongp
             value-integer->get-when-ullongp))

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
