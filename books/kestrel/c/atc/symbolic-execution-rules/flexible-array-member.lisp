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

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-flexible-array-member-rules
  :short "Rules about flexible array members."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our symbolic execution,
     the only use of structures with flexible array members
     is accessing their members;
     they are never copied,
     and thus the removal of the flexible array member never happens.
     In order to simplify away @(tsee remove-flexible-array-member),
     we need rules showing that our values being copied
     do not satisfy @(tsee remove-flexible-array-member).")
   (xdoc::p
    "Here we prove rules for the non-structure values.
     For structure values, @(tsee defstruct) generates rules
     saying that the recognizer implies that the flag is unset;
     here we provide a rule saying that if the flag is unset
     then @(tsee flexible-array-member-p) does not hold.")
   (xdoc::p
    "We also include the rule @('remove-flexible-array-member-when-absent')
     to actually simplify away @(tsee remove-flexible-array-member)."))

  (defruled not-flexible-array-member-p-when-ucharp
    (implies (ucharp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-scharp
    (implies (scharp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ushortp
    (implies (ushortp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sshortp
    (implies (sshortp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-uintp
    (implies (uintp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sintp
    (implies (sintp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ulongp
    (implies (ulongp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-slongp
    (implies (slongp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ullongp
    (implies (ullongp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sllongp
    (implies (sllongp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-uchar-arrayp
    (implies (uchar-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-schar-arrayp
    (implies (schar-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ushort-arrayp
    (implies (ushort-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sshort-arrayp
    (implies (sshort-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-uint-arrayp
    (implies (uint-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sint-arrayp
    (implies (sint-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ulong-arrayp
    (implies (ulong-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-slong-arrayp
    (implies (slong-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-ullong-arrayp
    (implies (ullong-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-sllong-arrayp
    (implies (sllong-arrayp val)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-value-pointer
    (implies (value-case val :pointer)
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defruled not-flexible-array-member-p-when-value-struct
    (implies (and (value-case val :struct)
                  (not (value-struct->flexiblep val)))
             (not (flexible-array-member-p val)))
    :enable flexible-array-member-p)

  (defval *atc-flexible-array-member-rules*
    '(not-flexible-array-member-p-when-ucharp
      not-flexible-array-member-p-when-scharp
      not-flexible-array-member-p-when-ushortp
      not-flexible-array-member-p-when-sshortp
      not-flexible-array-member-p-when-uintp
      not-flexible-array-member-p-when-sintp
      not-flexible-array-member-p-when-ulongp
      not-flexible-array-member-p-when-slongp
      not-flexible-array-member-p-when-ullongp
      not-flexible-array-member-p-when-sllongp
      not-flexible-array-member-p-when-uchar-arrayp
      not-flexible-array-member-p-when-schar-arrayp
      not-flexible-array-member-p-when-ushort-arrayp
      not-flexible-array-member-p-when-sshort-arrayp
      not-flexible-array-member-p-when-uint-arrayp
      not-flexible-array-member-p-when-sint-arrayp
      not-flexible-array-member-p-when-ulong-arrayp
      not-flexible-array-member-p-when-slong-arrayp
      not-flexible-array-member-p-when-ullong-arrayp
      not-flexible-array-member-p-when-sllong-arrayp
      not-flexible-array-member-p-when-value-pointer
      not-flexible-array-member-p-when-value-struct
      remove-flexible-array-member-when-absent)))
