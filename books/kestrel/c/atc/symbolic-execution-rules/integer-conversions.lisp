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

(include-book "../integer-conversions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-conv-rules
  :short "Rules about the composition of integer conversions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules used during the symbolic execution."))

  ;; unsigned int as final type:

  (defruled uint-from-sint-of-sint-from-schar
    (equal (uint-from-sint (sint-from-schar x))
           (uint-from-schar x))
    :enable (uint-from-sint
             sint-from-schar
             uint-from-schar
             sint-integerp-alt-def))

  (defruled uint-from-sint-of-sint-from-uchar
    (equal (uint-from-sint (sint-from-uchar x))
           (uint-from-uchar x))
    :enable (uint-from-sint
             sint-from-uchar
             uint-from-uchar
             sint-integerp-alt-def))

  (defruled uint-from-sint-of-sint-from-sshort
    (equal (uint-from-sint (sint-from-sshort x))
           (uint-from-sshort x))
    :enable (uint-from-sint
             sint-from-sshort
             uint-from-sshort
             sint-integerp-alt-def))

  (defruled uint-from-sint-of-sint-from-ushort
    (equal (uint-from-sint (sint-from-ushort x))
           (uint-from-ushort x))
    :enable (uint-from-sint
             sint-from-ushort
             uint-from-ushort
             sint-integerp-alt-def))

  ;; signed long as final type:

  (defruled slong-from-sint-of-sint-from-schar
    (equal (slong-from-sint (sint-from-schar x))
           (slong-from-schar x))
    :enable (slong-from-sint
             sint-from-schar
             slong-from-schar
             sint-integerp-alt-def))

  (defruled slong-from-sint-of-sint-from-uchar
    (equal (slong-from-sint (sint-from-uchar x))
           (slong-from-uchar x))
    :enable (slong-from-sint
             sint-from-uchar
             slong-from-uchar
             sint-integerp-alt-def))

  (defruled slong-from-sint-of-sint-from-sshort
    (equal (slong-from-sint (sint-from-sshort x))
           (slong-from-sshort x))
    :enable (slong-from-sint
             sint-from-sshort
             slong-from-sshort
             sint-integerp-alt-def))

  (defruled slong-from-sint-of-sint-from-ushort
    (equal (slong-from-sint (sint-from-ushort x))
           (slong-from-ushort x))
    :enable (slong-from-sint
             sint-from-ushort
             slong-from-ushort
             sint-integerp-alt-def))

  ;; unsigned long as final type:

  (defruled ulong-from-sint-of-sint-from-schar
    (equal (ulong-from-sint (sint-from-schar x))
           (ulong-from-schar x))
    :enable (ulong-from-sint
             sint-from-schar
             ulong-from-schar
             sint-integerp-alt-def))

  (defruled ulong-from-sint-of-sint-from-uchar
    (equal (ulong-from-sint (sint-from-uchar x))
           (ulong-from-uchar x))
    :enable (ulong-from-sint
             sint-from-uchar
             ulong-from-uchar
             sint-integerp-alt-def))

  (defruled ulong-from-sint-of-sint-from-sshort
    (equal (ulong-from-sint (sint-from-sshort x))
           (ulong-from-sshort x))
    :enable (ulong-from-sint
             sint-from-sshort
             ulong-from-sshort
             sint-integerp-alt-def))

  (defruled ulong-from-sint-of-sint-from-ushort
    (equal (ulong-from-sint (sint-from-ushort x))
           (ulong-from-ushort x))
    :enable (ulong-from-sint
             sint-from-ushort
             ulong-from-ushort
             sint-integerp-alt-def))

  ;; signed long long as final type:

  (defruled sllong-from-sint-of-sint-from-schar
    (equal (sllong-from-sint (sint-from-schar x))
           (sllong-from-schar x))
    :enable (sllong-from-sint
             sint-from-schar
             sllong-from-schar
             sint-integerp-alt-def))

  (defruled sllong-from-sint-of-sint-from-uchar
    (equal (sllong-from-sint (sint-from-uchar x))
           (sllong-from-uchar x))
    :enable (sllong-from-sint
             sint-from-uchar
             sllong-from-uchar
             sint-integerp-alt-def))

  (defruled sllong-from-sint-of-sint-from-sshort
    (equal (sllong-from-sint (sint-from-sshort x))
           (sllong-from-sshort x))
    :enable (sllong-from-sint
             sint-from-sshort
             sllong-from-sshort
             sint-integerp-alt-def))

  (defruled sllong-from-sint-of-sint-from-ushort
    (equal (sllong-from-sint (sint-from-ushort x))
           (sllong-from-ushort x))
    :enable (sllong-from-sint
             sint-from-ushort
             sllong-from-ushort
             sint-integerp-alt-def))

  ;; unsigned long long as final type:

  (defruled ullong-from-sint-of-sint-from-schar
    (equal (ullong-from-sint (sint-from-schar x))
           (ullong-from-schar x))
    :enable (ullong-from-sint
             sint-from-schar
             ullong-from-schar
             sint-integerp-alt-def))

  (defruled ullong-from-sint-of-sint-from-uchar
    (equal (ullong-from-sint (sint-from-uchar x))
           (ullong-from-uchar x))
    :enable (ullong-from-sint
             sint-from-uchar
             ullong-from-uchar
             sint-integerp-alt-def))

  (defruled ullong-from-sint-of-sint-from-sshort
    (equal (ullong-from-sint (sint-from-sshort x))
           (ullong-from-sshort x))
    :enable (ullong-from-sint
             sint-from-sshort
             ullong-from-sshort
             sint-integerp-alt-def))

  (defruled ullong-from-sint-of-sint-from-ushort
    (equal (ullong-from-sint (sint-from-ushort x))
           (ullong-from-ushort x))
    :enable (ullong-from-sint
             sint-from-ushort
             ullong-from-ushort
             sint-integerp-alt-def))

  (defval *atc-integer-conv-rules*
    '(uint-from-sint-of-sint-from-schar
      uint-from-sint-of-sint-from-uchar
      uint-from-sint-of-sint-from-sshort
      uint-from-sint-of-sint-from-ushort
      slong-from-sint-of-sint-from-schar
      slong-from-sint-of-sint-from-uchar
      slong-from-sint-of-sint-from-sshort
      slong-from-sint-of-sint-from-ushort
      ulong-from-sint-of-sint-from-schar
      ulong-from-sint-of-sint-from-uchar
      ulong-from-sint-of-sint-from-sshort
      ulong-from-sint-of-sint-from-ushort
      sllong-from-sint-of-sint-from-schar
      sllong-from-sint-of-sint-from-uchar
      sllong-from-sint-of-sint-from-sshort
      sllong-from-sint-of-sint-from-ushort
      ullong-from-sint-of-sint-from-schar
      ullong-from-sint-of-sint-from-uchar
      ullong-from-sint-of-sint-from-sshort
      ullong-from-sint-of-sint-from-ushort)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-get-rules
  :short "Rules about the composition of @(tsee sint->get)
          with @('sint-from-<type>') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules used during the symbolic execution."))

  (defruled sint->get-of-sint-from-schar
    (implies (scharp x)
             (equal (sint->get (sint-from-schar x))
                    (schar->get x)))
    :enable (sint-from-schar
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-uchar
    (implies (ucharp x)
             (equal (sint->get (sint-from-uchar x))
                    (uchar->get x)))
    :enable (sint-from-uchar
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-sshort
    (implies (sshortp x)
             (equal (sint->get (sint-from-sshort x))
                    (sshort->get x)))
    :enable (sint-from-sshort
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-ushort
    (implies (ushortp x)
             (equal (sint->get (sint-from-ushort x))
                    (ushort->get x)))
    :enable (sint-from-ushort
             sint-integerp-alt-def))

  (defval *atc-sint-get-rules*
    '(sint->get-of-sint-from-schar
      sint->get-of-sint-from-uchar
      sint->get-of-sint-from-sshort
      sint->get-of-sint-from-ushort)))
