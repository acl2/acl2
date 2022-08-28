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

(include-book "../../language/integer-operations")

(include-book "../integer-conversions")

(include-book "integers")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-convert-integer-value-rules
  :short "Rules about @(tsee convert-integer-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These turn calls of @(tsee convert-integer-value)
     into calls of @('<type1>-from-<type2>').")
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules
     used during the symbolic execution."))

  (local (in-theory (enable convert-integer-value
                            value-integer
                            value-integer->get
                            integer-type-rangep
                            integer-type-min
                            integer-type-max
                            ;; shallowly embedded conversions:
                            sint-from-schar
                            slong-from-schar
                            sllong-from-schar
                            uint-from-schar
                            ulong-from-schar
                            ullong-from-schar
                            sint-from-uchar
                            slong-from-uchar
                            sllong-from-uchar
                            uint-from-uchar
                            ulong-from-uchar
                            ullong-from-uchar
                            sint-from-sshort
                            slong-from-sshort
                            sllong-from-sshort
                            uint-from-sshort
                            ulong-from-sshort
                            ullong-from-sshort
                            sint-from-ushort
                            slong-from-ushort
                            sllong-from-ushort
                            uint-from-ushort
                            ulong-from-ushort
                            ullong-from-ushort
                            slong-from-sint
                            sllong-from-sint
                            uint-from-sint
                            ulong-from-sint
                            ullong-from-sint
                            slong-from-uint
                            sllong-from-uint
                            ulong-from-uint
                            ullong-from-uint
                            ulong-from-slong
                            sllong-from-slong
                            ullong-from-slong
                            sllong-from-ulong
                            ullong-from-ulong
                            ullong-from-sllong
                            ;; modular unsigned constructors:
                            uint-mod
                            ulong-mod
                            ullong-mod
                            ;; bridge rules for destructors:
                            value-schar->get-to-schar->get
                            value-uchar->get-to-uchar->get
                            value-sshort->get-to-sshort->get
                            value-ushort->get-to-ushort->get
                            value-sint->get-to-sint->get
                            value-uint->get-to-uint->get
                            value-slong->get-to-slong->get
                            value-ulong->get-to-ulong->get
                            value-sllong->get-to-sllong->get
                            value-ullong->get-to-ullong->get
                            ;; bridge rules for constructors:
                            value-sint-to-sint
                            value-slong-to-slong
                            value-sllong-to-sllong
                            value-uint-to-uint
                            value-ulong-to-ulong
                            value-ullong-to-ullong)))

  ;; from schar:

  (defruled convert-integer-value-of-schar-and-sint
    (implies (and (scharp val)
                  (equal type (type-sint)))
             (equal (convert-integer-value val type)
                    (sint-from-schar val))))

  (defruled convert-integer-value-of-schar-and-slong
    (implies (and (scharp val)
                  (equal type (type-slong)))
             (equal (convert-integer-value val type)
                    (slong-from-schar val))))

  (defruled convert-integer-value-of-schar-and-sllong
    (implies (and (scharp val)
                  (equal type (type-sllong)))
             (equal (convert-integer-value val type)
                    (sllong-from-schar val))))

  (defruled convert-integer-value-of-schar-and-uint
    (implies (and (scharp val)
                  (equal type (type-uint)))
             (equal (convert-integer-value val type)
                    (uint-from-schar val))))

  (defruled convert-integer-value-of-schar-and-ulong
    (implies (and (scharp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-schar val))))

  (defruled convert-integer-value-of-schar-and-ullong
    (implies (and (scharp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-schar val))))

  ;; from uchar:

  (defruled convert-integer-value-of-uchar-and-sint
    (implies (and (ucharp val)
                  (equal type (type-sint))
                  (<= (uchar-max) (sint-max)))
             (equal (convert-integer-value val type)
                    (sint-from-uchar val))))

  (defruled convert-integer-value-of-uchar-and-slong
    (implies (and (ucharp val)
                  (equal type (type-slong))
                  (<= (uchar-max) (slong-max)))
             (equal (convert-integer-value val type)
                    (slong-from-uchar val))))

  (defruled convert-integer-value-of-uchar-and-sllong
    (implies (and (ucharp val)
                  (equal type (type-sllong))
                  (<= (uchar-max) (sllong-max)))
             (equal (convert-integer-value val type)
                    (sllong-from-uchar val))))

  (defruled convert-integer-value-of-uchar-and-uint
    (implies (and (ucharp val)
                  (equal type (type-uint)))
             (equal (convert-integer-value val type)
                    (uint-from-uchar val))))

  (defruled convert-integer-value-of-uchar-and-ulong
    (implies (and (ucharp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-uchar val))))

  (defruled convert-integer-value-of-uchar-and-ullong
    (implies (and (ucharp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-uchar val))))

  ;; from sshort:

  (defruled convert-integer-value-of-sshort-and-sint
    (implies (and (sshortp val)
                  (equal type (type-sint)))
             (equal (convert-integer-value val type)
                    (sint-from-sshort val))))

  (defruled convert-integer-value-of-sshort-and-slong
    (implies (and (sshortp val)
                  (equal type (type-slong)))
             (equal (convert-integer-value val type)
                    (slong-from-sshort val))))

  (defruled convert-integer-value-of-sshort-and-sllong
    (implies (and (sshortp val)
                  (equal type (type-sllong)))
             (equal (convert-integer-value val type)
                    (sllong-from-sshort val))))

  (defruled convert-integer-value-of-sshort-and-uint
    (implies (and (sshortp val)
                  (equal type (type-uint)))
             (equal (convert-integer-value val type)
                    (uint-from-sshort val))))

  (defruled convert-integer-value-of-sshort-and-ulong
    (implies (and (sshortp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-sshort val))))

  (defruled convert-integer-value-of-sshort-and-ullong
    (implies (and (sshortp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-sshort val))))

  ;; from ushort:

  (defruled convert-integer-value-of-ushort-and-sint
    (implies (and (ushortp val)
                  (equal type (type-sint))
                  (<= (ushort-max) (sint-max)))
             (equal (convert-integer-value val type)
                    (sint-from-ushort val))))

  (defruled convert-integer-value-of-ushort-and-slong
    (implies (and (ushortp val)
                  (equal type (type-slong))
                  (<= (ushort-max) (slong-max)))
             (equal (convert-integer-value val type)
                    (slong-from-ushort val))))

  (defruled convert-integer-value-of-ushort-and-sllong
    (implies (and (ushortp val)
                  (equal type (type-sllong))
                  (<= (ushort-max) (sllong-max)))
             (equal (convert-integer-value val type)
                    (sllong-from-ushort val))))

  (defruled convert-integer-value-of-ushort-and-uint
    (implies (and (ushortp val)
                  (equal type (type-uint)))
             (equal (convert-integer-value val type)
                    (uint-from-ushort val))))

  (defruled convert-integer-value-of-ushort-and-ulong
    (implies (and (ushortp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-ushort val))))

  (defruled convert-integer-value-of-ushort-and-ullong
    (implies (and (ushortp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-ushort val))))

  ;; from sint:

  (defruled convert-integer-value-of-sint-and-slong
    (implies (and (sintp val)
                  (equal type (type-slong)))
             (equal (convert-integer-value val type)
                    (slong-from-sint val))))

  (defruled convert-integer-value-of-sint-and-sllong
    (implies (and (sintp val)
                  (equal type (type-sllong)))
             (equal (convert-integer-value val type)
                    (sllong-from-sint val))))

  (defruled convert-integer-value-of-sint-and-uint
    (implies (and (sintp val)
                  (equal type (type-uint)))
             (equal (convert-integer-value val type)
                    (uint-from-sint val))))

  (defruled convert-integer-value-of-sint-and-ulong
    (implies (and (sintp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-sint val))))

  (defruled convert-integer-value-of-sint-and-ullong
    (implies (and (sintp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-sint val))))

  ;; from uint:

  (defruled convert-integer-value-of-uint-and-slong
    (implies (and (uintp val)
                  (equal type (type-slong))
                  (<= (uint-max) (slong-max)))
             (equal (convert-integer-value val type)
                    (slong-from-uint val))))

  (defruled convert-integer-value-of-uint-and-sllong
    (implies (and (uintp val)
                  (equal type (type-sllong))
                  (<= (uint-max) (sllong-max)))
             (equal (convert-integer-value val type)
                    (sllong-from-uint val))))

  (defruled convert-integer-value-of-uint-and-ulong
    (implies (and (uintp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-uint val))))

  (defruled convert-integer-value-of-uint-and-ullong
    (implies (and (uintp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-uint val))))

  ;; from slong:

  (defruled convert-integer-value-of-slong-and-sllong
    (implies (and (slongp val)
                  (equal type (type-sllong)))
             (equal (convert-integer-value val type)
                    (sllong-from-slong val))))

  (defruled convert-integer-value-of-slong-and-ulong
    (implies (and (slongp val)
                  (equal type (type-ulong)))
             (equal (convert-integer-value val type)
                    (ulong-from-slong val))))

  (defruled convert-integer-value-of-slong-and-ullong
    (implies (and (slongp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-slong val))))

  ;; from ulong:

  (defruled convert-integer-value-of-ulong-and-sllong
    (implies (and (ulongp val)
                  (equal type (type-sllong))
                  (<= (ulong-max) (sllong-max)))
             (equal (convert-integer-value val type)
                    (sllong-from-ulong val))))

  (defruled convert-integer-value-of-ulong-and-ullong
    (implies (and (ulongp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-ulong val))))

  ;; from sllong:

  (defruled convert-integer-value-of-sllong-and-ullong
    (implies (and (sllongp val)
                  (equal type (type-ullong)))
             (equal (convert-integer-value val type)
                    (ullong-from-sllong val))))

  ;; all the rules:

  (defval *atc-convert-integer-value-rules*
    '(convert-integer-value-of-schar-and-sint
      convert-integer-value-of-schar-and-slong
      convert-integer-value-of-schar-and-sllong
      convert-integer-value-of-schar-and-uint
      convert-integer-value-of-schar-and-ulong
      convert-integer-value-of-schar-and-ullong
      convert-integer-value-of-uchar-and-sint
      convert-integer-value-of-uchar-and-slong
      convert-integer-value-of-uchar-and-sllong
      convert-integer-value-of-uchar-and-uint
      convert-integer-value-of-uchar-and-ulong
      convert-integer-value-of-uchar-and-ullong
      convert-integer-value-of-sshort-and-sint
      convert-integer-value-of-sshort-and-slong
      convert-integer-value-of-sshort-and-sllong
      convert-integer-value-of-sshort-and-uint
      convert-integer-value-of-sshort-and-ulong
      convert-integer-value-of-sshort-and-ullong
      convert-integer-value-of-ushort-and-sint
      convert-integer-value-of-ushort-and-slong
      convert-integer-value-of-ushort-and-sllong
      convert-integer-value-of-ushort-and-uint
      convert-integer-value-of-ushort-and-ulong
      convert-integer-value-of-ushort-and-ullong
      convert-integer-value-of-sint-and-slong
      convert-integer-value-of-sint-and-sllong
      convert-integer-value-of-sint-and-uint
      convert-integer-value-of-sint-and-ulong
      convert-integer-value-of-sint-and-ullong
      convert-integer-value-of-uint-and-slong
      convert-integer-value-of-uint-and-sllong
      convert-integer-value-of-uint-and-ulong
      convert-integer-value-of-uint-and-ullong
      convert-integer-value-of-slong-and-sllong
      convert-integer-value-of-slong-and-ulong
      convert-integer-value-of-slong-and-ullong
      convert-integer-value-of-ulong-and-sllong
      convert-integer-value-of-ulong-and-ullong
      convert-integer-value-of-sllong-and-ullong)))
