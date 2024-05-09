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

(include-book "../../language/static-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-adjust-type-rules
  :short "Rules for @(tsee adjust-type)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These serve to adjust types
     when building the initial scope of a function."))

  (defruled adjust-type-of-type-array-of-type-schar
    (equal (adjust-type (type-array (type-schar) size))
           (type-pointer (type-schar)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-uchar
    (equal (adjust-type (type-array (type-uchar) size))
           (type-pointer (type-uchar)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-sshort
    (equal (adjust-type (type-array (type-sshort) size))
           (type-pointer (type-sshort)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-ushort
    (equal (adjust-type (type-array (type-ushort) size))
           (type-pointer (type-ushort)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-sint
    (equal (adjust-type (type-array (type-sint) size))
           (type-pointer (type-sint)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-uint
    (equal (adjust-type (type-array (type-uint) size))
           (type-pointer (type-uint)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-slong
    (equal (adjust-type (type-array (type-slong) size))
           (type-pointer (type-slong)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-ulong
    (equal (adjust-type (type-array (type-ulong) size))
           (type-pointer (type-ulong)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-sllong
    (equal (adjust-type (type-array (type-sllong) size))
           (type-pointer (type-sllong)))
    :enable adjust-type)

  (defruled adjust-type-of-type-array-of-type-ullong
    (equal (adjust-type (type-array (type-ullong) size))
           (type-pointer (type-ullong)))
    :enable adjust-type)

  (defruled adjust-type-of-type-schar
    (equal (adjust-type (type-schar))
           (type-schar))
    :enable adjust-type)

  (defruled adjust-type-of-type-uchar
    (equal (adjust-type (type-uchar))
           (type-uchar))
    :enable adjust-type)

  (defruled adjust-type-of-type-sshort
    (equal (adjust-type (type-sshort))
           (type-sshort))
    :enable adjust-type)

  (defruled adjust-type-of-type-ushort
    (equal (adjust-type (type-ushort))
           (type-ushort))
    :enable adjust-type)

  (defruled adjust-type-of-type-sint
    (equal (adjust-type (type-sint))
           (type-sint))
    :enable adjust-type)

  (defruled adjust-type-of-type-uint
    (equal (adjust-type (type-uint))
           (type-uint))
    :enable adjust-type)

  (defruled adjust-type-of-type-slong
    (equal (adjust-type (type-slong))
           (type-slong))
    :enable adjust-type)

  (defruled adjust-type-of-type-ulong
    (equal (adjust-type (type-ulong))
           (type-ulong))
    :enable adjust-type)

  (defruled adjust-type-of-type-sllong
    (equal (adjust-type (type-sllong))
           (type-sllong))
    :enable adjust-type)

  (defruled adjust-type-of-type-ullong
    (equal (adjust-type (type-ullong))
           (type-ullong))
    :enable adjust-type)

  (defruled adjust-type-of-type-struct
    (equal (adjust-type (type-struct tag))
           (type-struct tag))
    :enable adjust-type)

  (defruled adjust-type-of-type-pointer
    (equal (adjust-type (type-pointer type))
           (type-pointer type))
    :enable adjust-type)

  (defval *atc-adjust-type-rules*
    '(adjust-type-of-type-array-of-type-schar
      adjust-type-of-type-array-of-type-uchar
      adjust-type-of-type-array-of-type-sshort
      adjust-type-of-type-array-of-type-ushort
      adjust-type-of-type-array-of-type-sint
      adjust-type-of-type-array-of-type-uint
      adjust-type-of-type-array-of-type-slong
      adjust-type-of-type-array-of-type-ulong
      adjust-type-of-type-array-of-type-sllong
      adjust-type-of-type-array-of-type-ullong
      adjust-type-of-type-schar
      adjust-type-of-type-uchar
      adjust-type-of-type-sshort
      adjust-type-of-type-ushort
      adjust-type-of-type-sint
      adjust-type-of-type-uint
      adjust-type-of-type-slong
      adjust-type-of-type-ulong
      adjust-type-of-type-sllong
      adjust-type-of-type-ullong
      adjust-type-of-type-struct
      adjust-type-of-type-pointer)))
