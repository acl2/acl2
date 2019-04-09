; Bitcoin -- Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "kestrel/utilities/digits-any-base/core" :dir :system)
(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bytes
  :parents (bitcoin)
  :short "Bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Bitcoin, as in most modern contexts,
     the unqualified term `byte' denotes an unsigned 8-bit byte.")
   (xdoc::p
    "We use the library type @(tsee byte)
     to model bytes in our Bitcoin model."))

  (defrule natp-of-byte-fix
    (natp (byte-fix x))
    :rule-classes :type-prescription
    :enable byte-fix)

  (defrule byte-fix-upper-bound
    (< (byte-fix x) 256)
    :rule-classes :linear
    :enable (byte-fix bytep))

  (defruled byte-fix-rewrite-dab-digit-fix-256
    (equal (byte-fix digits)
           (dab-digit-fix 256 digits))
    :enable (byte-fix dab-digit-fix dab-digitp bytep))

  (defruled byte-fix-rewrite-unsigned-byte-fix
    (equal (byte-fix x)
           (unsigned-byte-fix 8 x))
    :enable (byte-fix bytep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection byte-sequences
  :parents (bytes)
  :short "Byte sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are finite lists of bytes,
     which model byte arrays in particular.")
   (xdoc::p
    "We use the library type @(tsee byte-list)
     to model byte sequences in our Bitcoin model."))

  (defrule nat-listp-when-byte-listp
    (implies (byte-listp bytes)
             (nat-listp bytes)))

  (defruled dab-digit-listp-of-256-rewrite-byte-listp
    (equal (dab-digit-listp 256 x)
           (byte-listp x))
    :enable (dab-digit-listp dab-digitp byte-listp bytep))

  (defthm-dab-return-types
    dab-digit-listp-of-256-rewrite-byte-listp
    byte-listp-of)

  (defrule car-of-byte-list-fix
    (implies (consp x)
             (equal (car (byte-list-fix x))
                    (byte-fix (car x)))))

  (defrule cdr-of-byte-list-fix
    (equal (cdr (byte-list-fix x))
           (byte-list-fix (cdr x))))

  (defruled byte-list-fix-rewrite-dab-digit-list-fix-256
    (equal (byte-list-fix digits)
           (dab-digit-list-fix 256 digits))
    :enable (dab-digit-list-fix
             byte-list-fix
             byte-fix-rewrite-dab-digit-fix-256))

  (defruled byte-list-fix-rewrite-unsigned-byte-list-fix
    (equal (byte-list-fix x)
           (unsigned-byte-list-fix 8 x))
    :enable (byte-fix-rewrite-unsigned-byte-fix
             unsigned-byte-list-fix))

  (defcong byte-list-equiv byte-list-equiv (append x y) 1)

  (defcong byte-list-equiv byte-list-equiv (append x y) 2))
