; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/utilities/bytes-as-digits" :dir :system)

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

  (defrule car-of-byte-list-fix
    (implies (consp x)
             (equal (car (byte-list-fix x))
                    (byte-fix (car x)))))

  (defrule cdr-of-byte-list-fix
    (equal (cdr (byte-list-fix x))
           (byte-list-fix (cdr x))))

  (defcong byte-list-equiv byte-list-equiv (append x y) 1)

  (defcong byte-list-equiv byte-list-equiv (append x y) 2))
