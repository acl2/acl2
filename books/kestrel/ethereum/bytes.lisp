; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "kestrel/fty/byte-list20" :dir :system)
(include-book "kestrel/fty/byte-list32" :dir :system)
(include-book "kestrel/fty/byte-list64" :dir :system)
(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bytes
  :parents (basics)
  :short "Bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[YP:B] describes @($\\mathbb{O}$) as the set of 8-bit bytes.
     We use the library type @(tsee byte) to model @($\\mathbb{O}$)."))

  (defrule natp-of-byte-fix
    (natp (byte-fix x))
    :rule-classes :type-prescription
    :enable byte-fix)

  (defrule byte-fix-upper-bound
    (< (byte-fix x) 256)
    :rule-classes :linear
    :enable (byte-fix bytep))

  (defruled byte-fix-rewrite-unsigned-byte-fix
    (equal (byte-fix x)
           (unsigned-byte-fix 8 x))
    :enable (byte-fix bytep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection byte-arrays
  :parents (basics)
  :short "Byte arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "[YP:3] mentions the set @($\\mathbb{B}$) of byte arrays,
     and [YP:(178)] defines it as consisting of all finite sequences of bytes.
     We use the library type @(tsee byte-list) to model @($\\mathbb{B}$).")
   (xdoc::p
    "[YP:3] also introduces the notation @($\\mathbb{B}_k$) to denote
     the set of byte arrays of length @($k$).
     We use the library types
     @(tsee byte-list20), @(tsee byte-list32), and @(tsee byte-list64)
     to model @($\\mathbb{B}_k$) for @($k\\in\\{20,32,64\\}$).
     Arrays of 20 bytes may represent addresses [YP:4.1].
     Arrays of 32 bytes may represent Keccak-256 hashes.
     Arrays of 64 bytes may represent Keccak-512 hashes."))

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

  (defruled byte-list-fix-rewrite-unsigned-byte-list-fix
    (equal (byte-list-fix x)
           (unsigned-byte-list-fix 8 x))
    :enable (byte-fix-rewrite-unsigned-byte-fix
             unsigned-byte-list-fix)))
