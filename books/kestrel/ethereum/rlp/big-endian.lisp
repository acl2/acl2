; Ethereum -- RLP Big Endian Representations
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/digits-any-base/core" :dir :system)

(include-book "../basics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rlp-big-endian-representations
  :parents (rlp)
  :short "Big-endian representation of scalars in RLP."
  :long
  (xdoc::topstring
   (xdoc::p
    "The library function @(tsee nat=>bendian*),
     when the @('base') argument is 256,
     corresponds to @($\\mathtt{BE}$) [YP:(181)].
     Note that no leading 0 is allowed, even for representing 0,
     which is thus represented by the empty list of digits.")
   (xdoc::p
    "Digits in base 256 are bytes.
     We introduce return type theorems for @(tsee nat=>bendian*)
     (and for the other number-to-digit conversions,
     even though we do not use them here)."))

  (defruled dab-digit-listp-of-256-is-byte-listp
    (equal (acl2::dab-digit-listp 256 digits)
           (byte-listp digits))
    :enable (acl2::dab-digit-listp acl2::dab-digitp byte-listp bytep))

  (acl2::defthm-dab-return-types
   dab-digit-listp-of-256-is-byte-listp
   byte-listp-of))
