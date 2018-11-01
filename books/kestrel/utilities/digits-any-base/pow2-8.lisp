; Representation of Natural Numbers as Digits in Base 2^8
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/fixbytes/ubyte8-list" :dir :system)
(include-book "pow2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dab-digit-listp-of-256-rewrite-ubyte8-listp
  (equal (dab-digit-listp 256 x)
         (ubyte8-listp x))
  :enable (dab-digit-listp dab-digitp ubyte8-listp ubyte8p))

(defthm-dab-return-types
  dab-digit-listp-of-256-rewrite-ubyte8-listp
  ubyte8-listp-of
  :topic digit-ubyte8-return-types
  :parents (digits-any-base-pow2)
  :short "Additional return type theorems for conversions of natural numbers
          to digits in base 256, with @(tsee ubyte8-listp).")
