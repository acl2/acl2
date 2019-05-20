; Representation of Natural Numbers as Digits in Base 2^4
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defbytelist-standard-instances" :dir :system)
(include-book "pow2")
(include-book "defthm-dab-return-types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dab-digit-listp-of-16-rewrite-ubyte4-listp
  (equal (dab-digit-listp 16 x)
         (ubyte4-listp x))
  :enable (dab-digit-listp dab-digitp ubyte4-listp ubyte4p))

(defthm-dab-return-types
  dab-digit-listp-of-16-rewrite-ubyte4-listp
  ubyte4-listp-of
  :topic digit-ubyte4-return-types
  :parents (digits-any-base-pow2)
  :short "Additional return type theorems for conversions of natural numbers
          to digits in base 16, with @(tsee ubyte4-listp).")
