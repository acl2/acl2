; Representation of Natural Numbers as Digits in Base 2^2
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

(defruled dab-digit-listp-of-4-rewrite-ubyte2-listp
  (equal (dab-digit-listp 4 x)
         (ubyte2-listp x))
  :enable (dab-digit-listp dab-digitp ubyte2-listp ubyte2p))

(defthm-dab-return-types
  dab-digit-listp-of-4-rewrite-ubyte2-listp
  ubyte2-listp-of
  :topic digit-ubyte2-return-types
  :parents (digits-any-base-pow2)
  :short "Additional return type theorems for conversions of natural numbers
          to digits in base 4, with @(tsee ubyte2-listp).")
