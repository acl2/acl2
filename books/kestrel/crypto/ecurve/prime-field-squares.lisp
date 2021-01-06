; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk pfield-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (elliptic-curves)
  :short "Check if a prime field element is a square."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is more general than elliptic curve libraries,
     but it finds some uses in elliptic curves over prime fields
     (perhaps this should be moved to the prime field library).
     We non-constructively check whether there exists
     a square root in the prime field.
     The witness function returns a root, if one exists."))
  (exists (r) (and (fep r p)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->root)
