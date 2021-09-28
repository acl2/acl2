; Elliptic Curve Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield-squarep-of-0
  (implies (posp p)
           (pfield-squarep 0 p))
  :enable fep
  :use (:instance pfield-squarep-suff (r 0) (x 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield-squarep-of-1
  (implies (and (posp p)
                (> p 1))
           (pfield-squarep 1 p))
  :enable fep
  :prep-books ((include-book "arithmetic-5/top" :dir :system))
  :use (:instance pfield-squarep-suff (r 1) (x 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule fep-of-pfield-square->root
  (implies (pfield-squarep x p)
           (fep (pfield-square->root x p) p))
  :enable pfield-squarep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule natp-of-pfield-square->root
  (implies (pfield-squarep x p)
           (natp (pfield-square->root x p)))
  :rule-classes (:type-prescription :rewrite)
  :enable pfield-squarep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Odd and even square roots.

(define-sk pfield-odd-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (elliptic-curves)
  :short "Check if a prime field element is a square of an odd field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as pfield-squarep except restricts the root to be odd."))
  (exists (r) (and (fep r p)
                   (oddp r)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->odd-root)

(define-sk pfield-even-squarep (x p)
  :guard (and (integerp p) (fep x p))
  :returns (yes/no booleanp)
  :parents (elliptic-curves)
  :short "Check if a prime field element is a square of an even field element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same as pfield-squarep except restricts the root to be even."))
  (exists (r) (and (fep r p)
                   (evenp r)
                   (equal (mul r r p) x)))
  :skolem-name pfield-square->even-root)
