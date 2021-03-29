; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-conversions
  :parents (atc-integers)
  :short "A model of C integer conversions for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 functions that convert
     between values of different C integer types.
     In the ACL2 representation of C code for ATC,
     these conversions are necessary,
     because the ACL2 representations of different C integer types
     are disjoint, i.e. there are no automatic inclusions.
     However, under appropriate conditions,
     ATC can translate these conversions in ACL2 to no-ops in C,
     e.g. if an @('unsigned char') is used as an operand of binary addition,
     no explicit conversion is necessary in C
     due to the usual arithmetic conversions [C:6.3.1.8]
     that happen automatically.")
   (xdoc::p
    "We start by defining conversions between @('unsigned char') to @('int'),
     which are the two C types that we currently model.
     We will add more, as needed, as we add models for more C types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-from-uchar ((x ucharp))
  :returns (y sintp)
  :short "Convert an @('unsigned char') to an @('int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [C:6.3.1.3/1], the value is unchanged.
     Thus, we simply unwrap and rewrap the underlying ACL2 integer."))
  (sint (uchar->get x))
  :guard-hints (("Goal" :in-theory (enable sint-integerp-alt-def
                                           acl2::ubyte8p
                                           ucharp
                                           uchar->get)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-from-sint ((x sintp))
  :returns (y ucharp)
  :short "Convert an @('int') to an @('unsigned char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [C:6.3.1.3/2], the value is obtained by
     repeatedly adding or subtracting 256
     (i.e. one plus the maximum @('unsigned char') value)
     until the result is representable in @('unsigned char').
     This repeated addition or subtraction
     is equivalent to taking the initial value modulo 256."))
  (uchar (mod (sint->get x) 256))
  :guard-hints (("Goal" :in-theory (enable acl2::ubyte8p)))
  :hooks (:fix)
  :prepwork
  ((local (include-book "kestrel/arithmetic-light/mod" :dir :system))))
