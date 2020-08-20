; Solidity Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOLIDITY")

(include-book "sld-refs")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "kestrel/utilities/signed-byte-fixing" :dir :system)
(include-book "kestrel/utilities/unsigned-byte-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-values
  :parents (values)
  :short (xdoc::topstring "Integer values " xdoc::*sld-types-integers* ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the values of the types
     @('uint8') to @('uint256') and @('int8') to @('int256')
     where the numbers go in increments of 8.")
   (xdoc::p
    "First we introduce a fixtype of the 32 possible sizes of those types,
     and then we introduce two fixtypes for unsigned and signed integers.
     The values of the latter two fixtypes carry their own size.
     These two fixtypes consist of the sets of values
     of all the the unsigned or signed integer types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bit-size
  :short "Fixtype of sizes in bits of the integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the integer multiples of 8 from 8 to 256.")
   (xdoc::p
    "This is a type defined by @(tsee fty::deffixtype)."))

  (define bit-size-p (x)
    :returns (yes/no booleanp)
    :parents (bit-size)
    :short "Recognizer for @(tsee bit-size)."
    (and (integerp x)
         (integerp (/ x 8))
         (<= 8 x)
         (<= x 256))
    :no-function t
    ///

    (defruled bit-size-p-alt-def
      (iff (bit-size-p x)
           (member x (list 8 16 24 32 40 48 56 64
                           72 80 88 96 104 112 120 128
                           136 144 152 160 168 176 184 192
                           200 208 216 224 232 240 248 256)))
      :cases ((equal (/ x 8) 1)
              (equal (/ x 8) 2)
              (equal (/ x 8) 3)
              (equal (/ x 8) 4)
              (equal (/ x 8) 5)
              (equal (/ x 8) 6)
              (equal (/ x 8) 7)
              (equal (/ x 8) 8)
              (equal (/ x 8) 9)
              (equal (/ x 8) 10)
              (equal (/ x 8) 11)
              (equal (/ x 8) 12)
              (equal (/ x 8) 13)
              (equal (/ x 8) 14)
              (equal (/ x 8) 15)
              (equal (/ x 8) 16)
              (equal (/ x 8) 17)
              (equal (/ x 8) 18)
              (equal (/ x 8) 19)
              (equal (/ x 8) 20)
              (equal (/ x 8) 21)
              (equal (/ x 8) 22)
              (equal (/ x 8) 23)
              (equal (/ x 8) 24)
              (equal (/ x 8) 25)
              (equal (/ x 8) 26)
              (equal (/ x 8) 27)
              (equal (/ x 8) 28)
              (equal (/ x 8) 29)
              (equal (/ x 8) 30)
              (equal (/ x 8) 31))))

  (std::deffixer bit-size-fix
    :pred bit-size-p
    :body-fix 256
    :parents (bit-size)
    :short "Fixer for @(tsee bit-size).")

  (defrule posp-of-bit-size-fix
    (posp (bit-size-fix x))
    :rule-classes :type-prescription
    :enable (bit-size-fix bit-size-p))

  (fty::deffixtype bit-size
    :pred bit-size-p
    :fix bit-size-fix
    :equiv bit-size-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uint
  :short "Fixtype of unsigned integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We tag unsigned integer values with their bit sizes,
     since the sizes are part of their types."))
  ((size bit-size)
   (value acl2::nat :reqfix (unsigned-byte-fix size value)))
  :require (unsigned-byte-p size value)
  :layout :list
  :tag :uint
  :pred uintp
  :prepwork ((local (include-book "arithmetic/top" :dir :system)))
  ///

  (defrule uint->size-lower-bound
    (>= (uint->size x) 8)
    :rule-classes :linear
    :enable (uint->size
             bit-size-p
             bit-size-fix))

  (defrule uint->size-upper-bound
    (<= (uint->size x) 256)
    :rule-classes :linear
    :enable (uint->size
             bit-size-p
             bit-size-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int
  :short "Fixtype of signed integer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We tag unsigned integer values with their bit sizes,
     since the sizes are part of their types."))
  ((size bit-size)
   (value acl2::int :reqfix (signed-byte-fix size value)))
  :require (signed-byte-p size value)
  :layout :list
  :tag :int
  :pred intp
  :prepwork ((local (include-book "arithmetic/top" :dir :system)))
  ///

  (defrule int->size-lower-bound
    (>= (int->size x) 8)
    :rule-classes :linear
    :enable (int->size
             bit-size-p
             bit-size-fix))

  (defrule int->size-upper-bound
    (<= (int->size x) 256)
    :rule-classes :linear
    :enable (int->size
             bit-size-p
             bit-size-fix)))
