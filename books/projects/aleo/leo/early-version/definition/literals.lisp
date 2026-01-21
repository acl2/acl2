; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "characters")
(include-book "addresses")
(include-book "bit-sizes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ literals
  :parents (abstract-syntax)
  :short "Leo literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize an abstract syntactic representation
     of all the Leo literals."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum coordinate
  :short "Fixtype of Leo group literal coordinates."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo supports a notation for affine group literals @('(<x>, <y>)group'),
     where each of @('<x>') and @('<y>') can be
     either an integer that specifies the coordinate,
     or an indication that the coordinate should be derived
     from the other coordinate so that the point is on the curve.
     The latter indication is of three possible kinds:
     sign high (i.e. take the value with the high sign),
     sign low (i.e. take the value with the low sign),
     or inferred (i.e. try sign high and sign low)."))
  (:explicit ((get int)))
  (:sign-high ())
  (:sign-low ())
  (:inferred ())
  :pred coordinatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult coordinate-result
  :short "Fixtype of errors and Leo coordinates."
  :ok coordinate
  :pred coordinate-resultp
  :prepwork ((local (in-theory (e/d (coordinate-kind) (coordinatep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum group-literal
  :short "Fixtype of Leo group literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo supports a rich notation for literals representing
     points of an elliptic curve group.
     Besides the affine notation described in @(tsee coordinate),
     it also supports the product notation @('<n>group'),
     where @('<n>') is a natural number:
     this means the point obtained by multiplying the generator point
     by the natural number @('<n>');
     in particular, @('0group') is the group identity
     (the point at infinity for certain curves),
     and @('1group') is the generator point.")
   (xdoc::p
    "In an affine notation, at least one coordinate must be an explicit integer.
     We delegate this constraint to the static and dynamic semantics."))
  (:affine ((x coordinate)
            (y coordinate)))
  (:product ((factor nat)))
  :pred group-literalp
  :xvar lit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult group-literal-result
  :short "Fixtype of errors and Leo group literals."
  :ok group-literal
  :pred group-literal-resultp
  :prepwork ((local (in-theory (e/d (group-literal-kind) (group-literalp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal
  :short "Fixtype of Leo literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer literals are typed.
     They are unsigned or signed, and they have a bit size.
     The value is always a natural number;
     negative integers are represented as unary negations of signed literals.")
   (xdoc::p
    "String literals consist of lists of characters.
     Currently there is no character literal but we
     continue to use @(tsee char) to represent string elements.")
   (xdoc::p
    "Field literals represent elements of the @('field') type,
     which are natural numbers below the base prime.
     We allow any natural number here,
     which denotes the field element obtained by reducing modulo the prime.")
   (xdoc::p
    "Group literals are described in @(tsee group-literal).")
   (xdoc::p
    "Scalar literals represent elements of the @('scalar') type,
     which are natural numbers below the scalar prime.
     We allow any natural number here,
     which denotes the field element obtained by reducing modulo the prime."))
  (:bool ((val bool)))
  (:unsigned ((val nat)
              (size bitsize)))
  (:signed ((val nat)
            (size bitsize)))
  (:string ((get char-list)))
  (:address ((get address)))
  (:field ((val nat)))
  (:group ((get group-literal)))
  (:scalar ((val nat)))
  :pred literalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult literal-result
  :short "Fixtype of errors and Leo literals."
  :ok literal
  :pred literal-resultp
  :prepwork ((local (in-theory (e/d (literal-kind) (literalp))))))
