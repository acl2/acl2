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

(include-book "literals")
(include-book "values")
(include-book "field-arithmetic-operations")
(include-book "group-arithmetic-operations")
(include-book "scalar-arithmetic-operations")

(include-book "kestrel/crypto/ecurve/points-fty" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ literal-evaluation
  :parents (dynamic-semantics literals)
  :short "Evaluation of Leo literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo literals represent Leo values fairly directly.
     The only complication is with group literals
     with non-explicit coordinates,
     i.e. where one coordinate is determined from the other
     according to certain rules.")
   (xdoc::p
    "In any case, the semantics of Leo literals
     can be formalized via a function that evaluates literals to values.
     More precisely, the evaluation of literals may fail,
     in which case we return @('nil') as an error indication,
     in line with our defensive semantics of Leo."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-group-literal ((lit group-literalp) (curve curvep))
  :returns (result value-optionp)
  :short "Evaluate a Leo group element literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only formalize the evaluation of
     pairs with explicit coordinates
     and scalar multiplications of the generator.
     We will add derivation of coordinates later;
     for now we return @('nil') on pairs with derived coordinates,
     where in this case @('nil') does not indicate error
     but lack of support.
     (We should probably differentiate these two kinds of errors eventually.)")
   (xdoc::p
    "Like the group arithmetic operations depend on an elliptic curve,
     so does the evaluation of group element literals.")
   (xdoc::p
    "For a pair (with explicit coordinates),
     we ensure that the point is in the subgroup;
     otherwise, we return @('nil') as a defensive error indication.
     For a scalar multiplication of the generator,
     we know that the point is on the curve because the generator is,
     but for now we do not have a proof readily available yet,
     and thus we perform the check."))
  (group-literal-case
   lit
   :affine (if (and (coordinate-case lit.x :explicit)
                    (coordinate-case lit.y :explicit))
               (b* ((p (curve-base-prime curve))
                    (x (mod (coordinate-explicit->get lit.x) p))
                    (y (mod (coordinate-explicit->get lit.y) p))
                    (point (ecurve::point-finite x y)))
                 (and (curve-subgroupp point curve)
                      (value-group point)))
             nil)
   :product (b* ((gen (curve-generator curve))
                 (k (mod lit.factor (curve-scalar-prime curve)))
                 ((mv okp point) (curve-subgroup-mul k gen curve))
                 ((unless okp) nil))
              (value-group point)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-literal ((lit literalp) (curve curvep))
  :returns (result value-optionp)
  :short "Evaluate a Leo literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Evaluating a boolean literal is straighforward.")
   (xdoc::p
    "Evaluating an unsigned or signed integer literal
     involves checking that the number is representable in the bit size,
     returning @('nil') (to indicate error) if not.")
   (xdoc::p
    "Evaluating a string literal is straightforward.")
   (xdoc::p
    "Evaluating an address literal is straightforward.")
   (xdoc::p
    "Evaluating a field element literal is
     with respect to a prime number that defines the prime field,
     in the same way that the "
    (xdoc::seetopic "field-arithmetic-operations" "field arithmetic operations")
    " are defined with respect to a prime.
     Any integer (including negative ones) is allowed
     in a field element literal:
     it is coerced into an element of the prime field via modular reduction.")
   (xdoc::p
    "The evaluation of group element literals
     is formalized by @(tsee eval-group-literal).")
   (xdoc::p
    "Evaluating a scalar literal is similar to a field literal in that
     both are modular reduced to a field, but the modulus is different."))
  (literal-case
   lit
   :bool (value-bool lit.val)
   :unsigned (bitsize-case
              lit.size
              :8 (and (ubyte8p lit.val) (value-u8 lit.val))
              :16 (and (ubyte16p lit.val) (value-u16 lit.val))
              :32 (and (ubyte32p lit.val) (value-u32 lit.val))
              :64 (and (ubyte64p lit.val) (value-u64 lit.val))
              :128 (and (ubyte128p lit.val) (value-u128 lit.val)))
   :signed (bitsize-case
            lit.size
            :8 (and (sbyte8p lit.val) (value-i8 lit.val))
            :16 (and (sbyte16p lit.val) (value-i16 lit.val))
            :32 (and (sbyte32p lit.val) (value-i32 lit.val))
            :64 (and (sbyte64p lit.val) (value-i64 lit.val))
            :128 (and (sbyte128p lit.val) (value-i128 lit.val)))
   :string (value-string lit.get)
   :address (value-address lit.get)
   :field (value-field (mod lit.val (curve-base-prime curve)))
   :group (eval-group-literal lit.get curve)
   :scalar (value-scalar (mod lit.val (curve-scalar-prime curve))))
  :hooks (:fix))
