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

(include-book "elliptic-curve-generator-point")

(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "kestrel/fty/defunit" :dir :system)
(include-book "kestrel/number-theory/prime" :dir :system)

(local (in-theory (enable ecurve::pointp-when-edwards-bls12-pointp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ curve-parameterization
  :parents (static-semantics dynamic-semantics)
  :short "Curve parameterization in Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The (static and dynamic) semantics of Leo is parameterized over
     a choice of
     (i) a prime field,
     (ii) an elliptic curve over the field, and
     (iii) a generator point on the curve.
     Collectively, these are sometimes referred to just as `curve',
     because the curve is the primary component in some sense,
     with the prime field being considered in a way part of the curve,
     and with the generator point being closely related to the curve.
     The prime field is the `base field'.
     The generator point must have prime order,
     and its order defines another prime field,
     namely the `scalar field'.
     The curve is chosen in the Leo configuration file,
     which will be supported in future versions of Leo.
     All of this is explained in the Leo Reference.")
   (xdoc::p
    "In our ACL2 formalization,
     we capture the possible curve choices via a fixtype.
     Since currently Leo supports just one curve,
     for now the fixtype is a singleton.
     However, this will be extended as more curves are added.")
   (xdoc::p
    "We define functions that take the aforementioned fixtype as parameter
     and that define semantic aspects of Leo that depend on the curve.
     An example is the base field prime.
     These functions are used to define the semantics of Leo."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defunit curve
  :short "Fixtype of curve choices."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now there is just one choice, namely Edwards BLS12."))
  :value :edwards-bls12
  :pred curvep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-base-prime ((curve curvep))
  :returns (prime primep)
  :short "Base field prime of a curve."
  (declare (ignore curve))
  (ecurve::edwards-bls12-q)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-scalar-prime ((curve curvep))
  :returns (prime primep)
  :short "Scalar field prime of a curve."
  (declare (ignore curve))
  (ecurve::edwards-bls12-r)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-subgroupp (x (curve curvep))
  :returns (yes/no booleanp)
  :short "Recognizer of the subgroup of a curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The subgroup consists of points of the curve
     that additionally yield the neutral point
     when multiplied by the scalar prime.")
   (xdoc::p
    "This should be the same as @(tsee ecurve::edwards-bls12-r-pointp)
     for Edwards BLS12,
     but that definition uses
     the non-executable function @(tsee ecurve::twisted-edwards-point-orderp).
     We plan to extend the ACL2 elliptic curve library
     with executable versions of functions such as this,
     linked by theorems to the non-executable versions;
     but for now we just redefine the function here in executable form.
     Note that we just check that
     multiplying the point by the scalar prime yields the neutral point,
     without checking that multiplying the point by a smaller positive integer
     does not yield the neutral point
     (which is the complete definition of order):
     for this kind of curve group, the check performed here should suffice,
     i.e. it should imply the additional one;
     we plan to formally prove all of this."))
  (and (ecurve::edwards-bls12-pointp x)
       (equal (ecurve::edwards-bls12-mul-fast (curve-scalar-prime curve) x)
              (ecurve::twisted-edwards-zero)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-zero ((curve curvep))
  :returns (zero (curve-subgroupp zero curve)
                 :hints
                 (("Goal" :in-theory (enable curve-subgroupp
                                             curve-scalar-prime
                                             ecurve::edwards-bls12-r
                                             ecurve::twisted-edwards-zero))))
  :short "Neutral point of the subgroup."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as the neutral point of the curve,
     since the neutral point is shared with the subgroup."))
  (declare (ignore curve))
  (ecurve::twisted-edwards-zero)
  :hooks (:fix)
  ///

  (more-returns
   (zero pointp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-subgroup-add ((x (curve-subgroupp x curve))
                            (y (curve-subgroupp y curve))
                            (curve curvep))
  :returns (mv (okp booleanp)
               (x+y (curve-subgroupp x+y curve)))
  :short "Addition in the subgroup."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the same as addition in the curve group,
     but it has the property that
     adding two subgroup elements yields a subgroup element.
     We plan to prove that, but for now we check that here,
     returning an indication of failure as the first result
     and the neutral point as second result;
     otherwise, the first result indicates success
     and the second result is the sum.
     This function should never return @('nil') as first result;
     when we prove that it is the case,
     we will eliminate the first result."))
  (b* ((x (mbe :logic (if (curve-subgroupp x curve) x (curve-zero curve))
               :exec x))
       (y (mbe :logic (if (curve-subgroupp y curve) y (curve-zero curve))
               :exec y))
       (x+y (ecurve::edwards-bls12-add x y)))
    (if (curve-subgroupp x+y curve)
        (mv t x+y)
      (mv nil (curve-zero curve))))
  :guard-hints (("Goal" :in-theory (enable curve-subgroupp)))
  :hooks (:fix)
  ///

  (more-returns
   (x+y pointp
        :hints (("Goal" :in-theory (enable curve-subgroupp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-subgroup-neg ((x (curve-subgroupp x curve))
                            (curve curvep))
  :returns (mv (okp booleanp)
               (-x (curve-subgroupp -x curve)))
  :short "Negation in the subgroup."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the same two-result approach as for addition;
     see @(tsee curve-subgroup-add)."))
  (b* ((x (mbe :logic (if (curve-subgroupp x curve) x (curve-zero curve))
               :exec x))
       (-x (ecurve::edwards-bls12-neg x)))
    (if (curve-subgroupp -x curve)
        (mv t -x)
      (mv nil (curve-zero curve))))
  :guard-hints (("Goal" :in-theory (enable curve-subgroupp)))
  :hooks (:fix)
  ///

  (more-returns
   (-x pointp
       :hints (("Goal" :in-theory (enable curve-subgroupp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-subgroup-mul ((k natp)
                            (x (curve-subgroupp x curve))
                            (curve curvep))
  :guard (< k (curve-scalar-prime curve))
  :returns (mv (okp booleanp)
               (k*x (curve-subgroupp k*x curve)))
  :short "Scalar multiplication in the subgroup."
  :long
  (xdoc::topstring
   (xdoc::p
    "We limit the scalar to the in the scalar field,
     although there is no need to do that
     from the point of view of the operation being well-defined.
     We expect that this will always be the case though.")
   (xdoc::p
    "We use the same two-result approach as for addition;
     see @(tsee curve-subgroup-add)."))
  (b* ((x (mbe :logic (if (curve-subgroupp x curve) x (curve-zero curve))
               :exec x))
       (k*x (ecurve::edwards-bls12-mul-fast (nfix k) x)))
    (if (curve-subgroupp k*x curve)
        (mv t k*x)
      (mv nil (curve-zero curve))))
  :guard-hints (("Goal" :in-theory (enable curve-subgroupp)))
  :hooks (:fix)
  ///

  (more-returns
   (k*x pointp
        :hints (("Goal" :in-theory (enable curve-subgroupp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define curve-generator ((curve curvep))
  :returns (gen (curve-subgroupp gen curve)
                :hints
                (("Goal" :in-theory (enable curve-subgroupp
                                            curve-scalar-prime
                                            ecurve::edwards-bls12-r
                                            ecurve::twisted-edwards-zero))))
  :short "Generator point of the subgroup."
  :long
  (xdoc::topstring
   (xdoc::p
    "Even though any non-zero element of the subgroup
     is a generator of the subgroup,
     here we pick a specific one,
     which presumably is needed to make certain calculations
     unambiguous and deterministic."))
  (declare (ignore curve))
  (edwards-bls12-generator)
  :hooks (:fix))
