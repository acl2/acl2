; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "secp256k1-types")
(include-book "points")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ secp256k1-point-type-conversions
  :parents (secp256k1)
  :short "Conversions between @(tsee secp256k1-point) and @('pointp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type @(tsee secp256k1-point) represents elliptic curve points
     as FTY products, with the point at infinity as (0, 0).
     On the other hand, the predicate @('pointp') represents points
     as @(tsee cons) pairs, except for the point at infinity @(':infinity').
     Here we define functions to convert between these two representations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-to-pointp ((secp-point secp256k1-pointp))
  :returns (point pointp :hints (("Goal" :in-theory (enable pointp))))
  :short "Convert the representation of a secp256k1 point
          from @(tsee secp256k1-point) to @('pointp')."
  (b* ((x (secp256k1-point->x secp-point))
       (y (secp256k1-point->y secp-point)))
    (if (and (= x 0) (= y 0))
        :infinity
      (cons x y)))
  :hooks (:fix)
  ///

  (defrule point-in-pxp-p-of-secp256k1-point-to-pointp
    (point-in-pxp-p (secp256k1-point-to-pointp secp-point)
                    (secp256k1-field-prime))
    :enable (point-in-pxp-p
             secp256k1-point->x
             secp256k1-point->y
             secp256k1-field-fix
             secp256k1-fieldp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointp-to-secp256k1-point ((point pointp))
  :guard (and (point-in-pxp-p point (secp256k1-field-prime))
              (not (equal point (cons 0 0))))
  :returns (secp-point secp256k1-pointp)
  :short "Convert the representation of a secp256k1 point
          from @('pointp') to @(tsee secp256k1-point)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type @('pointp') is larger than @(tsee secp256k1-point),
     because it includes all possible points for all possible fields.
     So, we limit the conversion to points in the field of secp256k1,
     as expressed by the guard.")
   (xdoc::p
    "Furthermore, we limit the conversion to points that are not (0, 0),
     because that represents the point of infinity in @(tsee secp256k1-point),
     but not in @('pointp') (which uses @(':infinity').
     Without this restriction, one of the two the inverse theorem below
     (the one with the hypotheses) would not be provable."))
  (if (eq point :infinity)
      (secp256k1-point 0 0)
    (secp256k1-point (car point) (cdr point)))
  :guard-hints (("Goal"
                 :in-theory (enable pointp point-in-pxp-p secp256k1-fieldp)))
  ///

  (defrule pointp-to-secp256k1-point-of-secp256k1-point-to-pointp
    (equal (pointp-to-secp256k1-point (secp256k1-point-to-pointp secp-point))
           (secp256k1-point-fix secp-point))
    :enable (secp256k1-point-to-pointp
             secp256k1-point-fix
             secp256k1-point->x
             secp256k1-point->y
             secp256k1-pointp))

  (defrule secp256k1-point-to-pointp-of-pointp-to-secp256k1-point
    (implies (and (pointp point)
                  (point-in-pxp-p point (secp256k1-field-prime))
                  (not (equal point (cons 0 0))))
             (equal (secp256k1-point-to-pointp
                     (pointp-to-secp256k1-point point))
                    point))
    :enable (secp256k1-point-to-pointp
             pointp
             point-in-pxp-p
             secp256k1-fieldp)))
