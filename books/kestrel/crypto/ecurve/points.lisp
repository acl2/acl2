; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Point Predicates
; ----------------

; This book introduces predicates
; for points of elliptic curves over prime fields.
; It is actually more general than elliptic curves:
; points are defined as pairs of natural numbers,
; and an additional predicate is provided to check whether a point
; has coordinates below an integer p >= 2
; (where, in the context of elliptic curves, p is the prime).
; So this book could be factored into a more general library at some point.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following predicate is adequate to model
; all the possible points (and more) of an elliptic curve over a prime field
; whose equation is not satisfied by (0, 0),
; because in that case (0, 0) can be always used to model the point at infinity.
; For instance, for an elliptic curve in short Weierstrass form,
; whose equation is y^2 = x^3 + ax + b with a, b, x, y in Fp and p > 3
; (where Fp is the prime field),
; if b =/= 0 then (0, 0) can represent the point at infinity.
; Otherwise, we could model the point at infinity as some other point
; that does not satisfy the curve equation,
; or is outside the cartesian product Fp * Fp,
; such the point (p, p);
; but in this case the choice may vary with the curve.
; Eventually, it may be better to generalize this predicate to include
; an additional elemement (e.g. :INF) to model the point at infinity.

(defund pointp (point)
  (declare (xargs :guard t))
  (and (consp point)
       (natp (car point))
       (natp (cdr point))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following predicate checks if a point (as defined above)
; is in the cartesian product {0,...,p-1} * {0,...,p-1}, where p >= 2.
; In the context of elliptic curves, p is the prime,
; and this predicate checks if the point is in the "plane" of the curve.

(defund point-in-pxp-p (point p)
  (declare (xargs :guard (and (natp p) (<= 2 p)
                              (pointp point))
                  :guard-hints (("Goal" :in-theory (enable pointp)))))
  (and (< (car point) p)
       (< (cdr point) p)))

; As discussed above, under certain conditions
; the point at infinity can be modeled as (0, 0).
; Our elliptic curve library satisfies those conditions.
; The following theorem applies to this modeling of the point at infinity.

(defthm point-in-pxp-p-of-inf
  (implies (< 0 p)
           (point-in-pxp-p '(0 . 0) p))
  :hints (("Goal" :in-theory (enable point-in-pxp-p))))
