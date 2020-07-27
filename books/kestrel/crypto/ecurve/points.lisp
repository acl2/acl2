; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following predicate models (at least)
; all possible points of all possible elliptic curves.
; A point is either a pair of natural numbers or a special point at infinity.
; This type of points is perhaps more general then elliptic curves,
; and thus it might be factored out into some more general library.

(defund pointp (point)
  (declare (xargs :guard t))
  (or (and (consp point)
           (natp (car point))
           (natp (cdr point)))
      (eq point :infinity)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following predicate checks if a point (as defined above)
; is in the cartesian product {0,...,p-1} * {0,...,p-1}, where p >= 2.
; In the context of elliptic curves, p is the prime,
; and this predicate checks if the point is in the "plane" of the curve.
; This applies to finite points that are pairs of natural numbers;
; the point at infinity satisfies this predicate,
; because it is "outside" the cartesian product of the field with itself.
; The purpose of this predicate is to provide a preliminary constraint
; for points of curves in specific fields (described by p),
; and thus we must include the point at infinity in this predicate.

(defund point-in-pxp-p (point p)
  (declare (xargs :guard (and (natp p) (<= 2 p)
                              (pointp point))
                  :guard-hints (("Goal" :in-theory (enable pointp)))))
  (or (eq point :infinity)
      (and (< (car point) p)
           (< (cdr point) p))))

(defthm point-in-pxp-p-of-infinity
  (implies (< 0 p)
           (point-in-pxp-p :infinity p))
  :hints (("Goal" :in-theory (enable point-in-pxp-p))))
