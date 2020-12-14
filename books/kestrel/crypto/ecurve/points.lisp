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

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ points
  :parents (elliptic-curves)
  :short "Predicates for points of elliptic curves over prime fields."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointp (point)
  :short "Recognize all possible points of all possible elliptic curves."
  :long
  (xdoc::topstring
   (xdoc::p
    "This models (at least)
     all possible points of all possible elliptic curves.
     A point, as modeled here,
     is either a pair of natural numbers or a special point at infinity.")
   (xdoc::p
    "This type of points is perhaps more general then elliptic curves,
     and thus it might be factored out into some more general library."))
  (or (and (consp point)
           (natp (car point))
           (natp (cdr point)))
      (eq point :infinity)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-in-pxp-p ((point pointp) (p natp))
  :guard (<= 2 p)
  :short "Check if a point is in the cartesian product of a prime field,
          or it is the point at infinity."
  :long
  (xdoc::topstring
   (xdoc::p
    "This predicate checks if a point (as defined in @(tsee pointp))
     is either the point at infity,
     or is in the cartesian product
     @($\\{0, \\ldots, p-1\\} \\times \\{0, \\ldots, p-1\\}$),
     where @($p \\geq 2$).
     In the context of elliptic curves, @($p$) is the prime,
     and this predicate checks if the point, if finite,
     is in the ``plane'' of the curve.")
   (xdoc::p
    "The purpose of this predicate is to provide a preliminary constraint
     for points of curves in specific fields (described by @($p$)).
     Thus, we must include the point at infinity in this predicate,
     even though it is not actually on the the aforementioned plane.")
   (xdoc::p
    "We do not require the parameter @('p') to be prime here.
     It suffices, for the purpose of defining this predicate,
     for @('p') to be an integer that is at least 2."))
  (or (eq point :infinity)
      (and (< (car point) p)
           (< (cdr point) p)))
  :guard-hints (("Goal" :in-theory (enable pointp)))

  ///

  (defthm point-in-pxp-p-of-infinity
    (implies (< 0 p)
             (point-in-pxp-p :infinity p))
    :hints (("Goal" :in-theory (enable point-in-pxp-p)))))
