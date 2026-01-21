; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "xdoc/constructors" :dir :system)

(include-book "noninterval-arith-support")
(include-book "core")
(include-book "inp")
(include-book "subintervalp")
(include-book "arithmetic")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See also other interval arithmetic theories:
;; - nonstd/nsa/intevals
;; - workshops/2004/gameiro-manolios/support/interval
;; - centaur/vl2014/mlib/interval

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc intervals
  :parents (acl2::abstract-domains)
  :short "Rational intervals."
  :long
  (xdoc::topstring
    (xdoc::p
      "An @(see interval) represents a range of possible rational values. If it
       is not empty, it is characterized by its optional minimum and its
       optional maximum (see @(tsee min) and @(tsee max)). These bounds are
       <i>inclusive</i>. That is, the minimum, if it exists, is included in the
       interval. The same applies to the maximum.")
    (xdoc::p
      "The empty interval, written @($\\emptyset$), is represented by
       @('(empty)'). A bounded interval @($[x, y]$) (for rationals @($x$) and
       @($y$)) is represented by @('(interval x y)'). An interval that is
       bounded below but not above, such as @($[x, \\infty)$), is represented
       by @('(interval x nil)'). Similarly, @($(-\\infty, y]$) corresponds to
       @('(interval nil y)'). We refer to the totally unbounded interval,
       (@($(-\\infty, \\infty)$), @('(interval nil nil)')) as @(see full).")
    (xdoc::p
      "Intervals form a bounded lattice under the @(tsee subintervalp) order.
       The join of the lattice is @(tsee hull), and the meet is
       @(tsee intersect). The bottom element is the @(tsee empty) interval, and
       the top is @(tsee full).")
    (xdoc::p
      "We define various arithmetic operations on intervals. Each arithmetic
       operation is the tightest interval extension of the regular arithmetic
       operation. (See @(see arithmetic) for a definition of ``tightest
       interval extension.'')")))
