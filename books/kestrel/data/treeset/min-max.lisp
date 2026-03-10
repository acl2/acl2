; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "internal/min-max-defs")
(include-book "set-defs")
(include-book "to-oset-defs")
(include-book "in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "internal/tree"))
(local (include-book "internal/min-max"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min ((set setp))
  :parents (treeset)
  :short "The minimum element of a @(see treeset) (with respect to
          @(tsee <<))."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))
  :guard (not (emptyp set))
  (mbe :logic (tree-min (fix set))
       :exec (tree-leftmost set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(defrule min-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (min set0)
                  (min set1)))
  :rule-classes :congruence
  :enable min)

(defrule in-of-min
  (equal (in (min set) set)
         (not (emptyp set)))
  :enable (min
           in
           emptyp))

(defrule <<-of-arg1-and-min-when-in
  (implies (in x set)
           (not (<< x (min set))))
  :enable (min
           in))

(defrule <<-of-min-when-in
  (implies (in x set)
           (equal (<< (min set) x)
                  (not (equal (min set) x))))
  :enable (min
           in))

;;;;;;;;;;;;;;;;;;;;

(defrule car-of-to-oset
  (equal (car (to-oset set))
         (min set))
  :enable (to-oset
           min
           break-abstraction))

(add-to-ruleset from-oset-theory '(car-of-to-oset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max ((set setp))
  :parents (treeset)
  :short "The maximum element of a @(see treeset) (with respect to
          @(tsee <<))."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$)."))
  :guard (not (emptyp set))
  (mbe :logic (tree-max (fix set))
       :exec (tree-rightmost set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(defrule max-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (max set0)
                  (max set1)))
  :rule-classes :congruence
  :enable max)

(defrule in-of-max
  (equal (in (max set) set)
         (not (emptyp set)))
  :enable (max
           in
           emptyp))

(defrule <<-of--max-when-in
  (implies (in x set)
           (not (<< (max set) x)))
  :enable (max
           in))

(defrule <<-of-arg1-and-max-when-in
  (implies (in x set)
           (equal (<< x (max set))
                  (not (equal (max set) x))))
  :enable (max
           in))

;;;;;;;;;;;;;;;;;;;;

(defrule car-of-last-of-to-oset
  (equal (car (last (to-oset set)))
         (max set))
  :enable (to-oset
           max
           break-abstraction))

(add-to-ruleset from-oset-theory '(car-of-last-of-to-oset))
