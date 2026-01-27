; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "internal/count-defs")
(include-book "set-defs")
(include-book "to-oset-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/count"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "to-oset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality ((set setp))
  :returns (cardinality natp)
  :parents (treeset)
  :short "The number of elements in a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (tree-nodes-count (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable setp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t cardinality)))

(defrule cardinality-type-prescription
  (natp (cardinality set))
  :rule-classes ((:type-prescription :typed-term (cardinality set))))

(defrule cardinality-when-set-equiv-congruence
  (implies (equiv set0 set1)
           (equal (cardinality set0)
                  (cardinality set1)))
  :rule-classes :congruence
  :enable cardinality)

(defruled equal-of-cardinality-and-0-becomes-emptyp
  (equal (equal (cardinality set)
                0)
         (emptyp set))
  :enable (cardinality
           emptyp))

(defrule cardinality-when-emptyp-forward-chaining
  (implies (emptyp set)
           (equal (cardinality set)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule emptyp-when-equal-cardinality-and-0-forward-chaining
  (implies (equal (cardinality set)
                  0)
           (emptyp set))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule cardinality-of-empty
  (equal (cardinality (empty))
         0)
  :enable empty)

;;;;;;;;;;;;;;;;;;;;

(defrule oset-cardinality-of-to-oset
  (equal (set::cardinality (to-oset set))
         (cardinality set))
  :enable (to-oset
           cardinality
           fix
           setp
           empty))

(add-to-ruleset from-oset-theory '(oset-cardinality-of-to-oset))

(defruled cardinality-becomes-oset-cardinality
  (equal (cardinality set)
         (set::cardinality (to-oset set))))

(add-to-ruleset to-oset-theory '(cardinality-becomes-oset-cardinality))
