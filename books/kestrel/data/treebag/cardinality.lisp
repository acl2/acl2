; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/cardinality-defs")
(include-book "bag-defs")
(include-book "count-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/cardinality"))
(local (include-book "bag"))
(local (include-book "count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality ((bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (cardinality natp
                        :rule-classes ((:rewrite) (:type-prescription)))
  :parents (treebag)
  :short "The number of occurrences of all values in a @(see treebag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(m)$), where @($m$) is the number of distinct
     elements of the bag.")
  (tree-cardinality (fix bag))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp
                                           treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (cardinality bag0)
                  (cardinality bag1)))
  :rule-classes :congruence
  :enable cardinality)

(defruled equal-of-cardinality-and-0-becomes-emptyp
  (equal (equal (cardinality bag)
                0)
         (emptyp bag))
  :enable (cardinality
           emptyp
           break-abstraction
           equal-of-tree-cardinality-and-0-when-tree-all-vals-posp
           treemap::emptyp))

(defrule cardinality-when-emptyp-forward-chaining
  (implies (emptyp bag)
           (equal (cardinality bag)
                  0))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule emptyp-when-equal-cardinality-and-0-forward-chaining
  (implies (equal (cardinality bag)
                  0)
           (emptyp bag))
  :rule-classes :forward-chaining
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(defrule cardinality-of-empty
  (equal (cardinality (empty))
         0)
  :enable equal-of-cardinality-and-0-becomes-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defrule count-<=-cardinality-linear
  (<= (count x bag)
      (cardinality bag))
  :rule-classes :linear
  :enable (count
           cardinality
           break-abstraction
           treemap::lookup
           treemap::keys))
