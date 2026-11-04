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

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)

(include-book "bag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "bag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count (x (bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (count natp
                  :rule-classes ((:rewrite) (:type-prescription))
                  :hints (("Goal" :in-theory (enable fix bagp empty))))
  ;; Reading 0 for an absent element loses nothing, since no element of a
  ;; @(see treebag) is bound to 0.
  (treemap::lookup x (fix bag) :default 0)
  :guard-hints (("Goal" :in-theory (enable bagp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule count-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (count x bag0)
                  (count x bag1)))
  :rule-classes :congruence
  :enable count)

(defruled count-when-emptyp
  (implies (emptyp bag)
           (equal (count x bag)
                  0))
  :enable (count
           emptyp))

(defrule count-when-emptyp-cheap
  (implies (emptyp bag)
           (equal (count x bag)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable count-when-emptyp)

(defruled not-emptyp-when-count-nonzero
  (implies (not (equal (count x bag) 0))
           (not (emptyp bag)))
  :use count-when-emptyp)

(defrule count-of-arg1-and-empty
  (equal (count x (empty))
         0)
  :enable count-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in (x (bag bagp))
  :parents (treebag)
  :short "Check if a value occurs in a @(see treebag)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(m))$), where @($m$) is the number of
       distinct elements of the bag.")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(in x bag)') becomes @('(< 0 (count
       x bag))')."))
  (< 0 (count x bag))
  :enabled t
  :inline t)
