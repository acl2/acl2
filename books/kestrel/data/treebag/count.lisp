; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "bag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "bag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count (x (bag bagp))
  :type-prescription :none
  :returns (count natp
                  :rule-classes ((:rewrite) (:type-prescription))
                  :hints (("Goal" :in-theory (enable* break-abstraction))))
  :parents (treebag)
  :short "The number of occurrences of a value in a @(see treebag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(m))$), where @($m$) is the number of distinct
     elements of the bag.")
  ;; Reading 0 for an absent element loses nothing, since no element of a
  ;; @(see treebag) is bound to 0.
  (treemap::lookup x (fix bag) :default 0)
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

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

;; Reading counts after binding an element to a positive value, or removing
;; it, in the underlying treemap.

(defruled count-of-treemap-update
  (implies (posp v)
           (equal (count y (treemap::update x v (fix bag)))
                  (if (equal y x)
                      v
                    (count y bag))))
  :enable (count
           break-abstraction))

(add-to-ruleset break-abstraction '(count-of-treemap-update))

(defruled count-of-treemap-delete
  (equal (count y (treemap::delete x (fix bag)))
         (if (equal y x)
             0
           (count y bag)))
  :enable (count
           break-abstraction))

(add-to-ruleset break-abstraction '(count-of-treemap-delete))

;; A value that is not a key of a bag's tree does not occur in the bag.

(defruled count-when-not-in-tree-key-set-of-fix
  (implies (not (treeset::in x (treemap::tree-key-set (fix bag))))
           (equal (count x bag)
                  0))
  :enable (count
           break-abstraction
           treemap::lookup
           treemap::keys))

(add-to-ruleset break-abstraction '(count-when-not-in-tree-key-set-of-fix))

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
