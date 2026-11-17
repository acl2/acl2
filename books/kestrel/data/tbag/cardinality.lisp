; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "internal/cardinality-defs")
(include-book "bag-defs")
(include-book "count-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/cardinality"))
(local (include-book "bag"))
(local (include-book "count"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality ((bag bagp))
  :returns (cardinality natp
                        :rule-classes ((:rewrite) (:type-prescription)))
  :parents (tbag)
  :short "The number of occurrences of all values in a @(see tbag)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(m)$), where @($m$) is the number of distinct
     elements of the bag.")
  (tree-cardinality (fix bag))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp
                                           tmap::treep-when-mapp-forward-chaining))))

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
           tmap::emptyp))

;; The reverse direction, for proving emptiness from the cardinality.

(defruled emptyp-becomes-equal-of-cardinality-and-0
  (equal (emptyp bag)
         (equal (cardinality bag)
                0))
  :enable equal-of-cardinality-and-0-becomes-emptyp)

(theory-invariant
  (incompatible! (:rewrite emptyp-becomes-equal-of-cardinality-and-0)
                 (:rewrite equal-of-cardinality-and-0-becomes-emptyp)))

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
           tmap::lookup
           tmap::keys))

;;;;;;;;;;;;;;;;;;;;

;; Reading the cardinality after binding an element to a positive value, or
;; removing it, in the underlying tmap. The tmap operation must stay
;; closed until the bag fixer around it is gone, so these lemmas open it only
;; beneath the tree walk.

(defruledl tree-cardinality-of-tmap-update
  (equal (tree-cardinality (tmap::update x v map))
         (tree-cardinality
           (tmap::tree-update x v (tmap::fix map))))
  :enable tmap::update)

(defruledl tree-cardinality-of-tmap-delete
  (equal (tree-cardinality (tmap::delete x map))
         (tree-cardinality (tmap::tree-delete x (tmap::fix map))))
  :enable tmap::delete)

(defruled cardinality-of-tmap-update
  (implies (posp v)
           (equal (cardinality (tmap::update x v (fix bag)))
                  (+ v (- (cardinality bag) (count x bag)))))
  :enable (cardinality
           count
           break-abstraction
           tree-cardinality-of-tmap-update
           tmap::lookup
           tmap::keys
           nfix))

(add-to-ruleset break-abstraction '(cardinality-of-tmap-update))

(defruled cardinality-of-tmap-delete
  (equal (cardinality (tmap::delete x (fix bag)))
         (- (cardinality bag) (count x bag)))
  :enable (cardinality
           count
           break-abstraction
           tree-cardinality-of-tmap-delete
           tmap::lookup
           tmap::keys
           nfix))

(add-to-ruleset break-abstraction '(cardinality-of-tmap-delete))
