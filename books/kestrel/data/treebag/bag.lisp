; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "kestrel/data/treemap/map-defs" :dir :system)

(include-book "internal/map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))

(local (include-book "internal/map-values-all-posp"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bagp (x)
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (treebag)
  :short "Recognizer for @(see treebag)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (and (treemap::mapp x)
       (map-values-all-posp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  (declare (xargs :type-prescription :none))
  :returns (bag bagp)
  :parents (treebag)
  :short "The empty @(see treebag)."
  (treemap::empty)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fix ((bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (bag$ bagp)
  :parents (treebag)
  :short "Fixer for @(see treebag)s."
  (mbe :logic (if (bagp bag)
                  bag
                (empty))
       :exec (the list bag))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* bagp
                                            treemap::break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule fix-when-bagp
  (implies (bagp bag)
           (equal (fix bag)
                  bag))
  :enable fix)

(defruled fix-when-not-bagp
  (implies (not (bagp bag))
           (equal (fix bag)
                  (empty)))
  :enable fix)

(defrule fix-when-not-bagp-cheap
  (implies (not (bagp bag))
           (equal (fix bag)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-bagp)

(defruled mapp-of-fix
  (treemap::mapp (fix bag))
  :enable (fix
           bagp
           empty))

(add-to-ruleset break-abstraction '(mapp-of-fix))

(defruled map-values-all-posp-of-fix
  (map-values-all-posp (fix bag))
  :enable (fix
           bagp
           empty))

(add-to-ruleset break-abstraction '(map-values-all-posp-of-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x bagp)
   (y bagp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (treebag)
  :short "Equivalence up to @(tsee fix)."
  (equal (fix x)
         (fix y))
  :inline t

  ///
  (defequiv equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule fix-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (fix bag0)
                  (fix bag1)))
  :rule-classes :congruence
  :enable equiv)

(defrule fix-under-equiv
  (equiv (fix bag)
         bag)
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((bag bagp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (treebag)
  :short "Check if a @(see treebag) is empty."
  (treemap::emptyp (fix bag))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp))))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-when-equiv-congruence
  (implies (equiv bag0 bag1)
           (equal (emptyp bag0)
                  (emptyp bag1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable (empty
           emptyp
           fix))

(defruled fix-when-emptyp
  (implies (emptyp bag)
           (equal (fix bag)
                  (empty)))
  :enable (emptyp
           fix
           bagp
           empty
           treemap::emptyp
           treemap::empty
           treemap::break-abstraction))

(defrule fix-when-emptyp-cheap
  (implies (emptyp bag)
           (equal (fix bag)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fix-when-emptyp)

(defrule bagp-when-not-emptyp-forward-chaining
  (implies (not (emptyp bag))
           (bagp bag))
  :rule-classes :forward-chaining
  :enable (emptyp
           bagp
           empty))

;; TODO: Should this also be a regular rewrite rule?
(defrule emptyp-when-not-bagp-forward-chaining
  (implies (not (bagp bag))
           (emptyp bag))
  :rule-classes :forward-chaining)

;; This definition is useful for proving emptiness by extensionality.
(defruled emptyp-alt-definition
  (equal (emptyp bag)
         (equal (fix bag) (empty)))
  :rule-classes :definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy bag-extra-rules
  '(fix-when-not-bagp
    fix-when-emptyp
    ))
