; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(include-book "internal/subbag-defs")
(include-book "bag-defs")
(include-book "count-defs")
(include-book "cardinality-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "internal/map-values-all-posp"))
(local (include-book "internal/induction"))
(local (include-book "internal/subbag"))
(local (include-book "bag"))
(local (include-book "count"))
(local (include-book "cardinality"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subbag ((sub bagp)
                (sup bagp))
  :returns (yes/no booleanp)
  :parents (treebag)
  :short "Check if every value occurs in one @(see treebag) at most as often
          as in another."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
     numbers of distinct elements of @('sub') and @('sup').")
  (tree-subbag-p (fix sub) (fix sup))
  :inline t
  :guard-hints (("Goal" :in-theory (enable bagp
                                           tree-all-vals-posp-of-fix
                                           treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t subbag)))

(defrule subbag-type-prescription
  (booleanp (subbag sub sup))
  :rule-classes ((:type-prescription :typed-term (subbag sub sup))))

(defrule subbag-when-equiv-of-arg1-congruence
  (implies (equiv sub0 sub1)
           (equal (subbag sub0 sup)
                  (subbag sub1 sup)))
  :rule-classes :congruence
  :enable subbag)

(defrule subbag-when-equiv-of-arg2-congruence
  (implies (equiv sup0 sup1)
           (equal (subbag sub sup0)
                  (subbag sub sup1)))
  :rule-classes :congruence
  :enable subbag)

(defrule count-<=-count-when-subbag-linear
  (implies (subbag sub sup)
           (<= (count x sub)
               (count x sup)))
  :rule-classes :linear
  :enable (subbag
           count
           treemap::lookup
           treemap::keys
           break-abstraction
           in-of-tree-key-set-when-tree-subbag-p
           tree-lookup-<=-tree-lookup-when-tree-subbag-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk subbag-sk (sub sup)
  :parents (subbag)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (forall (elem)
    (non-exec
      (<= (count elem sub)
          (count elem sup)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t subbag-sk)))

;; The check fails, if at all, at its witness.

(defruledl subbag-becomes-<=-of-count-at-witness
  (equal (subbag sub sup)
         (let ((x (tree-subbag-p-witness (fix sub) (fix sup))))
           (<= (count x sub)
               (count x sup))))
  :enable (subbag
           tree-subbag-p-pick-a-point
           count
           treemap::lookup
           treemap::keys
           break-abstraction))

(defruledl subbag-sk-when-subbag
  (implies (subbag (double-rewrite sub) (double-rewrite sup))
           (subbag-sk sub sup))
  :enable subbag-sk)

(defruledl subbag-when-subbag-sk
  (implies (subbag-sk sub sup)
           (subbag sub sup))
  :enable (subbag-becomes-<=-of-count-at-witness
           subbag-sk-necc))

(defruled subbag-becomes-subbag-sk
  (equal (subbag sub sup)
         (subbag-sk sub sup))
  :cases ((subbag sub sup))
  :enable (subbag-sk-when-subbag
           subbag-when-subbag-sk))

(defruled subbag-sk-becomes-subbag
  (equal (subbag-sk sub sup)
         (subbag sub sup))
  :by subbag-becomes-subbag-sk)

(defrule subbag-sk-when-equiv-of-arg1-congruence
  (implies (equiv sub0 sub1)
           (equal (subbag-sk sub0 sup)
                  (subbag-sk sub1 sup)))
  :rule-classes :congruence
  :enable subbag-sk-becomes-subbag)

(defrule subbag-sk-when-equiv-of-arg2-congruence
  (implies (equiv sup0 sup1)
           (equal (subbag-sk sub sup0)
                  (subbag-sk sub sup1)))
  :rule-classes :congruence
  :enable subbag-sk-becomes-subbag)

(defthy pick-a-point
  '(subbag-becomes-subbag-sk
    subbag-sk))

(defruled subbag-becomes-subbag-sk-polar
  (implies (syntaxp (acl2::want-to-weaken (subbag sub sup)))
           (equal (subbag sub sup)
                  (subbag-sk sub sup)))
  :by subbag-becomes-subbag-sk)

(defthy pick-a-point-polar
  '(subbag-becomes-subbag-sk-polar
    subbag-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subbag-when-emptyp-of-arg1
  (implies (emptyp sub)
           (subbag sub sup))
  :enable pick-a-point)

;; Opening emptyp only where it is to be proved, so that an emptiness
;; hypothesis stays available to the count rules.

(defruledl emptyp-alt-definition-polar
  (implies (syntaxp (acl2::want-to-weaken (emptyp bag)))
           (equal (emptyp bag)
                  (equal (fix bag) (empty))))
  :enable emptyp-alt-definition)

(defruledl emptyp-when-subbag-and-emptyp
  (implies (and (subbag sub sup)
                (emptyp sup))
           (emptyp sub))
  :enable (emptyp-alt-definition-polar
           extensionality-polar))

(defrule subbag-when-emptyp-of-arg2
  (implies (emptyp sup)
           (equal (subbag sub sup)
                  (emptyp sub)))
  :cases ((subbag sub sup))
  :enable emptyp-when-subbag-and-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defrule subbag-reflexivity
  (subbag bag bag)
  :enable pick-a-point)

(defruled subbag-antisymmetry
  (implies (and (subbag x y)
                (subbag y x))
           (equal (fix x) (fix y)))
  :enable extensionality)

(defruled subbag-antisymmetry-equiv
  (implies (and (subbag x y)
                (subbag y x))
           (equiv x y))
  :enable (equiv
           extensionality))

(defrule subbag-antisymmetry-equiv-forward-chaining
  (implies (and (subbag x y)
                (subbag y x))
           (equiv x y))
  :rule-classes ((:forward-chaining :trigger-terms ((and (subbag x y)
                                                         (subbag y x)))))
  :by subbag-antisymmetry-equiv)

(defrule subbag-transitivity
  (implies (and (subbag x y)
                (subbag y z))
           (subbag x z))
  :enable pick-a-point-polar)

;; The same with the hypotheses in the other order, so that the middle bag can
;; be found from a known superbag instead of a known subbag.

(defrule subbag-transitivity-alt
  (implies (and (subbag y z)
                (subbag x y))
           (subbag x z))
  :by subbag-transitivity)

;;;;;;;;;;;;;;;;;;;;

(defruled double-containment
  (implies (and (bagp x)
                (bagp y))
           (equal (equal x y)
                  (and (subbag x y)
                       (subbag y x))))
  :use subbag-antisymmetry)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cardinality is a sum over the elements, so comparing the cardinalities of
;; a subbag and its superbag takes an induction. Each step removes every
;; occurrence of the subbag's smallest element from both bags.

(defruledl subbag-of-treemap-delete-and-treemap-delete
  (implies (subbag sub sup)
           (subbag (treemap::delete x (fix sub))
                   (treemap::delete x (fix sup))))
  :enable (pick-a-point-polar
           break-abstraction))

;; The gap between the counts of any one element is at most the gap between
;; the cardinalities.

(defrule count-gap-<=-cardinality-gap-when-subbag-linear
  (implies (subbag sub sup)
           (<= (- (count x sup) (count x sub))
               (- (cardinality sup) (cardinality sub))))
  :rule-classes ((:linear :trigger-terms ((count x sup))))
  :induct (min-delete-both-induction sub sup)
  :enable (break-abstraction
           subbag-of-treemap-delete-and-treemap-delete)
  :disable fix-when-bagp)

(defrule cardinality-when-subbag-linear
  (implies (subbag sub sup)
           (<= (cardinality sub)
               (cardinality sup)))
  :rule-classes :linear
  :induct (min-delete-both-induction sub sup)
  :enable (break-abstraction
           subbag-of-treemap-delete-and-treemap-delete)
  :disable fix-when-bagp)

(defrule cardinality-when-proper-subbag-linear
  (implies (and (subbag sub sup)
                (not (subbag sup sub)))
           (< (cardinality sub)
              (cardinality sup)))
  :rule-classes :linear
  :enable pick-a-point-polar)
