; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "internal/in-order-defs")
(include-book "set-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in-order"))
(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory aggressively rewrites from treesets to osets.
(def-ruleset! to-oset-theory ())

;; This theory aggressively rewrites from osets to treesets.
(def-ruleset! from-oset-theory ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-oset ((set setp))
  :parents (treeset)
  :short "Build an oset from a @(see treeset)"
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$).")
   (xdoc::p
     "@(see Treeset)s are isomorphic to "
     (xdoc::seetopic "set::std/osets" "osets")
     ". This function may be used in combination with @(tsee from-oset) to go
      back and forth between the two representations. There are rules relating
      all of the primitive operations (@(tsee in), @(tsee insert), @(tsee
      union), etc.)."))
  :returns (oset set::setp
                 :hints (("Goal" :in-theory (enable fix
                                                    setp
                                                    empty))))
  (tree-in-order (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t to-oset)))

(defrule to-oset-type-prescription
  (or (consp (to-oset set))
      (equal (to-oset set) nil))
  :rule-classes :type-prescription
  :enable to-oset)

(defrule to-oset-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (to-oset set0)
                  (to-oset set1)))
  :rule-classes :congruence
  :enable to-oset)

;;;;;;;;;;;;;;;;;;;;

(defruled to-oset-when-emptyp
  (implies (emptyp set)
           (equal (to-oset set)
                  nil))
  :enable (to-oset
           empty))

(defrule to-oset-when-emptyp-cheap
  (implies (emptyp set)
           (equal (to-oset set)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by to-oset-when-emptyp)

(defrule to-oset-of-empty
  (equal (to-oset (empty))
         nil)
  :enable to-oset-when-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defrule oset-emptyp-of-to-oset
  (equal (set::emptyp (to-oset set))
         (emptyp set))
  :enable (to-oset
           emptyp
           set::emptyp
           break-abstraction
           fix))

(add-to-ruleset from-oset-theory '(oset-emptyp-of-to-oset))

(defruled emptyp-becomes-oset-emptyp
  (equal (emptyp set)
         (set::emptyp (to-oset set))))

(add-to-ruleset to-oset-theory '(emptyp-becomes-oset-emptyp))
