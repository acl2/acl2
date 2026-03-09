; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/to-oset-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/values-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/osets/top" :dir :system))
(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/to-oset" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/values"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define values ((map mapp))
  :returns (values treeset::setp)
  :parents (treemap)
  :short "Get the value @(see treeset::treeset) from a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(n))$)."))
  (tree-val-set (fix map))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule values-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (values map0)
                  (values map1)))
  :rule-classes :congruence
  :enable values)

(defrule emptyp-of-values
  (equal (treeset::emptyp (values map))
         (emptyp map))
  :enable (values
           emptyp))

(defruled values-when-emptyp
  (implies (emptyp map)
           (equal (values map)
                  (treeset::empty)))
  :use emptyp-of-values
  :enable treeset::emptyp-alt-definition
  :disable emptyp-of-values)

(defrule values-when-emptyp-cheap
  (implies (emptyp map)
           (equal (values map)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by values-when-emptyp)

(defrule values-of-empty
  (equal (values (empty))
         (treeset::empty))
  :enable values-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-values-linear
  (<= (treeset::cardinality (values map))
      (treeset::cardinality (keys map)))
  :rule-classes :linear
  :enable (values
           keys
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-lookup-and-values
  (implies (treeset::in key (keys map))
           (treeset::in (lookup key map :default default)
                        (values map)))
  :enable (lookup
           keys
           values))

;; TODO: element is in the value set iff the reverse-lookup of the value yields
;;   a non-empty set.
;;   (Need to define reverse-lookup or map inversion first.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: it isn't clear to me that either direction is more natural for the
;; default.
(defrule values-of-to-omap
  (equal (omap::values (to-omap map))
         (treeset::to-oset (values map)))
  :enable (to-omap
           values
           break-abstraction))

(add-to-ruleset from-omap-theory '(values-of-to-omap))

;; TODO: wherever from-omap is defined
;; (defrule omap-values-becomes-values
;;   (equal (omap::values map)
;;          (treeset::to-oset (values (from-omap map))))
;;   :enable (to-omap
;;            values
;;            break-abstraction))

(defruled values-becomes-omap-values
  (equal (values map)
         (treeset::from-oset (omap::values (to-omap map))))
  :enable treeset::extensionality)

(add-to-ruleset to-omap-theory '(values-becomes-omap-values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy values-extra-rules
  '(values-when-emptyp))
