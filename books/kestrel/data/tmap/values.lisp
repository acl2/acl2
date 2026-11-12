; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/to-oset-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
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

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/to-oset" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/values"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define values ((map mapp))
  :type-prescription :none
  :returns (values tset::setp)
  :parents (tmap)
  :short "Get the value @(see acl2::tset) from a @(see tmap)."
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
  (equal (tset::emptyp (values map))
         (emptyp map))
  :enable (values
           emptyp))

(defruled values-when-emptyp
  (implies (emptyp map)
           (equal (values map)
                  (tset::empty)))
  :use emptyp-of-values
  :enable tset::emptyp-alt-definition
  :disable emptyp-of-values)

(defrule values-when-emptyp-cheap
  (implies (emptyp map)
           (equal (values map)
                  (tset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by values-when-emptyp)

(defrule values-of-empty
  (equal (values (empty))
         (tset::empty))
  :enable values-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule cardinality-of-values-linear
  (<= (tset::cardinality (values map))
      (tset::cardinality (keys map)))
  :rule-classes :linear
  :enable (values
           keys
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule in-of-lookup-and-values
  (implies (tset::in key (keys map))
           (tset::in (lookup key map :default default)
                     (values map)))
  :enable (lookup
           keys
           values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: it isn't clear to me that either direction is more natural for the
;; default.
(defrule values-of-to-omap
  (equal (omap::values (to-omap map))
         (tset::to-oset (values map)))
  :enable (to-omap
           values
           break-abstraction))

(add-to-ruleset from-omap-theory '(values-of-to-omap))

(defruled values-becomes-omap-values
  (equal (values map)
         (tset::from-oset (omap::values (to-omap map))))
  :enable tset::extensionality)

(add-to-ruleset to-omap-theory '(values-becomes-omap-values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy values-extra-rules
  '(values-when-emptyp))
