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

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/to-oset-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/rlookup-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "in-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "values-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/to-oset" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/values"))
(local (include-book "internal/rlookup"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "in"))
(local (include-book "lookup"))
(local (include-book "values"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rlookup
  (val
   (map mapp))
  :returns (keys treeset::setp)
  :parents (treemap)
  :short "Lookup all keys associated to a value."
  :long
  (xdoc::topstring-p
   "Time complexity: @($O(n\\log(n))$).")
  (tree-rlookup val (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule rlookup-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (rlookup val map0)
                  (rlookup val map1)))
  :rule-classes :congruence
  :enable rlookup)

;;;;;;;;;;;;;;;;;;;;

(defruled rlookup-when-emptyp
  (implies (emptyp map)
           (equal (rlookup val map)
                  (treeset::empty)))
  :enable (rlookup
           break-abstraction))

(defrule rlookup-when-emptyp-cheap
  (implies (emptyp map)
           (equal (rlookup val map)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by rlookup-when-emptyp)

(defruled rlookup-of-empty
  (equal (rlookup val (empty))
         (treeset::empty))
  :enable rlookup-when-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defruled in-of-keys-when-in-of-rlookup
  (implies (treeset::in key (rlookup val map))
           (treeset::in key (keys map)))
  :enable (rlookup
           keys))

(defrule in-of-keys-when-in-of-rlookup-forward-chaining
  (implies (treeset::in key (rlookup val map))
           (treeset::in key (keys map)))
  :rule-classes :forward-chaining
  :by in-of-keys-when-in-of-rlookup)

(defrule subset-of-rlookup-tree-and-keys
  (treeset::subset (rlookup val map)
                   (keys map))
  :enable (rlookup
           keys))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-rlookup
  (equal (treeset::in key (rlookup val map))
         (and (treeset::in key (keys map))
              (equal (lookup key map) val)))
  :enable (rlookup
           lookup
           keys
           break-abstraction))

(defrule emptyp-of-rlookup
  (equal (treeset::emptyp (rlookup val map))
         (not (treeset::in val (values map))))
  :enable (rlookup
           values))

(defrule emptyp-of-rlookup-when-in-of-values-forward-chaining
  (implies (treeset::in val (values map))
           (not (treeset::emptyp (rlookup val map))))
  :rule-classes :forward-chaining)

(defrule emptyp-of-rlookup-when-not-in-of-values-forward-chaining
  (implies (not (treeset::in val (values map)))
           (treeset::emptyp (rlookup val map)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rlookup-of-to-omap
  (equal (omap::rlookup val (to-omap map))
         (treeset::to-oset (rlookup val map)))
  :enable (to-omap
           rlookup
           break-abstraction))

(add-to-ruleset from-omap-theory '(rlookup-of-to-omap))

(defruled rlookup-becomes-omap-rlookup
  (equal (rlookup val map)
         (treeset::from-oset (omap::rlookup val (to-omap map)))))

(add-to-ruleset to-omap-theory '(rlookup-becomes-omap-rlookup))
