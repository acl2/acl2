; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/in-order-defs")
(include-book "map-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/omaps/core" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/in-order"))
(local (include-book "map"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory aggressively rewrites from treemaps to oamps.
(def-ruleset! to-omap-theory ())

;; This theory aggressively rewrites from omaps to treemaps.
(def-ruleset! from-omap-theory ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-omap ((map mapp))
  :parents (treemap)
  :short "Build an omap from a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$).")
   (xdoc::p
     "@(see Treemap)s are isomorphic to "
     (xdoc::seetopic "omap::omaps" "omaps")
     ". This function may be used in combination with @(tsee from-omap) to go
      back and forth between the two representations. There are rules relating
      all of the primitive operations (@(tsee keys), @(tsee lookup),
      @(tsee update), etc.).")
   (xdoc::p
     "We provide a @(see acl2::ruleset), @('to-omap-theory'), to aggressively
      rewrite @(see treemap)s into @(see omap::omaps). To rewrite in the
      other direction (i.e., from @(see omap::omaps) to @(see treemap)s), we
      provide the @('from-omap-theory') ruleset. To use one ruleset, the other
      must be explicitly disabled. If the other ruleset is not disabled, expect
      rewrite loops."))
  :returns (omap omap::mapp
                 :hints (("Goal" :in-theory (enable* break-abstraction))))
  (tree-in-order (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t to-omap)))

(defrule to-omap-type-prescription
  (or (consp (to-omap map))
      (equal (to-omap map) nil))
  :rule-classes :type-prescription
  :enable to-omap)

(defrule to-omap-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (to-omap map0)
                  (to-omap map1)))
  :rule-classes :congruence
  :enable to-omap)

;;;;;;;;;;;;;;;;;;;;

(defruled to-omap-when-emptyp
  (implies (emptyp map)
           (equal (to-omap map)
                  nil))
  :enable (to-omap
           empty))

(defrule to-omap-when-emptyp-cheap
  (implies (emptyp map)
           (equal (to-omap map)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by to-omap-when-emptyp)

(defrule to-omap-of-empty
  (equal (to-omap (empty))
         nil)
  :enable to-omap-when-emptyp)

;;;;;;;;;;;;;;;;;;;;

(defrule omap-emptyp-of-to-omap
  (equal (omap::emptyp (to-omap map))
         (emptyp map))
  :enable (to-omap
           omap::emptyp
           break-abstraction))

(add-to-ruleset from-omap-theory '(omap-emptyp-of-to-omap))

(defruled emptyp-becomes-omap-emptyp
  (equal (emptyp map)
         (omap::emptyp (to-omap map))))

(add-to-ruleset to-omap-theory '(emptyp-becomes-omap-emptyp))
