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

(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/count-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "keys-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/cardinality" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/count"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define size ((map mapp))
  :returns (size natp)
  :parents (treemap)
  :short "The number of key/value pairs in a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$).")
   (xdoc::p
     "This is <i>not</i> the logical normal form used by this library.
      Instead, we rewrite @('(size map)') to
      @('(treeset::cardinality (keys map))')."))
  (mbe :logic (treeset::cardinality (keys map))
       :exec (tree-nodes-count map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable mapp
                                           keys))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t size)))

(defrule size-type-prescription
  (natp (size map))
  :rule-classes ((:type-prescription :typed-term (size map))))

(defrule size-when-map-equiv-congruence
  (implies (equiv map0 map1)
           (equal (size map0)
                  (size map1)))
  :rule-classes :congruence
  :enable size)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule size-of-to-omap
  (equal (omap::size (to-omap map))
         (size map))
  :enable (to-omap
           keys
           break-abstraction))

(add-to-ruleset from-omap-theory '(size-of-to-omap))

(defruled size-becomes-omap-size
  (equal (size map)
         (omap::size (to-omap map))))

(add-to-ruleset to-omap-theory '(size-becomes-omap-size))
