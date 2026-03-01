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
(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/keys-defs")
(include-book "map-defs")
(include-book "to-omap-defs")

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
(local (include-book "internal/keys"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keys ((map mapp))
  :returns (keys treeset::setp)
  :parents (treemap)
  :short "Get the keys @(see treeset) from a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(log(n))$)."))
  (mbe :logic (tree-key-set (fix map))
       :exec (tree-key-tree map))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule keys-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (keys map0)
                  (keys map1)))
  :rule-classes :congruence
  :enable keys)

(defrule emptyp-of-keys
  (equal (treeset::emptyp (keys map))
         (emptyp map))
  :enable (keys
           emptyp))

(defruled keys-when-emptyp
  (implies (emptyp map)
           (equal (keys map)
                  (treeset::empty)))
  :use emptyp-of-keys
  :enable treeset::emptyp-alt-definition
  :disable emptyp-of-keys)

(defrule keys-when-emptyp-cheap
  (implies (emptyp map)
           (equal (keys map)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by keys-when-emptyp)

(defrule keys-of-empty
  (equal (keys (empty))
         (treeset::empty))
  :enable keys-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: it isn't clear to me that either direction is more natural for the
;; default.
(defrule keys-of-to-omap
  (equal (omap::keys (to-omap map))
         (treeset::to-oset (keys map)))
  :enable (to-omap
           keys
           break-abstraction))

(add-to-ruleset from-omap-theory '(keys-of-to-omap))

;; TODO: wherever from-omap is defined
;; (defrule omap-keys-becomes-keys
;;   (equal (omap::keys map)
;;          (treeset::to-oset (keys (from-omap map))))
;;   :enable (to-omap
;;            keys
;;            break-abstraction))

(defruled keys-becomes-omap-keys
  (equal (keys map)
         (treeset::from-oset (omap::keys (to-omap map))))
  :enable treeset::extensionality)

(add-to-ruleset to-omap-theory '(keys-becomes-omap-keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy keys-extra-rules
  '(keys-when-emptyp))
