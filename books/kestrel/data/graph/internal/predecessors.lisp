; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/omaps/defs" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/size-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/to-omap-defs" :dir :system)

(include-book "adj-list-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/size" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/to-omap" :dir :system))

(local (include-book "adj-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The search below, walking the omap of the list instead of removing its
;; least node at each step. This is what @(tsee adj-list-predecessors)
;; executes.

(define adj-list-predecessors-omap (to (omap omap::mapp))
  :guard (omap-values-all-adjacencyp omap)
  :returns (preds tset::setp)
  (if (omap::emptyp omap)
      (tset::empty)
    (b* (((mv from adj) (omap::head omap))
         (preds (adj-list-predecessors-omap to (omap::tail omap))))
      (if (tmap::in to adj)
          (tset::insert from preds)
        preds)))
  :guard-hints (("Goal" :in-theory (enable omap-values-all-adjacencyp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The nodes of an adjacency list whose adjacency has a given target, found by
;; visiting every node.

(define adj-list-predecessors (to (adjl adj-listp))
  :returns (preds tset::setp)
  (mbe :logic (if (tmap::emptyp adjl)
                  (tset::empty)
                (b* ((from (tmap::min-key adjl))
                     (preds (adj-list-predecessors to
                                                   (tmap::delete from adjl))))
                  (if (tmap::in to (tmap::lookup from adjl))
                      (tset::insert from preds)
                    preds)))
       :exec (adj-list-predecessors-omap to (tmap::to-omap adjl)))
  :measure (tmap::size adjl)
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-predecessors-when-tmap-equiv-of-arg2-congruence
  (implies (tmap::equiv adjl0 adjl1)
           (equal (adj-list-predecessors to adjl0)
                  (adj-list-predecessors to adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-predecessors to adjl0)
           (adj-list-predecessors to adjl1)))

(defruledl adj-list-predecessors-omap-of-to-omap
  (equal (adj-list-predecessors-omap to (tmap::to-omap adjl))
         (adj-list-predecessors to adjl))
  :induct (adj-list-predecessors to adjl)
  :enable (adj-list-predecessors
           adj-list-predecessors-omap))

(verify-guards adj-list-predecessors
  :hints (("Goal" :in-theory (enable adj-list-predecessors
                                     adj-list-predecessors-omap-of-to-omap))))

(defruled in-of-adj-list-predecessors
  (equal (tset::in from (adj-list-predecessors to adjl))
         (tset::in to (tmap::keys (tmap::lookup from
                                                adjl
                                                :default (tmap::empty)))))
  :induct t
  :enable adj-list-predecessors)
