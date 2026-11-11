; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/size-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/min-max-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "adj-list-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/size" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "adj-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The nodes of an adjacency list whose adjacency has a given target, found by
;; visiting every node.

(define adj-list-predecessors (to (adjl adj-listp))
  :returns (preds treeset::setp)
  (if (treemap::emptyp adjl)
      (treeset::empty)
    (b* ((from (treemap::min-key adjl))
         (preds (adj-list-predecessors to (treemap::delete from adjl))))
      (if (treemap::in to (treemap::lookup from adjl))
          (treeset::insert from preds)
        preds)))
  :measure (treemap::size adjl)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-predecessors-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-predecessors to adjl0)
                  (adj-list-predecessors to adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-predecessors to adjl0)
           (adj-list-predecessors to adjl1)))

(defruled in-of-adj-list-predecessors
  (equal (treeset::in from (adj-list-predecessors to adjl))
         (treeset::in to (treemap::keys (treemap::lookup from
                                                         adjl
                                                         :default (treemap::empty)))))
  :induct t
  :enable adj-list-predecessors)
