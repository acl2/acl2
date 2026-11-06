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
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/size-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/min-max-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../edge-defs")
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
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/size" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The edge set of an adjacency list, built by three nested walks: over the
;; labels leading to one target, over the targets of one adjacency, and over
;; the sources of the list. Each walk takes the minimum and deletes it.
;;
;; These are logical characterizations, not meant to be run on large graphs.
;; Each step costs a minimum and a deletion, so the walk over the whole list
;; is @($O((n + m) \\log(n + m))$). Since the edges come out in ascending
;; order, a linear-time construction through @(tsee treeset::from-oset) could
;; be added under an @(tsee mbe) without disturbing anything below.
;;
;; Each walk is characterized by its membership, and the laws that follow are
;; derived from those characterizations by @(see treeset::extensionality)
;; rather than by further induction.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The edges from one source to one target, one for each label.

(define labels-edges (from to (labels treeset::setp))
  :returns (edges treeset::setp)
  (if (treeset::emptyp labels)
      (treeset::empty)
    (treeset::insert
      (edge from to (treeset::min labels))
      (labels-edges from to (treeset::delete (treeset::min labels) labels))))
  :measure (treeset::cardinality labels)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule labels-edges-when-treeset-equiv-of-arg3-congruence
  (implies (treeset::equiv labels0 labels1)
           (equal (labels-edges from to labels0)
                  (labels-edges from to labels1)))
  :rule-classes :congruence
  :expand ((labels-edges from to labels0)
           (labels-edges from to labels1)))

(defruled in-of-labels-edges
  (equal (treeset::in edge (labels-edges from to labels))
         (and (edgep edge)
              (equal (edge->from (double-rewrite edge)) from)
              (equal (edge->to (double-rewrite edge)) to)
              (treeset::in (edge->label (double-rewrite edge)) labels)))
  :induct t
  :enable labels-edges)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The edges out of one source, as recorded by its adjacency.

(define adjacency-edges (from (adj treemap::mapp))
  :guard (map-values-all-nonempty-setp adj)
  :returns (edges treeset::setp)
  (if (treemap::emptyp adj)
      (treeset::empty)
    (b* ((to (treemap::min-key adj)))
      (treeset::union
        (labels-edges from to (treemap::lookup to adj))
        (adjacency-edges from (treemap::delete to adj)))))
  :measure (treemap::size adj)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-edges-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adj0 adj1)
           (equal (adjacency-edges from adj0)
                  (adjacency-edges from adj1)))
  :rule-classes :congruence
  :expand ((adjacency-edges from adj0)
           (adjacency-edges from adj1)))

(defruled in-of-adjacency-edges
  (equal (treeset::in edge (adjacency-edges from adj))
         (and (edgep edge)
              (equal (edge->from (double-rewrite edge)) from)
              (treeset::in (edge->label (double-rewrite edge))
                           (treemap::lookup (edge->to (double-rewrite edge))
                                            adj
                                            :default (treeset::empty)))))
  :induct t
  :enable (adjacency-edges
           in-of-labels-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The edges of the whole list.

(define adj-list-edges ((adjl adj-listp))
  :returns (edges treeset::setp)
  (if (treemap::emptyp adjl)
      (treeset::empty)
    (b* ((from (treemap::min-key adjl)))
      (treeset::union
        (adjacency-edges from (treemap::lookup from adjl))
        (adj-list-edges (treemap::delete from adjl)))))
  :measure (treemap::size adjl)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-edges-when-treemap-equiv-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-edges adjl0)
                  (adj-list-edges adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-edges adjl0)
           (adj-list-edges adjl1)))

(defruled in-of-adj-list-edges
  (equal (treeset::in edge (adj-list-edges adjl))
         (and (edgep edge)
              (treeset::in (edge->label (double-rewrite edge))
                           (treemap::lookup
                             (edge->to (double-rewrite edge))
                             (treemap::lookup (edge->from (double-rewrite edge))
                                              adjl
                                              :default (treemap::empty))
                             :default (treeset::empty)))))
  :induct t
  :enable (adj-list-edges
           in-of-adjacency-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule edgep-when-in-of-labels-edges
  (implies (treeset::in edge (labels-edges from to labels))
           (edgep edge))
  :enable in-of-labels-edges)

(defrule edgep-when-in-of-adjacency-edges
  (implies (treeset::in edge (adjacency-edges from adj))
           (edgep edge))
  :enable in-of-adjacency-edges)

(defrule edgep-when-in-of-adj-list-edges
  (implies (treeset::in edge (adj-list-edges adjl))
           (edgep edge))
  :enable in-of-adj-list-edges)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled labels-edges-when-emptyp
  (implies (treeset::emptyp labels)
           (equal (labels-edges from to labels)
                  (treeset::empty)))
  :enable labels-edges)

(defrule labels-edges-when-emptyp-cheap
  (implies (treeset::emptyp labels)
           (equal (labels-edges from to labels)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by labels-edges-when-emptyp)

(defrule labels-edges-of-empty
  (equal (labels-edges from to (treeset::empty))
         (treeset::empty))
  :enable labels-edges-when-emptyp)

(defruled adjacency-edges-when-emptyp
  (implies (treemap::emptyp adj)
           (equal (adjacency-edges from adj)
                  (treeset::empty)))
  :enable adjacency-edges)

(defrule adjacency-edges-when-emptyp-cheap
  (implies (treemap::emptyp adj)
           (equal (adjacency-edges from adj)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by adjacency-edges-when-emptyp)

(defrule adjacency-edges-of-empty
  (equal (adjacency-edges from (treemap::empty))
         (treeset::empty))
  :enable adjacency-edges-when-emptyp)

(defruled adj-list-edges-when-emptyp
  (implies (treemap::emptyp adjl)
           (equal (adj-list-edges adjl)
                  (treeset::empty)))
  :enable adj-list-edges)

(defrule adj-list-edges-when-emptyp-cheap
  (implies (treemap::emptyp adjl)
           (equal (adj-list-edges adjl)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by adj-list-edges-when-emptyp)

(defrule adj-list-edges-of-empty
  (equal (adj-list-edges (treemap::empty))
         (treeset::empty))
  :enable adj-list-edges-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updating one entry replaces that entry's edges and leaves the rest alone.

(defrule adjacency-edges-of-update
  (equal (adjacency-edges from (treemap::update to labels adj))
         (treeset::union
           (labels-edges from to (double-rewrite labels))
           (adjacency-edges from (treemap::delete to adj))))
  :enable (treeset::extensionality
           in-of-adjacency-edges
           in-of-labels-edges))

(defrule adj-list-edges-of-update
  (equal (adj-list-edges (treemap::update from adj adjl))
         (treeset::union
           (adjacency-edges from (double-rewrite adj))
           (adj-list-edges (treemap::delete from adjl))))
  :enable (treeset::extensionality
           in-of-adj-list-edges
           in-of-adjacency-edges))
