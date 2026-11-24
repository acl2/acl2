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
(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/values-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/to-omap-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/values" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/generic-typed" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/to-omap" :dir :system))
(local (include-book "kestrel/data/tmap/induction" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An adjacency list is a @(see tmap::tmap) from each source node to its
;; adjacency, and an adjacency is a tmap from each target node to the set of
;; labels on the edges from the source to that target. A target with no edges
;; is absent from the adjacency rather than bound to the empty set, so every
;; label set is nonempty. This is the structural predicate: it constrains each
;; value on its own, and says nothing relating the keys of one map to another.
;;
;; Each level is built the same way. The check is an instance of @(see
;; tset::generic-typed)'s all-elements predicate, and each law is the
;; corresponding generic law functionally instantiated.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check over a value @(see acl2::tset), by repeatedly taking the
;; minimum. This is the shape @(tsee tset::set-all-genericp) recurses in, so
;; it is the function the generic laws are instantiated at.

(define set-all-nonempty-setp ((set tset::setp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tset::emptyp set)
      (and (tset::setp (tset::min set))
           (not (tset::emptyp (tset::min set)))
           (set-all-nonempty-setp (tset::delete (tset::min set) set))))
  :measure (tset::cardinality set)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check run as a single walk over the map's own tree, reading the
;; value at every node. This builds no value tset, so it is what the
;; recognizer executes.

(define tree-all-vals-nonempty-setp ((tree tmap::treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tmap::tree-empty-p tree)
      (and (tset::setp
             (tmap::tree-element->val (tmap::tree->head tree)))
           (not (tset::emptyp
                  (tmap::tree-element->val (tmap::tree->head tree))))
           (tree-all-vals-nonempty-setp (tmap::tree->left tree))
           (tree-all-vals-nonempty-setp (tmap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values
  (implies (tmap::mapp map)
           (equal (tree-all-vals-nonempty-setp map)
                  (set-all-nonempty-setp
                    (tmap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp)
           (tmap::tree-all-vals-genericp tree-all-vals-nonempty-setp))
         (tmap::map map))
  :enable (set-all-nonempty-setp
           tree-all-vals-nonempty-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The invariant on an adjacency: every value is a nonempty tset. The
;; logical form is the tset check over @(tsee tmap::values), which is
;; where the generic laws land; the walk above is the execution.
;;
;; Time complexity: @($O(n)$).

(define map-values-all-nonempty-setp ((map tmap::mapp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (set-all-nonempty-setp (tmap::values map))
       :exec (tree-all-vals-nonempty-setp map))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values
            tmap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-nonempty-setp-when-tmap-equiv-congruence
  (implies (tmap::equiv map0 map1)
           (equal (map-values-all-nonempty-setp map0)
                  (map-values-all-nonempty-setp map1)))
  :rule-classes :congruence
  :enable map-values-all-nonempty-setp)

(defrule tree-all-vals-nonempty-setp-when-map-values-all-nonempty-setp
  (implies (and (tmap::mapp map)
                (map-values-all-nonempty-setp (double-rewrite map)))
           (tree-all-vals-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values))

(defruled map-values-all-nonempty-setp-when-tree-all-vals-nonempty-setp
  (implies (and (tmap::mapp map)
                (tree-all-vals-nonempty-setp map))
           (map-values-all-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values))

(defruled map-values-all-nonempty-setp-when-emptyp
  (implies (tmap::emptyp map)
           (map-values-all-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule map-values-all-nonempty-setp-when-emptyp-cheap
  (implies (tmap::emptyp map)
           (map-values-all-nonempty-setp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-nonempty-setp-when-emptyp)

(defrule map-values-all-nonempty-setp-of-empty
  (map-values-all-nonempty-setp (tmap::empty))
  :enable map-values-all-nonempty-setp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-lookup-when-map-values-all-nonempty-setp
  (implies (and (map-values-all-nonempty-setp map)
                (tmap::in k map))
           (tset::setp (tmap::lookup k map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-lookup-when-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule emptyp-of-lookup-when-map-values-all-nonempty-setp
  (implies (and (map-values-all-nonempty-setp map)
                (tmap::in k map))
           (not (tset::emptyp (tmap::lookup k map))))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-lookup-when-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

;; The weaker consequence, for a caller reading the empty set at an absent
;; target: the result is a set whether or not the target is present, and the
;; membership hypothesis drops away.

(defrule setp-of-lookup-with-default-empty-when-map-values-all-nonempty-setp
  (implies (map-values-all-nonempty-setp map)
           (tset::setp (tmap::lookup k map :default (tset::empty))))
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

;; Since no key is bound to the empty set, a key is present exactly when its
;; label set is nonempty, so the label sets alone determine the keys.

(defruled in-of-keys-becomes-not-emptyp-of-lookup-when-map-values-all-nonempty-setp
  (implies (map-values-all-nonempty-setp map)
           (equal (tset::in k (tmap::keys map))
                  (not (tset::emptyp
                         (tmap::lookup k map :default (tset::empty))))))
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

;; One direction holds of any map: an absent key reads as the empty set, so a
;; key with a nonempty label set is present.

(defrule in-of-keys-when-not-emptyp-of-lookup-with-default-empty-forward-chaining
  (implies (not (tset::emptyp
                  (tmap::lookup k map :default (tset::empty))))
           (tset::in k (tmap::keys map)))
  :rule-classes :forward-chaining
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

(defrule in-of-keys-when-in-of-lookup-with-default-empty-forward-chaining
  (implies (tset::in x (tmap::lookup k map :default (tset::empty)))
           (tset::in k (tmap::keys map)))
  :rule-classes :forward-chaining
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-nonempty-setp-of-update
  (equal (map-values-all-nonempty-setp (tmap::update k v map))
         (and (tset::setp v)
              (not (tset::emptyp (double-rewrite v)))
              (map-values-all-nonempty-setp (tmap::delete k map))))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-update
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp))
         (tmap::map map)
         (tmap::k k)
         (tmap::v v))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule map-values-all-nonempty-setp-of-delete
  (implies (map-values-all-nonempty-setp map)
           (map-values-all-nonempty-setp (tmap::delete k map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defruledl map-values-all-nonempty-setp-of-delete-when-in
  (implies (and (tset::in k (tmap::keys map))
                (tset::setp (tmap::lookup k map))
                (not (tset::emptyp (tmap::lookup k map))))
           (equal (map-values-all-nonempty-setp (tmap::delete k map))
                  (map-values-all-nonempty-setp map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete-when-in
           (tset::genericp (lambda (x) (and (tset::setp x)
                                            (not (tset::emptyp x)))))
           (tset::set-all-genericp set-all-nonempty-setp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same invariant over an omap, for walking an adjacency as the omap of
;; its entries. On the omap of a tmap it is the invariant on the tmap.

(define omap-values-all-nonempty-setp ((omap omap::mapp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (omap::emptyp omap)
      (b* (((mv - labels) (omap::head omap)))
        (and (tset::setp labels)
             (not (tset::emptyp labels))
             (omap-values-all-nonempty-setp (omap::tail omap))))))

;;;;;;;;;;;;;;;;;;;;

(defrule omap-values-all-nonempty-setp-of-to-omap
  (equal (omap-values-all-nonempty-setp (tmap::to-omap map))
         (map-values-all-nonempty-setp map))
  :induct (tmap::min-delete-induction map)
  :enable (omap-values-all-nonempty-setp
           map-values-all-nonempty-setp-of-delete-when-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same functions one level up, for the adjacency list itself: every
;; value is a tmap satisfying @(tsee map-values-all-nonempty-setp). An
;; adjacency has no recognizer of its own; the element condition is the
;; conjunction spelled out.

(define set-all-adjacencyp ((set tset::setp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tset::emptyp set)
      (and (tmap::mapp (tset::min set))
           (map-values-all-nonempty-setp (tset::min set))
           (set-all-adjacencyp (tset::delete (tset::min set) set))))
  :measure (tset::cardinality set)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-all-vals-adjacencyp ((tree tmap::treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tmap::tree-empty-p tree)
      (and (tmap::mapp
             (tmap::tree-element->val (tmap::tree->head tree)))
           (map-values-all-nonempty-setp
             (tmap::tree-element->val (tmap::tree->head tree)))
           (tree-all-vals-adjacencyp (tmap::tree->left tree))
           (tree-all-vals-adjacencyp (tmap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values
  (implies (tmap::mapp map)
           (equal (tree-all-vals-adjacencyp map)
                  (set-all-adjacencyp (tmap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp)
           (tmap::tree-all-vals-genericp tree-all-vals-adjacencyp))
         (tmap::map map))
  :enable (set-all-adjacencyp
           tree-all-vals-adjacencyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Time complexity: @($O(n + m)$), where @($n$) is the number of source nodes
;; and @($m$) the total number of targets over all adjacencies.

(define map-values-all-adjacencyp ((map tmap::mapp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (set-all-adjacencyp (tmap::values map))
       :exec (tree-all-vals-adjacencyp map))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values
            tmap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-adjacencyp-when-tmap-equiv-congruence
  (implies (tmap::equiv map0 map1)
           (equal (map-values-all-adjacencyp map0)
                  (map-values-all-adjacencyp map1)))
  :rule-classes :congruence
  :enable map-values-all-adjacencyp)

(defrule tree-all-vals-adjacencyp-when-map-values-all-adjacencyp
  (implies (and (tmap::mapp map)
                (map-values-all-adjacencyp (double-rewrite map)))
           (tree-all-vals-adjacencyp map))
  :enable (map-values-all-adjacencyp
           tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values))

(defruled map-values-all-adjacencyp-when-tree-all-vals-adjacencyp
  (implies (and (tmap::mapp map)
                (tree-all-vals-adjacencyp map))
           (map-values-all-adjacencyp map))
  :enable (map-values-all-adjacencyp
           tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values))

(defruled map-values-all-adjacencyp-when-emptyp
  (implies (tmap::emptyp map)
           (map-values-all-adjacencyp map))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-adjacencyp-when-emptyp-cheap
  (implies (tmap::emptyp map)
           (map-values-all-adjacencyp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-adjacencyp-when-emptyp)

(defrule map-values-all-adjacencyp-of-empty
  (map-values-all-adjacencyp (tmap::empty))
  :enable map-values-all-adjacencyp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule mapp-of-lookup-when-map-values-all-adjacencyp
  (implies (and (map-values-all-adjacencyp map)
                (tmap::in k map))
           (tmap::mapp (tmap::lookup k map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-lookup-when-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-nonempty-setp-of-lookup-when-map-values-all-adjacencyp
  (implies (and (map-values-all-adjacencyp map)
                (tmap::in k map))
           (map-values-all-nonempty-setp (tmap::lookup k map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-lookup-when-set-all-genericp-of-values
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

;; Unlike a label set, the empty adjacency is itself an adjacency: a source
;; absent from the list reads as one with no outgoing edges.

(defrule mapp-of-lookup-with-default-empty-when-map-values-all-adjacencyp
  (implies (map-values-all-adjacencyp map)
           (tmap::mapp (tmap::lookup k map :default (tmap::empty))))
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-nonempty-setp-of-lookup-with-default-empty-when-map-values-all-adjacencyp
  (implies (map-values-all-adjacencyp map)
           (map-values-all-nonempty-setp
             (tmap::lookup k map :default (tmap::empty))))
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-adjacencyp-of-update
  (equal (map-values-all-adjacencyp (tmap::update k v map))
         (and (tmap::mapp v)
              (map-values-all-nonempty-setp (double-rewrite v))
              (map-values-all-adjacencyp (tmap::delete k map))))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-update
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp))
         (tmap::map map)
         (tmap::k k)
         (tmap::v v))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-adjacencyp-of-delete
  (implies (map-values-all-adjacencyp map)
           (map-values-all-adjacencyp (tmap::delete k map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defruledl map-values-all-adjacencyp-of-delete-when-in
  (implies (and (tset::in k (tmap::keys map))
                (tmap::mapp (tmap::lookup k map))
                (map-values-all-nonempty-setp (tmap::lookup k map)))
           (equal (map-values-all-adjacencyp (tmap::delete k map))
                  (map-values-all-adjacencyp map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete-when-in
           (tset::genericp (lambda (x) (and (tmap::mapp x)
                                            (map-values-all-nonempty-setp
                                              x))))
           (tset::set-all-genericp set-all-adjacencyp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define omap-values-all-adjacencyp ((omap omap::mapp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (omap::emptyp omap)
      (b* (((mv - adj) (omap::head omap)))
        (and (tmap::mapp adj)
             (map-values-all-nonempty-setp adj)
             (omap-values-all-adjacencyp (omap::tail omap))))))

;;;;;;;;;;;;;;;;;;;;

(defrule omap-values-all-adjacencyp-of-to-omap
  (equal (omap-values-all-adjacencyp (tmap::to-omap map))
         (map-values-all-adjacencyp map))
  :induct (tmap::min-delete-induction map)
  :enable (omap-values-all-adjacencyp
           map-values-all-adjacencyp-of-delete-when-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The structural predicate. It is enabled, so it is only ever an abbreviation
;; for its two conjuncts, and rules are stated over those.

(define adj-listp (x)
  (and (tmap::mapp x)
       (map-values-all-adjacencyp x))
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy adj-list-extra-rules
  '(map-values-all-nonempty-setp-when-emptyp
    map-values-all-adjacencyp-when-emptyp
    ))
