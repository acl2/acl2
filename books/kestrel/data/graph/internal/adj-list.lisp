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
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/values-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/values" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/generic-typed" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An adjacency list is a @(see treemap::treemap) from each source node to its
;; adjacency, and an adjacency is a treemap from each target node to the set of
;; labels on the edges from the source to that target. A target with no edges
;; is absent from the adjacency rather than bound to the empty set, so every
;; label set is nonempty. This is the structural predicate: it constrains each
;; value on its own, and says nothing relating the keys of one map to another.
;;
;; Each level is built the same way. The check is an instance of @(see
;; treeset::generic-typed)'s all-elements predicate, and each law is the
;; corresponding generic law functionally instantiated.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check over a value @(see acl2::treeset), by repeatedly taking the
;; minimum. This is the shape @(tsee treeset::set-all-genericp) recurses in, so
;; it is the function the generic laws are instantiated at.

(define set-all-nonempty-setp ((set treeset::setp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (or (treeset::emptyp set)
      (and (treeset::setp (treeset::min set))
           (not (treeset::emptyp (treeset::min set)))
           (set-all-nonempty-setp (treeset::delete (treeset::min set) set))))
  :measure (treeset::cardinality set)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-nonempty-setp-type-prescription
  (booleanp (set-all-nonempty-setp set))
  :rule-classes ((:type-prescription :typed-term (set-all-nonempty-setp set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check run as a single walk over the map's own tree, reading the
;; value at every node. This builds no value treeset, so it is what the
;; recognizer executes.

(define tree-all-vals-nonempty-setp ((tree treemap::treep))
  (or (treemap::tree-empty-p tree)
      (and (treeset::setp
             (treemap::tree-element->val (treemap::tree->head tree)))
           (not (treeset::emptyp
                  (treemap::tree-element->val (treemap::tree->head tree))))
           (tree-all-vals-nonempty-setp (treemap::tree->left tree))
           (tree-all-vals-nonempty-setp (treemap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values
  (implies (treemap::mapp map)
           (equal (tree-all-vals-nonempty-setp map)
                  (set-all-nonempty-setp
                    (treemap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treeset::setp x)
                                               (not (treeset::emptyp x)))))
           (treeset::set-all-genericp set-all-nonempty-setp)
           (treemap::tree-all-vals-genericp tree-all-vals-nonempty-setp))
         (treemap::map map))
  :enable (set-all-nonempty-setp
           tree-all-vals-nonempty-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The invariant on an adjacency: every value is a nonempty treeset. The
;; logical form is the treeset check over @(tsee treemap::values), which is
;; where the generic laws land; the walk above is the execution.
;;
;; Time complexity: @($O(n)$).

(define map-values-all-nonempty-setp ((map treemap::mapp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (mbe :logic (set-all-nonempty-setp (treemap::values map))
       :exec (tree-all-vals-nonempty-setp map))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values
            treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-nonempty-setp-type-prescription
  (booleanp (map-values-all-nonempty-setp map))
  :rule-classes ((:type-prescription
                   :typed-term (map-values-all-nonempty-setp map))))

(defrule map-values-all-nonempty-setp-when-treemap-equiv-congruence
  (implies (treemap::equiv map0 map1)
           (equal (map-values-all-nonempty-setp map0)
                  (map-values-all-nonempty-setp map1)))
  :rule-classes :congruence
  :enable map-values-all-nonempty-setp)

(defrule tree-all-vals-nonempty-setp-when-map-values-all-nonempty-setp
  (implies (and (treemap::mapp map)
                (map-values-all-nonempty-setp (double-rewrite map)))
           (tree-all-vals-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values))

(defruled map-values-all-nonempty-setp-when-tree-all-vals-nonempty-setp
  (implies (and (treemap::mapp map)
                (tree-all-vals-nonempty-setp map))
           (map-values-all-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           tree-all-vals-nonempty-setp-becomes-set-all-nonempty-setp-of-values))

(defruled map-values-all-nonempty-setp-when-emptyp
  (implies (treemap::emptyp map)
           (map-values-all-nonempty-setp map))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule map-values-all-nonempty-setp-when-emptyp-cheap
  (implies (treemap::emptyp map)
           (map-values-all-nonempty-setp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-nonempty-setp-when-emptyp)

(defrule map-values-all-nonempty-setp-of-empty
  (map-values-all-nonempty-setp (treemap::empty))
  :enable map-values-all-nonempty-setp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule setp-of-lookup-when-map-values-all-nonempty-setp
  (implies (and (map-values-all-nonempty-setp map)
                (treemap::in k map))
           (treeset::setp (treemap::lookup k map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treeset::setp x)
                                               (not (treeset::emptyp x)))))
           (treeset::set-all-genericp set-all-nonempty-setp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule emptyp-of-lookup-when-map-values-all-nonempty-setp
  (implies (and (map-values-all-nonempty-setp map)
                (treemap::in k map))
           (not (treeset::emptyp (treemap::lookup k map))))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treeset::setp x)
                                               (not (treeset::emptyp x)))))
           (treeset::set-all-genericp set-all-nonempty-setp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

;; The weaker consequence, for a caller reading the empty set at an absent
;; target: the result is a set whether or not the target is present, and the
;; membership hypothesis drops away.

(defrule setp-of-lookup-with-default-empty-when-map-values-all-nonempty-setp
  (implies (map-values-all-nonempty-setp map)
           (treeset::setp (treemap::lookup k map :default (treeset::empty))))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

;; Since no key is bound to the empty set, a key is present exactly when its
;; label set is nonempty, so the label sets alone determine the keys.

(defruled in-of-keys-becomes-not-emptyp-of-lookup-when-map-values-all-nonempty-setp
  (implies (map-values-all-nonempty-setp map)
           (equal (treeset::in k (treemap::keys map))
                  (not (treeset::emptyp
                         (treemap::lookup k map :default (treeset::empty))))))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

;; One direction holds of any map: an absent key reads as the empty set, so a
;; key with a nonempty label set is present.

(defrule in-of-keys-when-not-emptyp-of-lookup-with-default-empty-forward-chaining
  (implies (not (treeset::emptyp
                  (treemap::lookup k map :default (treeset::empty))))
           (treeset::in k (treemap::keys map)))
  :rule-classes :forward-chaining
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule in-of-keys-when-in-of-lookup-with-default-empty-forward-chaining
  (implies (treeset::in x (treemap::lookup k map :default (treeset::empty)))
           (treeset::in k (treemap::keys map)))
  :rule-classes :forward-chaining
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-nonempty-setp-of-update
  (equal (map-values-all-nonempty-setp (treemap::update k v map))
         (and (treeset::setp v)
              (not (treeset::emptyp (double-rewrite v)))
              (map-values-all-nonempty-setp (treemap::delete k map))))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-update
           (treeset::genericp (lambda (x) (and (treeset::setp x)
                                               (not (treeset::emptyp x)))))
           (treeset::set-all-genericp set-all-nonempty-setp))
         (treemap::map map)
         (treemap::k k)
         (treemap::v v))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

(defrule map-values-all-nonempty-setp-of-delete
  (implies (map-values-all-nonempty-setp map)
           (map-values-all-nonempty-setp (treemap::delete k map)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-delete
           (treeset::genericp (lambda (x) (and (treeset::setp x)
                                               (not (treeset::emptyp x)))))
           (treeset::set-all-genericp set-all-nonempty-setp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-nonempty-setp
           set-all-nonempty-setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same three functions one level up, for the adjacency list itself: every
;; value is a treemap satisfying @(tsee map-values-all-nonempty-setp). An
;; adjacency has no recognizer of its own; the element condition is the
;; conjunction spelled out.

(define set-all-adjacencyp ((set treeset::setp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (or (treeset::emptyp set)
      (and (treemap::mapp (treeset::min set))
           (map-values-all-nonempty-setp (treeset::min set))
           (set-all-adjacencyp (treeset::delete (treeset::min set) set))))
  :measure (treeset::cardinality set)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-adjacencyp-type-prescription
  (booleanp (set-all-adjacencyp set))
  :rule-classes ((:type-prescription :typed-term (set-all-adjacencyp set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-all-vals-adjacencyp ((tree treemap::treep))
  (or (treemap::tree-empty-p tree)
      (and (treemap::mapp
             (treemap::tree-element->val (treemap::tree->head tree)))
           (map-values-all-nonempty-setp
             (treemap::tree-element->val (treemap::tree->head tree)))
           (tree-all-vals-adjacencyp (treemap::tree->left tree))
           (tree-all-vals-adjacencyp (treemap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values
  (implies (treemap::mapp map)
           (equal (tree-all-vals-adjacencyp map)
                  (set-all-adjacencyp (treemap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treemap::mapp x)
                                               (map-values-all-nonempty-setp
                                                 x))))
           (treeset::set-all-genericp set-all-adjacencyp)
           (treemap::tree-all-vals-genericp tree-all-vals-adjacencyp))
         (treemap::map map))
  :enable (set-all-adjacencyp
           tree-all-vals-adjacencyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Time complexity: @($O(n + m)$), where @($n$) is the number of source nodes
;; and @($m$) the total number of targets over all adjacencies.

(define map-values-all-adjacencyp ((map treemap::mapp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (mbe :logic (set-all-adjacencyp (treemap::values map))
       :exec (tree-all-vals-adjacencyp map))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values
            treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-adjacencyp-type-prescription
  (booleanp (map-values-all-adjacencyp map))
  :rule-classes ((:type-prescription
                   :typed-term (map-values-all-adjacencyp map))))

(defrule map-values-all-adjacencyp-when-treemap-equiv-congruence
  (implies (treemap::equiv map0 map1)
           (equal (map-values-all-adjacencyp map0)
                  (map-values-all-adjacencyp map1)))
  :rule-classes :congruence
  :enable map-values-all-adjacencyp)

(defrule tree-all-vals-adjacencyp-when-map-values-all-adjacencyp
  (implies (and (treemap::mapp map)
                (map-values-all-adjacencyp (double-rewrite map)))
           (tree-all-vals-adjacencyp map))
  :enable (map-values-all-adjacencyp
           tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values))

(defruled map-values-all-adjacencyp-when-tree-all-vals-adjacencyp
  (implies (and (treemap::mapp map)
                (tree-all-vals-adjacencyp map))
           (map-values-all-adjacencyp map))
  :enable (map-values-all-adjacencyp
           tree-all-vals-adjacencyp-becomes-set-all-adjacencyp-of-values))

(defruled map-values-all-adjacencyp-when-emptyp
  (implies (treemap::emptyp map)
           (map-values-all-adjacencyp map))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-adjacencyp-when-emptyp-cheap
  (implies (treemap::emptyp map)
           (map-values-all-adjacencyp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-adjacencyp-when-emptyp)

(defrule map-values-all-adjacencyp-of-empty
  (map-values-all-adjacencyp (treemap::empty))
  :enable map-values-all-adjacencyp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule mapp-of-lookup-when-map-values-all-adjacencyp
  (implies (and (map-values-all-adjacencyp map)
                (treemap::in k map))
           (treemap::mapp (treemap::lookup k map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treemap::mapp x)
                                               (map-values-all-nonempty-setp
                                                 x))))
           (treeset::set-all-genericp set-all-adjacencyp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-nonempty-setp-of-lookup-when-map-values-all-adjacencyp
  (implies (and (map-values-all-adjacencyp map)
                (treemap::in k map))
           (map-values-all-nonempty-setp (treemap::lookup k map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp (lambda (x) (and (treemap::mapp x)
                                               (map-values-all-nonempty-setp
                                                 x))))
           (treeset::set-all-genericp set-all-adjacencyp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

;; Unlike a label set, the empty adjacency is itself an adjacency: a source
;; absent from the list reads as one with no outgoing edges.

(defrule mapp-of-lookup-with-default-empty-when-map-values-all-adjacencyp
  (implies (map-values-all-adjacencyp map)
           (treemap::mapp (treemap::lookup k map :default (treemap::empty))))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-nonempty-setp-of-lookup-with-default-empty-when-map-values-all-adjacencyp
  (implies (map-values-all-adjacencyp map)
           (map-values-all-nonempty-setp
             (treemap::lookup k map :default (treemap::empty))))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-adjacencyp-of-update
  (equal (map-values-all-adjacencyp (treemap::update k v map))
         (and (treemap::mapp v)
              (map-values-all-nonempty-setp (double-rewrite v))
              (map-values-all-adjacencyp (treemap::delete k map))))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-update
           (treeset::genericp (lambda (x) (and (treemap::mapp x)
                                               (map-values-all-nonempty-setp
                                                 x))))
           (treeset::set-all-genericp set-all-adjacencyp))
         (treemap::map map)
         (treemap::k k)
         (treemap::v v))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

(defrule map-values-all-adjacencyp-of-delete
  (implies (map-values-all-adjacencyp map)
           (map-values-all-adjacencyp (treemap::delete k map)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-delete
           (treeset::genericp (lambda (x) (and (treemap::mapp x)
                                               (map-values-all-nonempty-setp
                                                 x))))
           (treeset::set-all-genericp set-all-adjacencyp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-adjacencyp
           set-all-adjacencyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The structural predicate. It is enabled, so it is only ever an abbreviation
;; for its two conjuncts, and rules are stated over those.

(define adj-listp (x)
  (and (treemap::mapp x)
       (map-values-all-adjacencyp x))
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy adj-list-extra-rules
  '(map-values-all-nonempty-setp-when-emptyp
    map-values-all-adjacencyp-when-emptyp
    ))
