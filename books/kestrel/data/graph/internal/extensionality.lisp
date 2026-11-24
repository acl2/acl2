; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tmap/keys-defs" :dir :system)

(include-book "adj-list-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An adjacency list is determined by its keys and its edge set. The keys are
;; needed only at the top level, where a source may be present with no
;; outgoing edges, which the edge set cannot witness. Within an adjacency, no
;; target is bound to the empty set, so the edge set already says which targets
;; are present. This is where the structural predicate's nonempty label sets
;; earn their keep.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The label set under a source and target is determined by the edge set.

(defruledl lookup-of-lookup-when-equal-of-adj-list-edges
  (implies (and (equal (adj-list-edges x) (adj-list-edges y))
                (adj-listp x)
                (adj-listp y))
           (equal (tmap::lookup to
                                (tmap::lookup from
                                              x
                                              :default (tmap::empty))
                                :default (tset::empty))
                  (tmap::lookup to
                                (tmap::lookup from
                                              y
                                              :default (tmap::empty))
                                :default (tset::empty))))
  :enable (tset::extensionality-no-backchain-limit-polar
           in-of-lookup-of-lookup-becomes-in-of-adj-list-edges))

;; A lookup at any default, read through the label set: a target is bound
;; exactly when its label set is nonempty.

(defruledl lookup-becomes-lookup-with-default-empty
  (implies (and (syntaxp (not (equal default '(tset::empty$inline))))
                (map-values-all-nonempty-setp map))
           (equal (tmap::lookup k map :default default)
                  (if (tset::emptyp
                        (tmap::lookup k map :default (tset::empty)))
                      default
                    (tmap::lookup k map :default (tset::empty)))))
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp
  :use in-of-keys-becomes-not-emptyp-of-lookup-when-map-values-all-nonempty-setp)

;; Hence an adjacency is determined by the edge set as well.

(defruledl lookup-when-equal-of-adj-list-edges
  (implies (and (equal (adj-list-edges x) (adj-list-edges y))
                (adj-listp x)
                (adj-listp y))
           (equal (tmap::lookup from x :default (tmap::empty))
                  (tmap::lookup from y :default (tmap::empty))))
  :enable (tmap::extensionality
           lookup-becomes-lookup-with-default-empty)
  :use (:instance
         lookup-of-lookup-when-equal-of-adj-list-edges
         (to (mv-nth 0 (tmap::ext-equal-witness
                         (tmap::lookup from x :default (tmap::empty))
                         (tmap::lookup from y :default (tmap::empty)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The adj-list- prefix leaves the bare name for the public graph theorem.

(defruled adj-list-extensionality
  (implies (and (adj-listp x)
                (adj-listp y)
                (tmap::equiv x$ (double-rewrite x))
                (tmap::equiv y$ (double-rewrite y)))
           (equal (equal x y)
                  (and (equal (tmap::keys x$)
                              (tmap::keys y$))
                       (equal (adj-list-edges x$)
                              (adj-list-edges y$)))))
  :enable (tmap::extensionality-polar
           tmap::lookup-with-default-becomes-lookup-syntaxp)
  :use (:instance lookup-when-equal-of-adj-list-edges
                  (from (mv-nth 0 (tmap::ext-equal-witness x y)))))
