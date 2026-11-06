; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treemap/keys-defs" :dir :system)

(include-book "adj-list-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

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
           (equal (treemap::lookup to
                                   (treemap::lookup from
                                                    x
                                                    :default (treemap::empty))
                                   :default (treeset::empty))
                  (treemap::lookup to
                                   (treemap::lookup from
                                                    y
                                                    :default (treemap::empty))
                                   :default (treeset::empty))))
  :enable (treeset::extensionality-no-backchain-limit-polar
           in-of-lookup-of-lookup-becomes-in-of-adj-list-edges))

;; A lookup at any default, read through the label set: a target is bound
;; exactly when its label set is nonempty.

(defruledl lookup-becomes-lookup-with-default-empty
  (implies (and (syntaxp (not (equal default '(treeset::empty$inline))))
                (map-values-all-nonempty-setp map))
           (equal (treemap::lookup k map :default default)
                  (if (treeset::emptyp
                        (treemap::lookup k map :default (treeset::empty)))
                      default
                    (treemap::lookup k map :default (treeset::empty)))))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp
  :use in-of-keys-becomes-not-emptyp-of-lookup-when-map-values-all-nonempty-setp)

;; Hence an adjacency is determined by the edge set as well.

(defruledl lookup-when-equal-of-adj-list-edges
  (implies (and (equal (adj-list-edges x) (adj-list-edges y))
                (adj-listp x)
                (adj-listp y))
           (equal (treemap::lookup from x :default (treemap::empty))
                  (treemap::lookup from y :default (treemap::empty))))
  :enable (treemap::extensionality
           lookup-becomes-lookup-with-default-empty)
  :use (:instance
         lookup-of-lookup-when-equal-of-adj-list-edges
         (to (mv-nth 0 (treemap::ext-equal-witness
                         (treemap::lookup from x :default (treemap::empty))
                         (treemap::lookup from y :default (treemap::empty)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The adj-list- prefix leaves the bare name for the public graph theorem.

(defruled adj-list-extensionality
  (implies (and (adj-listp x)
                (adj-listp y))
           (equal (equal x y)
                  (and (equal (treemap::keys (double-rewrite x))
                              (treemap::keys (double-rewrite y)))
                       (equal (adj-list-edges (double-rewrite x))
                              (adj-list-edges (double-rewrite y))))))
  :enable (treemap::extensionality-polar
           treemap::lookup-with-default-becomes-lookup-syntaxp)
  :use (:instance lookup-when-equal-of-adj-list-edges
                  (from (mv-nth 0 (treemap::ext-equal-witness x y)))))
