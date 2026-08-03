; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/keys-defs")
(include-book "internal/lookup-defs")
(include-book "internal/rotate-defs")
(include-book "internal/join-defs")
(include-book "internal/delete-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "update-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/rotate"))
(local (include-book "internal/join"))
(local (include-book "internal/delete"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))
(local (include-book "map"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "update"))
(local (include-book "delete"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The count of a treemap is structural: one per entry, walking the map's own
;; tree. It cannot be composed from counts of the key and value treesets,
;; since the value treeset collapses values shared by distinct keys.

(encapsulate
  (((generic-count * *) => *))

  (local
    (define generic-count (key val)
      (declare (ignore key val))
      0))

  (defrule natp-of-generic-count-type-prescription
    (natp (generic-count key val))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable generic-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-generic-count ((tree treep))
  :returns (count natp :rule-classes :type-prescription)
  (if (tree-empty-p tree)
      0
    (+ 1
       (generic-count (tree-element->key (tree->head tree))
                      (tree-element->val (tree->head tree)))
       (tree-generic-count (tree->left tree))
       (tree-generic-count (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-generic-count)))

(defrule tree-generic-count-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-generic-count tree0)
                  (tree-generic-count tree1)))
  :rule-classes :congruence
  :expand ((tree-generic-count tree0)
           (tree-generic-count tree1)))

(defruled equal-of-tree-generic-count-and-0-becomes-tree-empty-p
  (equal (equal (tree-generic-count tree) 0)
         (tree-empty-p tree))
  :induct t
  :enable (tree-generic-count
           tree-empty-p))

(defrule tree-generic-count-when-tree-empty-p-forward-chaining
  (implies (tree-empty-p tree)
           (equal (tree-generic-count tree) 0))
  :rule-classes :forward-chaining
  :enable equal-of-tree-generic-count-and-0-becomes-tree-empty-p)

(defrule tree-empty-p-when-equal-tree-generic-count-and-0-forward-chaining
  (implies (equal (tree-generic-count tree) 0)
           (tree-empty-p tree))
  :rule-classes :forward-chaining
  :enable equal-of-tree-generic-count-and-0-becomes-tree-empty-p)

(defrule tree-generic-count-of-rotate-left
  (implies (not (tree-empty-p (tree->right tree)))
           (equal (tree-generic-count (rotate-left tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count
           rotate-left))

(defrule tree-generic-count-of-rotate-right
  (implies (not (tree-empty-p (tree->left tree)))
           (equal (tree-generic-count (rotate-right tree))
                  (tree-generic-count tree)))
  :enable (tree-generic-count
           rotate-right))

(defrule tree-generic-count-of-tree-join
  (equal (tree-generic-count (tree-join left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :induct t
  :enable (tree-generic-count
           tree-join))

(defrule tree-generic-count-of-tree-join-at
  (equal (tree-generic-count (tree-join-at split left right))
         (+ (tree-generic-count left)
            (tree-generic-count right)))
  :enable (tree-generic-count
           tree-join-at))

;; The induction is tree-delete's own. The default merged scheme also draws
;; on tree-lookup, whose recursion is guided by key treeset membership rather
;; than <<, and the merge misshapes the inductive hypotheses.
(defrule tree-generic-count-of-tree-delete
  (implies (bstp tree)
           (equal (tree-generic-count (tree-delete key tree))
                  (if (treeset::in key (tree-key-set tree))
                      (- (tree-generic-count tree)
                         (+ 1 (generic-count key (tree-lookup key tree))))
                    (tree-generic-count tree))))
  :induct (tree-delete key tree)
  :enable (tree-delete
           tree-generic-count
           tree-lookup
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define map-generic-count ((map mapp))
  :returns (count natp :rule-classes :type-prescription)
  (tree-generic-count (fix map))
  :guard-hints (("Goal" :in-theory (enable mapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t map-generic-count)))

(defruled map-generic-count-when-emptyp
  (implies (emptyp map)
           (equal (map-generic-count map) 0))
  :enable (map-generic-count
           emptyp))

(defrule map-generic-count-when-emptyp-cheap
  (implies (emptyp map)
           (equal (map-generic-count map) 0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-generic-count-when-emptyp)

(defrule map-generic-count-of-empty
  (equal (map-generic-count (empty)) 0)
  :enable map-generic-count-when-emptyp)

(defruled map-generic-count-of-delete
  (equal (map-generic-count (delete key map))
         (if (treeset::in key (keys map))
             (- (map-generic-count map)
                (+ 1 (generic-count key (lookup key map))))
           (map-generic-count map)))
  :enable (map-generic-count
           delete
           keys
           lookup
           mapp
           break-abstraction))

(defrule map-generic-count-of-delete-when-in
  (implies (treeset::in key (keys map))
           (equal (map-generic-count (delete key map))
                  (- (map-generic-count map)
                     (+ 1 (generic-count key (lookup key map))))))
  :enable map-generic-count-of-delete)

(defrule map-generic-count-of-update
  (equal (map-generic-count (update key val map))
         (+ 1
            (generic-count key val)
            (map-generic-count (delete key map))))
  :use ((:instance map-generic-count-of-delete-when-in
                   (map (update key val map))))
  :disable map-generic-count-of-delete-when-in
  :enable treeset::in-of-insert)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule generic-count-<-map-generic-count-when-in
  (implies (treeset::in key (keys map))
           (< (generic-count key (lookup key map))
              (map-generic-count map)))
  :rule-classes :linear
  :use map-generic-count-of-delete-when-in
  :disable map-generic-count-of-delete-when-in)

(defrule map-generic-count-of-delete-<-map-generic-count-when-in
  (implies (treeset::in key (keys map))
           (< (map-generic-count (delete key map))
              (map-generic-count map)))
  :rule-classes :linear
  :use map-generic-count-of-delete-when-in
  :disable map-generic-count-of-delete-when-in)

(defrule generic-count-of-min-<-map-generic-count
  (implies (not (emptyp map))
           (< (generic-count (treeset::min (keys map))
                             (lookup (treeset::min (keys map)) map))
              (map-generic-count map)))
  :rule-classes :linear
  :use (:instance generic-count-<-map-generic-count-when-in
                  (key (treeset::min (keys map))))
  :disable generic-count-<-map-generic-count-when-in)

(defrule map-generic-count-of-delete-min-<-map-generic-count
  (implies (not (emptyp map))
           (< (map-generic-count (delete (treeset::min (keys map)) map))
              (map-generic-count map)))
  :rule-classes :linear
  :use (:instance map-generic-count-of-delete-<-map-generic-count-when-in
                  (key (treeset::min (keys map))))
  :disable map-generic-count-of-delete-<-map-generic-count-when-in)

(defrule generic-count-of-head-<-map-generic-count
  (implies (not (emptyp map))
           (< (generic-count (head-key map)
                             (lookup (head-key map) map))
              (map-generic-count map)))
  :rule-classes :linear
  :use (:instance generic-count-<-map-generic-count-when-in
                  (key (head-key map)))
  :disable generic-count-<-map-generic-count-when-in)

(defrule map-generic-count-of-delete-head-<-map-generic-count
  (implies (not (emptyp map))
           (< (map-generic-count (delete (head-key map) map))
              (map-generic-count map)))
  :rule-classes :linear
  :use (:instance map-generic-count-of-delete-<-map-generic-count-when-in
                  (key (head-key map)))
  :disable map-generic-count-of-delete-<-map-generic-count-when-in)
