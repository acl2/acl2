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
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/bst-defs")
(include-book "internal/heap-defs")
(include-book "internal/keys-defs")
(include-book "internal/lookup-defs")
(include-book "internal/split-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "values-defs")
(include-book "generic-typed")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/internal/heap-order" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/split"))
(local (include-book "map"))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A union of two treemaps which combines the values of a key bound in both.
;; The combining function sees the key and the two values, the first map's
;; value first. Its one constraint is that it preserves the generic value
;; predicate of @(see treeset::generic-typed), so that a union of typed maps
;; is typed. A use with no value type instantiates that predicate to accept
;; everything, which discharges the constraint trivially.

(encapsulate
  (((generic-combine * * *) => *))

  (local
    (define generic-combine (key x y)
      (declare (ignore key x))
      y))

  (defrule genericp-of-generic-combine
    (implies (and (treeset::genericp x)
                  (treeset::genericp y))
             (treeset::genericp (generic-combine key x y)))
    :hints (("Goal" :in-theory (enable generic-combine)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The recursion is that of tree-update*. That union is the instance which
;; returns the first map's value.

(define tree-generic-union
  ((x treep)
   (y treep))
  :returns (tree treep)
  (cond ((tree-empty-p x)
         (tree-fix y))
        ((tree-empty-p y)
         (tree-fix x))
        ((heap<-with-tree-element (tree->head x) (tree->head y))
         (mv-let (assoc left right)
                 (tree-split (tree-element->key (tree->head y)) x)
           (let ((head
                   (if assoc
                       (tree-element (tree-element->hash (tree->head y))
                                     (tree-element->key (tree->head y))
                                     (generic-combine
                                       (tree-element->key (tree->head y))
                                       (cdr assoc)
                                       (tree-element->val (tree->head y))))
                     (tree->head y))))
             (tree-node head
                        (tree-generic-union left (tree->left y))
                        (tree-generic-union right (tree->right y))))))
        (t
         (mv-let (assoc left right)
                 (tree-split (tree-element->key (tree->head x)) y)
           (let ((head
                   (if assoc
                       (tree-element (tree-element->hash (tree->head x))
                                     (tree-element->key (tree->head x))
                                     (generic-combine
                                       (tree-element->key (tree->head x))
                                       (tree-element->val (tree->head x))
                                       (cdr assoc)))
                     (tree->head x))))
             (tree-node head
                        (tree-generic-union (tree->left x) left)
                        (tree-generic-union (tree->right x) right))))))
  :measure (+ (acl2-count x)
              (acl2-count y))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable tree-element
                                           tree-element-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-generic-union-type-prescription
  (or (consp (tree-generic-union x y))
      (equal (tree-generic-union x y) nil))
  :rule-classes :type-prescription
  :induct t
  :enable tree-generic-union)

(defrule tree-generic-union-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv x0 x1)
           (equal (tree-generic-union x0 y)
                  (tree-generic-union x1 y)))
  :rule-classes :congruence
  :induct t
  :enable tree-generic-union)

(defrule tree-generic-union-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv y0 y1)
           (equal (tree-generic-union x y0)
                  (tree-generic-union x y1)))
  :rule-classes :congruence
  :induct t
  :enable tree-generic-union)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-empty-p-of-tree-generic-union
  (equal (tree-empty-p (tree-generic-union x y))
         (and (tree-empty-p x)
              (tree-empty-p y)))
  :induct t
  :enable tree-generic-union)

(defruled in-of-tree-key-set-of-tree-generic-union
  (implies (and (bstp x)
                (bstp y))
           (equal (treeset::in a (tree-key-set (tree-generic-union x y)))
                  (treeset::in a (treeset::union (tree-key-set x)
                                                 (tree-key-set y)))))
  :induct t
  :enable (tree-generic-union
           data::<<-rules))

(defrule tree-key-set-of-tree-generic-union
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-key-set (tree-generic-union x y))
                  (treeset::union (tree-key-set x)
                                  (tree-key-set y))))
  :enable (treeset::extensionality
           in-of-tree-key-set-of-tree-generic-union))

;;;;;;;;;;;;;;;;;;;;

(defrule <<-all-l-of-tree-generic-union
  (equal (<<-all-l (tree-generic-union x y) z)
         (and (<<-all-l x z)
              (<<-all-l y z)))
  :induct t
  :enable (tree-generic-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

(defrule <<-all-r-of-arg1-tree-generic-union
  (equal (<<-all-r x (tree-generic-union y z))
         (and (<<-all-r x y)
              (<<-all-r x z)))
  :induct t
  :enable (tree-generic-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-tree-generic-union-when-bstp
  (implies (and (bstp x)
                (bstp y))
           (bstp (tree-generic-union x y)))
  :induct t
  :enable tree-generic-union)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-lookup-of-tree-generic-union
  (implies (and (bstp x)
                (bstp y))
           (equal (tree-lookup a (tree-generic-union x y))
                  (if (treeset::in a (tree-key-set x))
                      (if (treeset::in a (tree-key-set y))
                          (generic-combine a
                                           (tree-lookup a x)
                                           (tree-lookup a y))
                        (tree-lookup a x))
                    (tree-lookup a y))))
  :induct t
  :enable (tree-generic-union
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule heap<-all-l-of-tree-generic-union
  (equal (heap<-all-l (tree-generic-union x y) z)
         (and (heap<-all-l x z)
              (heap<-all-l y z)))
  :induct t
  :enable (tree-generic-union
           tree-split-extra-rules
           acl2::equal-of-booleans-cheap))

;;;;;;;;;;;;;;;;;;;;

(defrule heapp-of-tree-generic-union-when-heapp
  (implies (and (heapp x)
                (heapp y))
           (heapp (tree-generic-union x y)))
  :induct t
  :hints ('(:cases ((equal (tree-element->key (tree->head x))
                           (tree-element->key (tree->head y))))))
  :enable (tree-generic-union
           heap<-all-l-extra-rules
           tree-split-extra-rules
           heap<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-genericp-of-tree-generic-union
  (implies (and (tree-all-vals-genericp x)
                (tree-all-vals-genericp y))
           (tree-all-vals-genericp (tree-generic-union x y)))
  :induct t
  :enable (tree-generic-union
           tree-all-vals-genericp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define generic-union
  ((x mapp)
   (y mapp))
  :type-prescription :none
  :returns (map mapp
                :hints (("Goal" :in-theory (enable mapp
                                                   fix
                                                   empty))))
  (tree-generic-union (fix x) (fix y))
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defruled generic-union-type-prescription
  (or (consp (generic-union x y))
      (equal (generic-union x y) nil))
  :rule-classes :type-prescription
  :enable generic-union)

(add-to-ruleset break-abstraction '(generic-union-type-prescription))

(defrule generic-union-when-equiv-of-arg1-congruence
  (implies (equiv x0 x1)
           (equal (generic-union x0 y)
                  (generic-union x1 y)))
  :rule-classes :congruence
  :enable generic-union)

(defrule generic-union-when-equiv-of-arg2-congruence
  (implies (equiv y0 y1)
           (equal (generic-union x y0)
                  (generic-union x y1)))
  :rule-classes :congruence
  :enable generic-union)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-generic-union
  (equal (emptyp (generic-union x y))
         (and (emptyp x)
              (emptyp y)))
  :enable (generic-union
           emptyp
           mapp
           break-abstraction))

(defrule keys-of-generic-union
  (equal (keys (generic-union x y))
         (treeset::union (keys x)
                         (keys y)))
  :enable (generic-union
           keys
           mapp
           break-abstraction))

(defrule lookup-of-generic-union
  (equal (lookup key (generic-union x y) :default default)
         (if (treeset::in key (keys x))
             (if (treeset::in key (keys y))
                 (generic-combine key
                                  (lookup key x)
                                  (lookup key y))
               (lookup key x :default default))
           (lookup key y :default default)))
  :enable (generic-union
           lookup
           keys
           mapp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defruled generic-union-when-emptyp-of-arg1
  (implies (emptyp x)
           (equal (generic-union x y)
                  (fix y)))
  :enable (generic-union
           tree-generic-union
           emptyp
           break-abstraction))

(defrule generic-union-when-emptyp-of-arg1-cheap
  (implies (emptyp x)
           (equal (generic-union x y)
                  (fix y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by generic-union-when-emptyp-of-arg1)

(defrule generic-union-of-empty
  (equal (generic-union (empty) y)
         (fix y))
  :enable generic-union-when-emptyp-of-arg1)

(defruled generic-union-when-emptyp-of-arg2
  (implies (emptyp y)
           (equal (generic-union x y)
                  (fix x)))
  :enable (generic-union
           tree-generic-union
           emptyp
           tree-empty-p-when-treep
           break-abstraction))

(defrule generic-union-when-emptyp-of-arg2-cheap
  (implies (emptyp y)
           (equal (generic-union x y)
                  (fix x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by generic-union-when-emptyp-of-arg2)

(defrule generic-union-of-arg1-and-empty
  (equal (generic-union x (empty))
         (fix x))
  :enable generic-union-when-emptyp-of-arg2)

;;;;;;;;;;;;;;;;;;;;

;; The value check over a map's own tree is the check over its value set.
(defruledl set-all-genericp-of-tree-val-set-becomes-tree-all-vals-genericp
  (equal (treeset::set-all-genericp (tree-val-set tree))
         (tree-all-vals-genericp tree))
  :enable tree-all-vals-genericp-becomes-set-all-genericp-of-tree-val-set)

(defrule set-all-genericp-of-values-of-generic-union
  (implies (and (treeset::set-all-genericp (values x))
                (treeset::set-all-genericp (values y)))
           (treeset::set-all-genericp (values (generic-union x y))))
  :enable (generic-union
           values
           mapp
           break-abstraction
           set-all-genericp-of-tree-val-set-becomes-tree-all-vals-genericp))
