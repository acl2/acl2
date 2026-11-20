; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/to-oset-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/union-defs" :dir :system)
(include-book "kestrel/data/tset/intersect-defs" :dir :system)

(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/restrict-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "submap-defs")
(include-book "update-defs")
(include-book "delete-defs")
(include-book "update-star-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/omap" :dir :system))

(local (include-book "kestrel/data/tset/internal/in" :dir :system))
(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/to-oset" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/restrict"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "to-omap"))
(local (include-book "keys"))
(local (include-book "lookup"))
(local (include-book "submap"))
(local (include-book "extensionality"))
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "update-star"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc restrict
  :parents (tmap)
  :short "A restriction of a @(see tmap) to a key set."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$) (where @($m < n$)).")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(restrict keys map :test test)")
      (xdoc::desc
        "@(':test') &mdash; optional"
        (xdoc::p
          "One of: @('equal'), @('='), @('eq'), or @('eql'). If no value is
           provided, the default is @('equal'). Specifying an alternative test
           allows for a more performant implementation, at the cost of a
           stronger guard. The guard asserts that both the key set and the map
           keys consist of elements suitable for comparison with the specified
           equality variant.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro restrict (keys map &key (test 'equal))
  (declare (xargs :guard (member-eq test '(equal = eq eql))))
  (case test
    (equal `(restrict$inline ,keys ,map))
    (=     `(restrict-=      ,keys ,map))
    (eq    `(restrict-eq     ,keys ,map))
    (eql   `(restrict-eql    ,keys ,map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict$inline
  ((keys tset::setp)
   (map mapp))
  :returns (map$ mapp
                 :hints (("Goal" :in-theory (enable* mapp
                                                     tset::break-abstraction
                                                     break-abstraction))))
  (tree-restrict (tset::fix keys) (fix map))
  :guard-hints (("Goal" :in-theory (enable* tset::break-abstraction
                                            break-abstraction)))

  ///
  (add-macro-fn restrict restrict$inline t))

;;;;;;;;;;;;;;;;;;;;

(defruled restrict-type-prescription
  (or (consp (restrict keys map))
      (equal (restrict keys map) nil))
  :rule-classes :type-prescription
  :enable restrict)

(add-to-ruleset break-abstraction '(restrict-type-prescription))

(defrule restrict-when-set-equiv-of-arg1-congruence
  (implies (tset::equiv keys0 keys1)
           (equal (restrict keys0 map)
                  (restrict keys1 map)))
  :rule-classes :congruence
  :enable restrict)

(defrule restrict-when-set-equiv-of-arg2-congruence
  (implies (equiv map0 map1)
           (equal (restrict keys map0)
                  (restrict keys map1)))
  :rule-classes :congruence
  :enable restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-of-restrict-when-emptyp-of-arg1
  (implies (tset::emptyp keys)
           (emptyp (restrict keys map)))
  :enable (tset::emptyp
           restrict))

(defrule emptyp-of-restrict-when-emptyp-of-arg2
  (implies (emptyp map)
           (emptyp (restrict keys map)))
  :enable (emptyp
           restrict))

(defruled restrict-when-emptyp-of-arg1
  (implies (tset::emptyp keys)
           (equal (restrict keys map)
                  (empty)))
  :enable (tset::emptyp
           restrict
           empty))

(defrule restrict-when-emptyp-of-arg1-cheap
  (implies (tset::emptyp keys)
           (equal (restrict keys map)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-when-emptyp-of-arg1)

(defrule restrict-of-empty
  (equal (restrict (tset::empty) map)
         (empty))
  :enable restrict-when-emptyp-of-arg1)

(defruled restrict-when-emptyp-of-arg2
  (implies (emptyp map)
           (equal (restrict keys map)
                  (empty)))
  :enable (tset::emptyp
           restrict
           empty))

(defrule restrict-when-emptyp-of-arg2-cheap
  (implies (emptyp map)
           (equal (restrict keys map)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-when-emptyp-of-arg2)

(defrule restrict-of-arg1-and-empty
  (equal (restrict keys (empty))
         (empty))
  :enable restrict-when-emptyp-of-arg2)

;;;;;;;;;;;;;;;;;;;;

(defrule keys-of-restrict
  (equal (keys (restrict keys map))
         (tset::intersect keys (keys map)))
  :enable tset::extensionality
  :prep-lemmas
  ((defrule in-of-keys-of-restrict
     (equal (tset::in key (keys (restrict keys map)))
            (and (tset::in key keys)
                 (tset::in key (keys map))))
     ;; TODO: improve proof
     :use (:instance in-of-tree-key-set-of-tree-restrict
                     (a key)
                     (tree map))
     :enable (restrict
              keys
              tset::in
              tset::fix
              fix
              tset::setp
              mapp
              tset::empty
              empty)
     :disable in-of-tree-key-set-of-tree-restrict)))

(defrule lookup-of-restrict
  (equal (lookup key (restrict keys map) :default default)
         (if (tset::in key keys)
             (lookup key map :default default)
           default))
  :enable (restrict
           lookup
           tset::in
           mapp
           keys
           tset::break-abstraction
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-restrict
  (submap (restrict keys map) map)
  :enable pick-a-point)

(defrule submap-of-arg1-and-restrict
  (equal (submap x (restrict keys map))
         (and (submap x map)
              (tset::subset (keys x) keys)))
  :enable (acl2::equal-of-booleans-cheap
           pick-a-point-polar)
  :prep-lemmas
  ((defrule lemma
     (implies (submap x (restrict keys map))
              (tset::subset (keys x) keys))
     ;; TODO: why isn't this inferred by forward-chaining?
     :use (:instance subset-of-keys
                     (y (restrict keys map)))
     :enable tset::pick-a-point-polar
     :disable subset-of-keys)
   (defrule lemma2
     (implies (submap x (restrict keys map))
              (submap x map)))))

(defrule monotonicity-of-restrict
  (implies (and (tset::subset keys0 keys1)
                (submap map0 map1))
           (submap (restrict keys0 map0)
                   (restrict keys1 map1)))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule restrict-of-restrict
  (equal (restrict x (restrict y map))
         (restrict (tset::intersect x y) map))
  :enable extensionality)

(defrule restrict-when-superset-of-keys
  (implies (tset::subset (keys map) keys)
           (equal (restrict keys map)
                  (fix map)))
  :enable extensionality)

(defrule equal-of-restrict-of-keys
  (implies (and (equiv x$$ (double-rewrite x$))
                (equal x$$ x))
           (equal (equal (restrict (keys x) y) x$)
                  (and (mapp x$)
                       (submap x y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :enable extensionality)

(defruled submap-becomes-equal-of-restrict
  (equal (submap x y)
         (equal (restrict (keys x) y) (fix x))))

(theory-invariant (incompatible! (:rewrite submap-becomes-equal-of-restrict)
                                 (:rewrite equal-of-restrict-of-keys)))

;;;;;;;;;;;;;;;;;;;;

(defruled restrict-of-update
  (equal (restrict keys (update key val map))
         (if (tset::in key keys)
             (update key val (restrict keys map))
           (restrict keys map)))
  :enable extensionality)

(defruled restrict-of-update-when-in
  (implies (tset::in key keys)
           (equal (restrict keys (update key val map))
                  (update key val (restrict keys map))))
  :by restrict-of-update)

(defrule restrict-of-update-when-in-cheap
  (implies (tset::in key keys)
           (equal (restrict keys (update key val map))
                  (update key val (restrict keys map))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-of-update-when-in)

(defruled restrict-of-update-when-not-in
  (implies (not (tset::in key keys))
           (equal (restrict keys (update key val map))
                  (restrict keys map)))
  :by restrict-of-update)

(defrule restrict-of-update-when-not-in-cheap
  (implies (not (tset::in key keys))
           (equal (restrict keys (update key val map))
                  (restrict keys map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-of-update-when-not-in)

(defrule restrict-of-delete
  (equal (restrict (tset::delete key keys) map)
         (delete key (restrict keys map)))
  :enable extensionality)

(defrule restrict-of-arg1-and-delete
  (equal (restrict keys (delete key map))
         (delete key (restrict keys map)))
  :enable extensionality)

;; TODO: is there any sensible rule for (update* (restrict keys x) y)?
(defruled update*-of-arg1-and-restrict
  (equal (update* x (restrict keys y))
         (restrict (tset::union (keys x) keys) (update* x y)))
  :enable extensionality)

;; NOTE: this goes the opposite direction then the corresponding operations on
;; sets (update* -> union, restrict -> intersect).
(defrule update*-of-restrict-restrict-1
  (equal (update* (restrict x map) (restrict y map))
         (restrict (tset::union x y) map))
  :enable extensionality)

(defrule update*-of-restrict-restrict-2
  (equal (update* (restrict keys x) (restrict keys y))
         (restrict keys (update* x y)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled lookup-when-equal-of-restrict
  (implies (and (equal (restrict keys x) (restrict keys y))
                (tset::in key keys))
           (equal (lookup key x :default default)
                  (lookup key y :default default)))
  :use ((:instance lookup-of-restrict
                   (map x))
        (:instance lookup-of-restrict
                   (map y)))
  :disable lookup-of-restrict)

(defrule lookup-when-equal-of-restrict-forward-chaining
  (implies (and (equal (restrict keys x) (restrict keys y))
                (tset::in key keys))
           (equal (lookup key x :default default)
                  (lookup key y :default default)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((lookup key x :default default))))
  :by lookup-when-equal-of-restrict)

(defrule lookup-default-nil-when-equal-of-restrict-forward-chaining
  (implies (and (equal (restrict keys x) (restrict keys y))
                (tset::in key keys))
           (equal (lookup key x)
                  (lookup key y)))
  :rule-classes :forward-chaining
  :by lookup-when-equal-of-restrict)

;;;;;;;;;;;;;;;;;;;;

(defrule to-omap-of-restrict
  (equal (to-omap (restrict keys map))
         (omap::restrict (tset::to-oset keys)
                         (to-omap map)))
  :enable (to-omap
           tset::to-oset
           restrict
           mapp
           tset::break-abstraction
           break-abstraction))

(add-to-ruleset to-omap-theory '(to-omap-of-restrict))

(defrule from-omap-of-restrict
  (equal (from-omap (omap::restrict keys map))
         (restrict (tset::from-oset keys)
                   (from-omap map)))
  :enable (extensionality
           omap::assoc-of-restrict))

(add-to-ruleset from-omap-theory '(from-omap-of-restrict))

(defruled restrict-becomes-omap-restrict
  (equal (restrict keys map)
         (from-omap (omap::restrict (tset::to-oset keys)
                                    (to-omap map)))))

(add-to-ruleset to-omap-theory '(restrict-becomes-omap-restrict))

(defruled omap-restrict-becomes-restrict
  (equal (omap::restrict keys map)
         (to-omap (restrict (tset::from-oset keys)
                            (from-omap map)))))

(add-to-ruleset from-omap-theory '(omap-restrict-becomes-restrict))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule commutativity-of-update*-when-compatiblep
  (implies (equal (restrict (tset::intersect (keys x) (keys y)) x)
                  (restrict (tset::intersect (keys x) (keys y)) y))
           (equal (update* y x)
                  (update* x y)))
  :use ((:instance lookup-when-equal-of-restrict
                   (keys (tset::intersect (keys x) (keys y)))
                   (key (mv-nth 0 (ext-equal-witness (update* y x)
                                                     (update* x y))))
                   (default nil)))
  :enable extensionality-polar)

(defrule commutativity-2-of-update*-when-compatiblep
  (implies (equal (restrict (tset::intersect (keys x) (keys y)) x)
                  (restrict (tset::intersect (keys x) (keys y)) y))
           (equal (update* y x z)
                  (update* x y z)))
  :use ((:instance lookup-when-equal-of-restrict
                   (keys (tset::intersect (keys x) (keys y)))
                   (key (mv-nth 0 (ext-equal-witness (update* y x z)
                                                     (update* x y z))))
                   (default nil)))
  :enable extensionality-polar)

(defrule submap-of-arg1-and-update*-of-arg2-when-compatiblep
  (implies (equal (restrict (tset::intersect (keys x) (keys y)) x)
                  (restrict (tset::intersect (keys x) (keys y)) y))
           (submap x (update* y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-=
  ((keys tset::acl2-number-setp)
   (map acl2-number-mapp))
  (mbe :logic (restrict keys map)
       :exec (acl2-number-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            tset::set-all-acl2-numberp
                                            keys
                                            tset::break-abstraction
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-eq
  ((keys tset::symbol-setp)
   (map symbol-mapp))
  (mbe :logic (restrict keys map)
       :exec (symbol-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            tset::set-all-symbolp
                                            keys
                                            tset::break-abstraction
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-eql
  ((keys tset::eqlable-setp)
   (map eqlable-mapp))
  (mbe :logic (restrict keys map)
       :exec (eqlable-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            tset::set-all-eqlablep
                                            keys
                                            tset::break-abstraction
                                            break-abstraction))))
