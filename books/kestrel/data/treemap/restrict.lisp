; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/to-oset-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)
(include-book "kestrel/data/treeset/intersect-defs" :dir :system)

(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/restrict-defs")
(include-book "map-defs")
(include-book "to-omap-defs")
(include-book "submap-defs")
(include-book "update-defs")
(include-book "delete-defs")
(include-book "update-star-defs")
;; TODO
;; (include-book "generic-typed-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

;; (local (include-book "std/osets/top" :dir :system))
(local (include-book "kestrel/data/utilities/omap" :dir :system))

(local (include-book "kestrel/data/treeset/internal/in" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/to-oset" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))

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
;; TODO
;; (local (include-book "generic-typed"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc restrict
  :parents (treeset)
  :short "A restriction of a @(see treemap) to a key set."
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
           stronger guard. The guard asserts that the key set and the map keys
           consist of elements suitable for comparison with the specified
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
  ((keys treeset::setp)
   (map mapp))
  :returns (map$ mapp
                 :hints (("Goal" :in-theory (enable* mapp
                                                     treeset::break-abstraction
                                                     break-abstraction))))
  (tree-restrict (treeset::fix keys) (fix map))
  :guard-hints (("Goal" :in-theory (enable* treeset::break-abstraction
                                            break-abstraction)))

  ///
  (add-macro-fn restrict restrict$inline t))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t restrict)))

(defruled restrict-type-prescription
  (or (consp (restrict keys map))
      (equal (restrict keys map) nil))
  :rule-classes :type-prescription
  :enable restrict)

(add-to-ruleset break-abstraction '(restrict-type-prescription))

(defrule restrict-when-set-equiv-of-arg1-congruence
  (implies (treeset::equiv keys0 keys1)
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
  (implies (treeset::emptyp keys)
           (emptyp (restrict keys map)))
  :enable (treeset::emptyp
           restrict))

(defrule emptyp-of-restrict-when-emptyp-of-arg2
  (implies (emptyp map)
           (emptyp (restrict keys map)))
  :enable (emptyp
           restrict))

(defruled restrict-when-emptyp-of-arg1
  (implies (treeset::emptyp keys)
           (equal (restrict keys map)
                  (empty)))
  :enable (treeset::emptyp
           restrict
           empty))

(defrule restrict-when-emptyp-of-arg1-cheap
  (implies (treeset::emptyp keys)
           (equal (restrict keys map)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-when-emptyp-of-arg1)

(defrule restrict-of-empty
  (equal (restrict (treeset::empty) map)
         (empty))
  :enable restrict-when-emptyp-of-arg1)

(defruled restrict-when-emptyp-of-arg2
  (implies (emptyp map)
           (equal (restrict keys map)
                  (empty)))
  :enable (treeset::emptyp
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
         (treeset::intersect keys (keys map)))
  :enable treeset::extensionality
  :prep-lemmas
  ((defrule in-of-keys-of-restrict
     (equal (treeset::in key (keys (restrict keys map)))
            (and (treeset::in key keys)
                 (treeset::in key (keys map))))
     ;; TODO: improve proof
     :use (:instance in-of-tree-key-set-of-tree-restrict
                     (a key)
                     (tree map))
     :enable (restrict
              keys
              treeset::in
              treeset::fix
              fix
              treeset::setp
              mapp
              treeset::empty
              empty)
     :disable in-of-tree-key-set-of-tree-restrict)))

(defrule lookup-of-restrict
  (equal (lookup key (restrict keys map) :default default)
         (if (treeset::in key keys)
             (lookup key map :default default)
           default))
  :enable (restrict
           lookup
           treeset::in
           mapp
           keys
           treeset::break-abstraction
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-restrict
  (submap (restrict keys map) map)
  :enable pick-a-point)

;; TODO
;; (defrule submap-of-arg1-and-restrict
;;   (equal (submap map (restrict keys map))
;;          (treeset::subset (keys map) keys))
;;   :enable (acl2::equal-of-booleans-cheap
;;            pick-a-point-polar
;;            treeset::pick-a-point-polar))

(defrule monotonicity-of-restrict
  (implies (and (treeset::subset keys0 keys1)
                (submap map0 map1))
           (submap (restrict keys0 map0)
                   (restrict keys1 map1)))
  :enable pick-a-point-polar)

;;;;;;;;;;;;;;;;;;;;

(defrule restrict-of-restrict
  (equal (restrict x (restrict y map))
         (restrict (treeset::intersect x y) map))
  :enable extensionality)

(defrule restrict-when-superset-of-keys
  (implies (treeset::subset (keys map) keys)
           (equal (restrict keys map)
                  (fix map)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;

(defruled restrict-of-update
  (equal (restrict keys (update key val map))
         (if (treeset::in key keys)
             (update key val (restrict keys map))
           (restrict keys map)))
  :enable extensionality)

(defruled restrict-of-update-when-in
  (implies (treeset::in key keys)
           (equal (restrict keys (update key val map))
                  (update key val (restrict keys map))))
  :by restrict-of-update)

(defrule restrict-of-update-when-in-cheap
  (implies (treeset::in key keys)
           (equal (restrict keys (update key val map))
                  (update key val (restrict keys map))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-of-update-when-in)

(defruled restrict-of-update-when-not-in
  (implies (not (treeset::in key keys))
           (equal (restrict keys (update key val map))
                  (restrict keys map)))
  :by restrict-of-update)

(defrule restrict-of-update-when-not-in-cheap
  (implies (not (treeset::in key keys))
           (equal (restrict keys (update key val map))
                  (restrict keys map)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by restrict-of-update-when-not-in)

(defrule restrict-of-delete
  (equal (restrict (treeset::delete key keys) map)
         (delete key (restrict keys map)))
  :enable extensionality)

(defrule restrict-of-arg1-and-delete
  (equal (restrict keys (delete key map))
         (delete key (restrict keys map)))
  :enable extensionality)

;; TODO: is there any sensible rule for (update* (restrict keys x) y)?
(defruled update*-of-arg1-and-restrict
  (equal (update* x (restrict keys y))
         (restrict (treeset::union (keys x) keys) (update* x y)))
  :enable extensionality)

;; TODO GJ: Resume

;; (defrule restrict-over-union
;;   (equal (restrict (union x y) z)
;;          (union (restrict x z) (restrict y z)))
;;   :enable extensionality)

;; NOTE: this goes the opposite direction then the corresponding operations on
;; sets (update* -> union, restrict -> intersect).
(defrule update*-of-restrict-restrict-1
  (equal (update* (restrict x map) (restrict y map))
         (restrict (treeset::union x y) map))
  :enable extensionality)

(defrule update*-of-restrict-restrict-2
  (equal (update* (restrict keys x) (restrict keys y))
         (restrict keys (update* x y)))
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;
#| ;; TODO
(defrule set-all-genericp-of-restrict-when-set-all-genericp-of-arg1
  (implies (set-all-genericp x)
           (set-all-genericp (restrict x y)))
  :enable set-all-genericp-pick-a-point-polar)

(defrule set-all-genericp-of-restrict-when-set-all-genericp-of-arg2
  (implies (set-all-genericp y)
           (set-all-genericp (restrict x y)))
  :enable set-all-genericp-pick-a-point-polar)

(defrule set-all-acl2-numberp-of-restrict-when-set-all-acl2-numberp-of-arg1
  (implies (set-all-acl2-numberp x)
           (set-all-acl2-numberp (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg1
         (genericp acl2-numberp)
         (set-all-genericp set-all-acl2-numberp))
  :enable set-all-acl2-numberp-alt-definition)

(defrule set-all-acl2-numberp-of-restrict-when-set-all-acl2-numberp-of-arg2
  (implies (set-all-acl2-numberp y)
           (set-all-acl2-numberp (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg2
         (genericp acl2-numberp)
         (set-all-genericp set-all-acl2-numberp)))

(defrule set-all-symbolp-of-restrict-when-set-all-symbolp-of-arg1
  (implies (set-all-symbolp x)
           (set-all-symbolp (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg1
         (genericp symbolp)
         (set-all-genericp set-all-symbolp))
  :enable set-all-symbolp-alt-definition)

(defrule set-all-symbolp-of-restrict-when-set-all-symbolp-of-arg2
  (implies (set-all-symbolp y)
           (set-all-symbolp (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg2
         (genericp symbolp)
         (set-all-genericp set-all-symbolp)))

(defrule set-all-eqlablep-of-restrict-when-set-all-eqlablep-of-arg1
  (implies (set-all-eqlablep x)
           (set-all-eqlablep (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg1
         (genericp eqlablep)
         (set-all-genericp set-all-eqlablep))
  :enable set-all-eqlablep-alt-definition)

(defrule set-all-eqlablep-of-restrict-when-set-all-eqlablep-of-arg2
  (implies (set-all-eqlablep y)
           (set-all-eqlablep (restrict x y)))
  :use (:functional-instance
         set-all-genericp-of-restrict-when-set-all-genericp-of-arg2
         (genericp eqlablep)
         (set-all-genericp set-all-eqlablep)))
|#
;;;;;;;;;;;;;;;;;;;;

(defrule to-omap-of-restrict
  (equal (to-omap (restrict keys map))
         (omap::restrict (treeset::to-oset keys)
                         (to-omap map)))
  :enable (to-omap
           treeset::to-oset
           restrict
           mapp
           treeset::break-abstraction
           break-abstraction))

(add-to-ruleset to-omap-theory '(to-omap-of-restrict))

(defrule from-omap-of-restrict
  (equal (from-omap (omap::restrict keys map))
         (restrict (treeset::from-oset keys)
                   (from-omap map)))
  :enable (extensionality
           omap::assoc-of-restrict))

(add-to-ruleset from-omap-theory '(from-omap-of-restrict))

(defruled restrict-becomes-omap-restrict
  (equal (restrict keys map)
         (from-omap (omap::restrict (treeset::to-oset keys)
                                    (to-omap map)))))

(add-to-ruleset to-omap-theory '(restrict-becomes-omap-restrict))

(defruled omap-restrict-becomes-restrict
  (equal (omap::restrict keys map)
         (to-omap (restrict (treeset::from-oset keys)
                            (from-omap map)))))

(add-to-ruleset from-omap-theory '(omap-restrict-becomes-restrict))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-=
  ((keys treeset::acl2-number-setp)
   (map acl2-number-mapp))
  (mbe :logic (restrict keys map)
       :exec (acl2-number-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            treeset::set-all-acl2-numberp
                                            map-keys-acl2-numberp
                                            treeset::break-abstraction
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-eq
  ((keys treeset::symbol-setp)
   (map symbol-mapp))
  (mbe :logic (restrict keys map)
       :exec (symbol-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            treeset::set-all-symbolp
                                            map-keys-symbolp
                                            treeset::break-abstraction
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-eql
  ((keys treeset::eqlable-setp)
   (map eqlable-mapp))
  (mbe :logic (restrict keys map)
       :exec (eqlable-tree-restrict keys map))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* restrict
                                            treeset::set-all-eqlablep
                                            map-keys-eqlablep
                                            treeset::break-abstraction
                                            break-abstraction))))
