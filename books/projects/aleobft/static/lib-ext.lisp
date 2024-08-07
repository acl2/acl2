; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "kestrel/utilities/omaps/core" :dir :system)
(include-book "std/osets/top" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::not-emptyp-when-in-of-subset
  (implies (and (set::in a x)
                (set::subset x y))
           (not (set::emptyp y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::expand-cardinality-of-intersect
  (equal (set::cardinality (set::intersect x y))
         (+ (set::cardinality x)
            (set::cardinality y)
            (- (set::cardinality (set::union x y))))))

(theory-invariant
 (incompatible (:rewrite set::expand-cardinality-of-union)
               (:rewrite set::expand-cardinality-of-intersect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::subset-of-union-when-both-subset
  (implies (and (set::subset a s)
                (set::subset b s))
           (set::subset (set::union a b) s))
  :enable set::expensive-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::cardinality-of-union-upper-bound-when-both-subset
  (implies (and (set::subset a s)
                (set::subset b s))
           (<= (set::cardinality (set::union a b))
               (set::cardinality s)))
  :rule-classes (:rewrite :linear)
  :enable (set::cardinality)
  :disable set::expand-cardinality-of-union)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::intersect-of-nil-left
  (equal (set::intersect nil set)
         nil)
  :enable set::intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::intersect-of-nil-right
  (equal (set::intersect set nil)
         nil)
  :induct t
  :enable set::intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::intersect-of-insert-left
  (equal (set::intersect (set::insert a x) y)
         (if (set::in a y)
             (set::insert a (set::intersect x y))
           (set::intersect x y)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;

(defruled set::intersect-of-insert-right
  (equal (set::intersect x (set::insert a y))
         (if (set::in a x)
             (set::insert a (set::intersect x y))
           (set::intersect x y)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::same-element-when-cardinality-leq-1
  (implies (and (<= (set::cardinality set) 1)
                (set::in elem1 set)
                (set::in elem2 set))
           (equal elem1 elem2))
  :rule-classes nil
  :induct t
  :enable (set::cardinality
           set::in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule set::cardinality-of-tail-leq
  (<= (set::cardinality (set::tail set))
      (set::cardinality set))
  :rule-classes :linear
  :use (:instance set::subset-cardinality (x (set::tail set)) (y set))
  :disable set::subset-cardinality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::head-of-intersection-member-when-not-emptyp
  (implies (not (set::emptyp (set::intersect x y)))
           (and (set::in (set::head (set::intersect x y)) x)
                (set::in (set::head (set::intersect x y)) y)))
  :use (:instance set::in-head (x (set::intersect x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::emptyp-when-proper-subset-of-singleton
  (implies (and (set::subset x (set::insert a nil))
                (not (equal x (set::insert a nil))))
           (set::emptyp x))
  :induct t
  :enable (set::subset
           set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omap::head-key-not-in-keys-of-tail
  (not (set::in (mv-nth 0 (omap::head map))
                (omap::keys (omap::tail map))))
  :enable omap::in-of-keys-to-assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omap::size-to-cardinality-of-keys
  (equal (omap::size map)
         (set::cardinality (omap::keys map)))
  :induct t
  :enable (omap::size
           omap::keys
           set::expensive-rules))

(defruled omap::cardinality-of-keys-to-size
  (equal (set::cardinality (omap::keys map))
         (omap::size map))
  :enable omap::size-to-cardinality-of-keys)

(theory-invariant (incompatible (:rewrite omap::size-to-cardinality-of-keys)
                                (:rewrite omap::cardinality-of-keys-to-size)))
