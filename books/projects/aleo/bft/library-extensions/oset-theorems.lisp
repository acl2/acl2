; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection oset-theorems
  :parents (library-extensions)
  :short "Some theorems about osets."
  :long
  (xdoc::topstring
   (xdoc::p
    "Among other theorems,
     we introduce an alternative pick-a-point reasoning support
     for @(tsee set::subset).
     Unlike @(see set::pick-a-point-subset-strategy),
     this uses a @(tsee defun-sk) and a ruleset."))

  (defruled set::not-emptyp-when-in-of-subset
    (implies (and (set::in a x)
                  (set::subset x y))
             (not (set::emptyp y))))

  (defrule set::subset-of-union-when-both-subset
    (implies (and (set::subset a s)
                  (set::subset b s))
             (set::subset (set::union a b) s))
    :enable set::expensive-rules)

  (defrule set::cardinality-of-union-upper-bound-when-both-subset
    (implies (and (set::subset a s)
                  (set::subset b s))
             (<= (set::cardinality (set::union a b))
                 (set::cardinality s)))
    :rule-classes (:rewrite :linear)
    :enable (set::cardinality)
    :disable set::expand-cardinality-of-union)

  (defruled set::intersect-of-insert-left
    (equal (set::intersect (set::insert a x) y)
           (if (set::in a y)
               (set::insert a (set::intersect x y))
             (set::intersect x y)))
    :enable (set::double-containment
             set::pick-a-point-subset-strategy))

  (defruled set::intersect-of-insert-right
    (equal (set::intersect x (set::insert a y))
           (if (set::in a x)
               (set::insert a (set::intersect x y))
             (set::intersect x y)))
    :enable (set::double-containment
             set::pick-a-point-subset-strategy))

  (defrule set::same-element-when-cardinality-leq-1
    (implies (and (<= (set::cardinality set) 1)
                  (set::in elem1 set)
                  (set::in elem2 set))
             (equal elem1 elem2))
    :rule-classes nil
    :induct t
    :enable (set::cardinality
             set::in))

  (defrule set::cardinality-of-tail-leq
    (<= (set::cardinality (set::tail set))
        (set::cardinality set))
    :rule-classes :linear
    :use (:instance set::subset-cardinality (x (set::tail set)) (y set))
    :disable set::subset-cardinality)

  (defruled set::head-of-intersect-member-when-not-emptyp
    (implies (not (set::emptyp (set::intersect x y)))
             (and (set::in (set::head (set::intersect x y)) x)
                  (set::in (set::head (set::intersect x y)) y)))
    :use (:instance set::in-head (x (set::intersect x y))))

  (defruled set::emptyp-when-proper-subset-of-singleton
    (implies (and (set::subset x (set::insert a nil))
                  (not (equal x (set::insert a nil))))
             (set::emptyp x))
    :induct t
    :enable (set::subset
             set::expensive-rules))

  (defrule set::same-element-when-in-subset-of-singleton
    (implies (and (set::subset set (set::insert elem nil))
                  (set::in elem1 set))
             (equal elem elem1))
    :rule-classes nil
    :enable set::expensive-rules)

  (defruled set::intersect-mono-subset
    (implies (set::subset a b)
             (set::subset (set::intersect a c)
                          (set::intersect b c)))
    :enable set::expensive-rules)

  (defruled set::emptyp-to-subset-of-nil
    (equal (set::emptyp a)
           (set::subset a nil)))

  (defruled set::not-member-when-member-of-disjoint
    (implies (and (not (set::intersect a b))
                  (set::in x a))
             (not (set::in x b)))
    :induct t
    :enable set::intersect)

  (defruled set::emptyp-of-intersect-of-subset-left
    (implies (and (set::subset a b)
                  (set::emptyp (set::intersect b c)))
             (set::emptyp (set::intersect a c)))
    :enable (set::emptyp-to-subset-of-nil
             set::intersect-mono-subset
             set::expensive-rules)
    :disable set::emptyp-subset-2)

  (defruled set::subset-of-intersect-if-subset-of-both
    (implies (and (set::subset a b)
                  (set::subset a c))
             (set::subset a (set::intersect b c)))
    :enable set::expensive-rules)

  (defruled set::subset-of-tail-and-delete-when-subset
    (implies (and (not (set::emptyp x))
                  (set::subset x y))
             (set::subset (set::tail x)
                          (set::delete (set::head x) y)))
    :enable set::expensive-rules)

  (defruled set::subset-of-difference-when-disjoint
    (implies (and (set::subset x y)
                  (set::emptyp (set::intersect x z)))
             (set::subset x (set::difference y z)))
    :enable (set::expensive-rules
             set::not-member-when-member-of-disjoint
             set::emptyp))

  (defruled set::not-emptyp-of-intersect-when-in-both
    (implies (and (set::in a x)
                  (set::in a y))
             (not (set::emptyp (set::intersect x y))))
    :use (:instance set::never-in-empty (a a) (x (set::intersect x y)))
    :disable set::never-in-empty)

  (defruled set::intersect-ab-subset-difference-bc-when-disjoint-ac
    (implies (set::emptyp (set::intersect a c))
             (set::subset (set::intersect a b)
                          (set::difference b c)))
    :enable (set::expensive-rules
             set::emptyp
             set::not-member-when-member-of-disjoint))

  ;; pick-a-point:
  (define-sk set::subset-sk ((set1 set::setp) (set2 set::setp))
    (forall (elem)
            (implies (set::in elem set1)
                     (set::in elem set2)))
    :skolem-name set::subset-witness

    ///

    (in-theory (disable set::subset-sk set::subset-sk-necc))

    (defruled set::subset-sk-of-tail-when-subset-sk
      (implies (set::subset-sk set1 set2)
               (set::subset-sk (set::tail set1) set2))
      :expand (set::subset-sk (set::tail set1) set2)
      :use (:instance set::subset-sk-necc
                      (elem (set::subset-witness (set::tail set1) set2))))

    (defruled set::subset-sk-when-subset
      (implies (set::subset set1 set2)
               (set::subset-sk set1 set2))
      :enable (set::subset-sk
               set::expensive-rules))

    (defruled set::subset-when-subset-sk
      (implies (set::subset-sk set1 set2)
               (set::subset set1 set2))
      :induct t
      :enable (set::subset
               set::subset-sk-of-tail-when-subset-sk)
      :hints ('(:use (:instance set::subset-sk-necc
                                (elem (set::head set1))))))

    (defruled set::subset-to-subset-sk
      (equal (set::subset set1 set2)
             (set::subset-sk set1 set2))
      :use (set::subset-sk-when-subset
            set::subset-when-subset-sk))

    ;; Enable this ruleset to perform pick-a-point reasoning on SET::SUBSET.
    ;; The arbitrary element will be (SET::SUBSET-WITNESS <set1> <set2>),
    ;; where <set1> and <set2> are the omaps for which
    ;; we want to prove that (SET::SUBSET <set1> <set2>) holds.
    (acl2::def-ruleset set::subset-pick-a-point
      '(set::subset-to-subset-sk
        set::subset-sk))))
